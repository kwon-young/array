:- module(array, []).

:- use_module(library(clpfd)).

view:_.from_shape(Shape) := View :-
   shape_strides(Shape, Strides),
   shape_mask(Shape, Mask),
   View = view{shape: Shape, strides: Strides, mask: Mask, offset: 0}.

view:M.reshape(_Shape) := M :-
   true.

M.default() := Dict :-
   Dict = M.default([]).
M.default(Options) := Dict :-
   dict_options(M, MOptions),
   merge_options(Options, MOptions, Merged),
   option(dtype(DType), Merged, float),
   option(device(Device), Merged, prolog),
   Dict = array{views: [], dtype:DType, device:Device, data: _}.

M.push(buffer(Size)) := Dict =>
   Dict = M.push_view(view{}.from_shape([Size])).push_op(buffer(Size)).
M.push_op(Op) := Dict :-
   Dict = M.put([id: _Id, op: Op]).
M.push_view(View) := Dict :-
   Dict = M.put([views: [View | M.views]]).

M.empty(Shape) := Dict :-
   Dict = M.empty(Shape, []).
M.empty(Shape, Options) := Dict :-
   shape_size(Shape, Size),
   Dict = M.default(Options).push(buffer(Size)).reshape(Shape).

product(L, Rel, Product) :-
   foldl([A, B, A*B]>>(true), L, 1, Expr),
   call(Rel, Expr, Product).

shape_size(Shape, Size) :-
   % msort is used to improve product constraint propagation.
   % by putting vars first and grounded term last.
   msort(Shape, SortedShape),
   product(SortedShape, #=, Size).

shape_mask(Shape, Mask) :-
   same_length(Shape, Mask),
   maplist([Dim, 0-Dim1]>>(Dim1 is Dim - 1), Shape, Mask).

shape_strides([_ | Shape], [HeadStride | Strides]) :-
   foldl([Dim, Stride, ParentStride, Stride]>>(ParentStride #= Dim*Stride),
         Shape, Strides, HeadStride, 1).

:- begin_tests(strides).

test('strides_1') :-
   shape_strides([_], [1]).
test('strides_2') :-
   shape_strides([2, 3], [3, 1]).
test('strides_3') :-
   shape_strides([2, 3, 4], [12, 4, 1]).

:- end_tests(strides).

:- begin_tests(view).

test('from_shape') :-
   view{}.from_shape([5]) = view{shape: [5], strides: [1], mask: [0-4], offset: 0},
   view{}.from_shape([2, 3]) = view{shape: [2, 3], strides: [3, 1], mask: [0-1, 0-2], offset: 0},
   view{}.from_shape([2, 3, 4]) = view{shape: [2, 3, 4], strides: [12, 4, 1], mask: [0-1, 0-2, 0-3], offset: 0}.

:- end_tests(view).

:- begin_tests(reshape).

% reformat the test cases below into correct plunit test cases
% in our case, contiguous is not a attribute but a method of View AI!
    cases = [                                                                                                                 
      # ===== SUCCESSFUL RESHAPES =====                                                                                       
      # --- Contiguous ---                                                                                                    
      {"name": "contiguous merge",                                                                                            
       "start": View(shape=(2, 3, 4), strides=(12, 4, 1), offset=0, mask=None, contiguous=True),                              
       "arg": (6, 4),                                                                                                         
       "expected": View(shape=(6, 4), strides=(4, 1), offset=0, mask=None, contiguous=True)},                                 
      {"name": "contiguous split",                                                                                            
       "start": View(shape=(24,), strides=(1,), offset=0, mask=None, contiguous=True),                                        
       "arg": (2, 3, 4),                                                                                                      
       "expected": View(shape=(2, 3, 4), strides=(12, 4, 1), offset=0, mask=None, contiguous=True)},                          
      {"name": "contiguous to scalar",                                                                                        
       "start": View(shape=(1,), strides=(1,), offset=0, mask=None, contiguous=True),                                         
       "arg": (),                                                                                                             
       "expected": View(shape=(), strides=(), offset=0, mask=None, contiguous=True)},                                         
      {"name": "scalar to contiguous",                                                                                        
       "start": View(shape=(), strides=(), offset=0, mask=None, contiguous=True),                                             
       "arg": (1, 1, 1),                                                                                                      
       "expected": View(shape=(1, 1, 1), strides=(1, 1, 1), offset=0, mask=None, contiguous=True)},                           
      {"name": "contiguous with ones",                                                                                        
       "start": View(shape=(1, 10, 1), strides=(10, 1, 1), offset=0, mask=None, contiguous=True),                             
       "arg": (10,),                                                                                                          
       "expected": View(shape=(10,), strides=(1,), offset=0, mask=None, contiguous=True)},                                    
                                                                                                                              
      # --- Non-contiguous (from expand, permute) ---                                                                         
      {"name": "split expanded dim",                                                                                          
       "start": View(shape=(10, 10), strides=(1, 0), offset=0, mask=None, contiguous=False),                                  
       "arg": (10, 2, 5),                                                                                                     
       "expected": View(shape=(10, 2, 5), strides=(1, 0, 0), offset=0, mask=None, contiguous=False)},                         
      {"name": "split other expanded dim",                                                                                    
       "start": View(shape=(10, 10), strides=(0, 1), offset=0, mask=None, contiguous=False),                                  
       "arg": (10, 5, 2),                                                                                                     
       "expected": View(shape=(10, 5, 2), strides=(0, 2, 1), offset=0, mask=None, contiguous=False)},                         
      {"name": "merge after permute",                                                                                         
       "start": View(shape=(3, 4, 2), strides=(4, 1, 12), offset=0, mask=None, contiguous=False),                             
       "arg": (12, 2),                                                                                                        
       "expected": View(shape=(12, 2), strides=(1, 12), offset=0, mask=None, contiguous=False)},                              
      {"name": "double permute with merge",                                                                                   
       "start": View(shape=(4, 4, 4), strides=(1, 16, 4), offset=0, mask=None, contiguous=False),                             
       "arg": (16, 4),                                                                                                        
       "expected": View(shape=(16, 4), strides=(4, 1), offset=0, mask=None, contiguous=True)},                                
                                                                                                                              
      # --- Masked ---                                                                                                        
      {"name": "reshape masked view",                                                                                         
       "start": View(shape=(10,), strides=(1,), offset=0, mask=((2, 8),), contiguous=False),                                  
       "arg": (3, 2),                                                                                                         
       "expected": View(shape=(3, 2), strides=(2, 1), offset=2, mask=((0, 3), (0, 2)), contiguous=False)},                    
      {"name": "reshape with offset",                                                                                         
        "start": View(shape=(6,), strides=(1,), offset=2, mask=None, contiguous=False),                                       
        "arg": (2, 3),                                                                                                        
        "expected": View(shape=(2, 3), strides=(3, 1), offset=2, mask=None, contiguous=False)},                               
      {"name": "masked with pad no-op reshape",                                                                               
       "start": View(shape=(14,), strides=(1,), offset=-2, mask=((2, 12),), contiguous=False),                                
       "arg": (14,),                                                                                                          
       "expected": View(shape=(14,), strides=(1,), offset=-2, mask=((2, 12),), contiguous=False)},                            
                                                                                                                              
      # --- Zero shapes ---                                                                                                   
      {"name": "zero shape to zero shape",                                                                                    
       "start": View(shape=(2, 0, 4), strides=(0, 4, 1), offset=0, mask=None, contiguous=False),                              
       "arg": (0, 3, 1),                                                                                                      
       "expected": View(shape=(0, 3, 1), strides=(0, 0, 0), offset=0, mask=None, contiguous=True)},                           
      {"name": "zero shape with ones",                                                                                        
       "start": View(shape=(1, 10, 0), strides=(0, 0, 1), offset=0, mask=None, contiguous=False),                             
       "arg": (0,),                                                                                                           
       "expected": View(shape=(0,), strides=(0,), offset=0, mask=None, contiguous=True)},                                     
                                                                                                                              
      # ===== FAILED RESHAPES (expected=None) =====                                                                           
      {"name": "permute breaks contiguity",                                                                                   
       "start": View(shape=(3, 2, 4), strides=(4, 12, 1), offset=0, mask=None, contiguous=False),                             
       "arg": (6, 4),                                                                                                         
       "expected": None},                                                                                                     
      {"name": "permute breaks contiguity 2",                                                                                 
       "start": View(shape=(2, 4, 3), strides=(12, 1, 4), offset=0, mask=None, contiguous=False),                             
       "arg": (2, 12),                                                                                                        
       "expected": None},                                                                                                     
      {"name": "expand and permute breaks contiguity",                                                                        
       "start": View(shape=(2, 4, 3), strides=(0, 1, 0), offset=0, mask=None, contiguous=False),                              
       "arg": (2, 12),                                                                                                        
       "expected": None},                                                                                                     
      {"name": "merge expanded dim",                                                                                          
       "start": View(shape=(10, 10), strides=(1, 0), offset=0, mask=None, contiguous=False),                                  
       "arg": (100,),                                                                                                         
       "expected": None},                                                                                                     
      {"name": "non-contiguous to smaller non-contiguous",                                                                    
       "start": View(shape=(8, 2), strides=(1, 8), offset=0, mask=None, contiguous=False),                                    
       "arg": (4, 4),                                                                                                         
       "expected": None},                                                                                                     
      {"name": "masked permute",                                                                                              
       "start": View(shape=(2, 2), strides=(1, 4), offset=5, mask=None, contiguous=False),                                    
       "arg": (4,),                                                                                                           
       "expected": None},                                                                                                     
      {"name": "masked split unaligned",                                                                                      
       "start": View(shape=(10,), strides=(1,), offset=0, mask=((2, 7),), contiguous=False),                                  
       "arg": (2, 3), # size 5 cannot be reshaped to 6                                                                        
       "expected": None},                                                                                                     
                                                                                                                              
      # --- Symbolic ---                                                                                                      
      {"name": "symbolic contiguous",                                                                                         
       "start": View(shape=(UOp.variable('w', 1, 10), 4), strides=(4, 1), offset=0, mask=None, contiguous=True),              
       "arg": (UOp.variable('w', 1, 10) * 4,),                                                                                
       "expected": View(shape=(UOp.variable('w', 1, 10) * 4,), strides=(1,), offset=0, mask=None, contiguous=True)},          
      {"name": "symbolic non-contiguous fail",                                                                                
       "start": View(shape=(4, UOp.variable('w', 1, 10)), strides=(UOp.variable('w', 1, 10), 1), offset=0, mask=None,         
contiguous=False),                                                                                                            
       "arg": (UOp.variable('w', 1, 10) * 4,),                                                                                
       "expected": None},                                                                                                     
      {"name": "symbolic no-op",                                                                                              
       "start": View(shape=(4, UOp.variable('w', 1, 10)), strides=(1, 4), offset=0, mask=None, contiguous=False),             
       "arg": (4, UOp.variable('w', 1, 10)),                                                                                  
       "expected": View(shape=(4, UOp.variable('w', 1, 10)), strides=(1, 4), offset=0, mask=None, contiguous=False)},         
    ]                                                                                                                         


:- end_tests(reshape).
