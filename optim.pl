:- module(optim, [
   operator_fusion//5
]).

:- use_module(library(egraph)).

% Operator fusion: fuse elementwise multiplication into reduce to prevent intermediate allocations
egraph:rewrite(operator_fusion, 
               array{data:D, datasize:DS, device:Dev, dtype:DT, id:ID, op:reduce(Op, Axes, array{data:D2, datasize:DS2, device:Dev2, dtype:DT2, id:ID2, op:A * B, precision:P2, range:R2, views:V2}), precision:P, range:R, views:V}, 
               array{data:D, datasize:DS, device:Dev, dtype:DT, id:ID, op:reduce(Op, Axes, A * B), precision:P, range:R, views:V}).

:- begin_tests(optim).

:- use_module(array).

test('operator_fusion multiplication') :-
    A = array{}.rand([3, 3]),
    B @= A @ A,
    
    phrase((
        egraph:add_term(B, Extracted),
        egraph:saturate([operator_fusion]),
        egraph:extract
    ), [], _),
    
    Extracted.op = view(R),
    R.op = reduce(+, [2], _ * _).

:- end_tests(optim).
