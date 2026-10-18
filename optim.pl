:- module(optim, [
   operator_fusion//5
]).

:- use_module(library(egraph)).
:- use_module(library(macros)).

#define(array{op: Op}, array{data:_, datasize:_, device:_, dtype:_, id:_, precision:_, range:_, views:_, op:Op}).
#define(
    rewrite(Name, array{op: Left}, array{op: Right}),
    rewrite(Name, array{op: Left}, [], array{op: Right}, [])
).
#define(
    rewrite(Name, array{op: Left}, LeftOptions, array{op: Right}, RightOptions),
    egraph:rewrite(
        Name,
        array{
            data:D, datasize:DS, device:Dev, dtype:DT, id:ID, precision:P, range:R,
            views:V, op: Left
        },
        LeftOptions,
        array{
            data:D, datasize:DS, device:Dev, dtype:DT, id:ID, precision:P, range:R,
            views:V, op: Right
        },
        RightOptions
    )
).

elementwise(rand).
elementwise(contiguous(_)).
elementwise(float(_)).
elementwise(integer(_)).
elementwise(_+_).
elementwise(_*_).
elementwise(_<_).
elementwise(sin(_)).
elementwise(log(_)).
elementwise(sqrt(_)).

egraph:analyze(is_elementwise, #array{op: '$NODE'(Op)}, [elementwise(Op)]) :-
    elementwise(Op).

% Operator fusion: fuse elementwise multiplication into reduce to prevent intermediate allocations
#rewrite(
    operator_fusion_reduce_mul, 
    array{op: reduce(Op, Axes, #array{op:Sub})}, [elementwise(Sub, _)],
    array{op:reduce(Op, Axes, Sub)}, []
).
#rewrite(
    operator_fusion_add,
    array{op: A + #array{op: Op}}, [elementwise(Op, _)],
    array{op: A+Op}, []
).
#rewrite(
    operator_fusion_mul,
    array{op: A * #array{op: Op}}, [elementwise(Op, _)],
    array{op: A*Op}, []
).
#rewrite(
    operator_fusion_comp_right,
    array{op: A < #array{op: Op}}, [elementwise(Op, _)],
    array{op: A<Op}, []
).
#rewrite(
    operator_fusion_comp_left,
    array{op: #array{op: Op} < A}, [elementwise(Op, _)],
    array{op: Op<A}, []
).
#rewrite(
    operator_fusion_float,
    array{op: float(#array{op: Op})}, [elementwise(Op, _)],
    array{op: float(Op)}, []
).
#rewrite(
    operator_fusion_integer,
    array{op: integer(#array{op: Op})}, [elementwise(Op, _)],
    array{op: integer(Op)}, []
).
#rewrite(
    operator_fusion_sin,
    array{op: sin(#array{op: Op})}, [elementwise(Op, _)],
    array{op: sin(Op)}, []
).
#rewrite(
    operator_fusion_log,
    array{op: log(#array{op: Op})}, [elementwise(Op, _)],
    array{op: log(Op)}, []
).
#rewrite(
    operator_fusion_sqrt,
    array{op: sqrt(#array{op: Op})}, [elementwise(Op, _)],
    array{op: sqrt(Op)}, []
).
#rewrite(
    operator_fusion_contiguous,
    array{op: contiguous(#array{op: Op})}, [elementwise(Op, _)],
    array{op: contiguous(Op)}, []
).

#rewrite(comm_add, array{op: A+B}, array{op: B+A}).
#rewrite(assoc_add, array{op: (A+B)+C}, array{op: A+(B+C)}).
#rewrite(comm_mul, array{op: A*B}, array{op: B*A}).
#rewrite(assoc_mul, array{op: (A*B)*C}, array{op: A*(B*C)}).

:- begin_tests(optim).

:- use_module(array).

test('operator_fusion multiplication') :-
    A = array{}.rand([3, 3]),
    B @= A @ A,
    
    phrase((
        add_term(B, Id),
        saturate([is_elementwise, operator_fusion_reduce_mul]),
        extract(Id, Extracted)
    ), [], _),
    
    % print_term(B, []), nl,
    array{op: view(R)} :< Extracted,
    print_term(R, []), nl,
    array{op: reduce(+, [2], _*_)} :< R.

:- end_tests(optim).
