:- module(optim, [
   operator_fusion//5
]).

:- use_module(library(egraph)).
:- use_module(library(macros)).

#define(array{op: Op}, array{data:_, datasize:_, device:_, dtype:_, id:_, precision:_, range:_, views:_, op:Op}).
#define(
    rewrite(Name, array{op: Left}, array{op: Right}),
    egraph:rewrite(
        Name,
        array{
            data:D, datasize:DS, device:Dev, dtype:DT, id:ID, precision:P, range:R,
            views:V, op: Left
        },
        array{
            data:D, datasize:DS, device:Dev, dtype:DT, id:ID, precision:P, range:R,
            views:V, op: Right
        }
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
    array{op: reduce(Op, Axes, #array{op:Sub})}, [elementwise(Sub)],
    array{op:reduce(Op, Axes, Sub)}, []
).
#rewrite(
    operator_fusion_add,
    array{op: A + #array{op: Op}}, [elementwise(Op)],
    array{op: A+Op}, []
).
#rewrite(
    operator_fusion_mul,
    array{op: A * #array{op: Op}}, [elementwise(Op)],
    array{op: A*Op}, []
).
#rewrite(
    operator_fusion_comp_right,
    array{op: A < #array{op: Op}}, [elementwise(Op)],
    array{op: A<Op}, []
).
#rewrite(
    operator_fusion_comp_left,
    array{op: #array{op: Op} < A}, [elementwise(Op)],
    array{op: Op<A}, []
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
        saturate([operator_fusion]),
        extract(Id, Extracted)
    ), [], _),
    
    % print_term(B, []), nl,
    array{op: view(R)} :< Extracted,
    print_term(R, []), nl,
    array{op: reduce(+, [2], _*_)} :< R.

:- end_tests(optim).
