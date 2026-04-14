:- module(optim, [
   operator_fusion//5
]).

:- use_module(library(egraph)).

% Operator fusion: fuse elementwise multiplication into reduce to prevent intermediate allocations
egraph:rewrite(
    operator_fusion, 
    array{
        data:D, datasize:DS, device:Dev, dtype:DT, id:ID, precision:P, range:R, views:V,
        op: reduce(Op, Axes,
            array{
                data:_, datasize:_, device:_, dtype:_, id:_, precision:_, range:_, views:_,
                op:A * B
            }
        )
    }, 
    array{
        data:D, datasize:DS, device:Dev, dtype:DT, id:ID, precision:P, range:R, views:V,
        op:reduce(Op, Axes, A * B)
    }
).

:- begin_tests(optim).

:- use_module(array).

test('operator_fusion multiplication') :-
    A = array{}.rand([3, 3]),
    B @= A @ A,
    
    once(phrase((
        add_term(B, Extracted),
        saturate([operator_fusion]),
        extract
    ), [], _)),
    
    % print_term(B, []), nl,
    array{op: view(R)} :< Extracted,
    print_term(R, []), nl,
    array{op: reduce(+, [2], _*_)} :< R.

:- end_tests(optim).
