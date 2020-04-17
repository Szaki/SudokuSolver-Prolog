% :- type sspec ---> s(size, board).
% :- type size  == int.
% :- type field == list(info).
% :- type info ---> e; o; s; w; v(int).
% :- type board == list(list(field)).
% :- type ssol == list(list(int)).

?- use_module(library(between)).
?- use_module(library(lists)).
?- use_module(library(sets)).

% :- pred sudoku(sspec::in, ssol::out).
sudoku(Spec, Sol) :-
    s(Size, Board) = Spec,
    Interval is Size*Size,
    findall(SanCell, sanitize(Board, SanCell), SanCells),
    board(Interval, SanCells, SanBoard),
    \+ isillegal(s(Size, SanBoard)),
    findall(Val, cellvals(s(Size, SanBoard), Val), FilledCells),
    board(Interval, FilledCells, FilledBoard),
    reduce(s(Size, FilledBoard), ReducedBoard),
    solution(s(Size, ReducedBoard), 0, 0, Solution),
    findall(Cell, clean(Solution, Cell), Cells),
    board(Interval, Cells, Sol).

% :- pred isillegal(sspec::in).
isillegal(Spec) :-
    s(Size, Board) = Spec,
    Iter is (Size*Size)-1,
    between:between(0, Iter, Row),
    lists:nth0(Row, Board, Cols),
    between:between(0, Iter, Col),
    lists:nth0(Col, Cols, Cell),
    (
        member(e, Cell), member(o, Cell) -> true, !;
        findall(N, nums(Cell, N), CellNums), [H|T] = CellNums,
        (
            T \== [] -> true, !;
            member(e, Cell), (H mod 2) =:= 1 -> true, !;
            member(o, Cell), (H mod 2) =:= 0 -> true, !;
            ColMinus is Col-1, RowPlus is Row+1,
            (
                member(w, Cell), cell(Board, Row, ColMinus, WCell),
                findall(N, nums(WCell, N), WCellNums),
                [WH|[]] = WCellNums,
                (WH mod 2) =:= (H mod 2) ->
                    true, !;
                member(s, Cell),
                cell(Board, RowPlus, Col, SCell),
                findall(N, nums(SCell, N), SCellNums),
                [SH|[]] = SCellNums,
                (SH mod 2) =:= (H mod 2) ->
                    true, !
            )
        );
        findall(N, colnums(Board, Col, N), ColNums), \+ sets:is_set(ColNums) -> true, !;
        findall(N, rownums(Board, Row, N), RowNums), \+ sets:is_set(RowNums) -> true, !;
        findall(N, subboardnums(Spec, Row, Col, N), SubboardNums), \+ sets:is_set(SubboardNums) -> true, !
    ).

% :- pred clean(board::in, int::out).
clean(Board, Num) :-
    member(Row, Board),
    member(Cell, Row),
    [Num|_] = Cell.

% :- pred sanitizecell(field::in, info::out).
sanitizecell(Cell, Bit) :-
    member(Info, Cell),
    (
        v(N) = Info -> Bit = N;
        Bit = Info
    ).

% :- pred sanitize(board::in, field::out).
sanitize(Board, SanCell) :-
    member(Row, Board),
    member(Cell, Row),
    findall(I, sanitizecell(Cell, I), SanCell).

% :- pred solution(sspec::in, int::in, int::in, field::out).
solution(Spec, Row, Col, Sol) :-
    s(Size, Board) = Spec,
    Len is (Size*Size)-1,
    lists:nth0(Row, Board, Cols),
    lists:nth0(Col, Cols, Cell),
    findall(N, nums(Cell, N), CellNums),
    [_|T] = CellNums,
    (
        T == [] -> (
            Col =:= Len, Row =:= Len -> \+ isillegal(Spec), \+ isdefective(Board),
                Sol = Board;
            Col =:= Len -> NextRow is Row+1, solution(Spec, NextRow, 0, Sol);
            NextCol is Col+1, solution(Spec, Row, NextCol, Sol)
        );
        findall(I, adjinfo(Cell, I), Adj),
        member(Num, CellNums),
        update(Spec, Row, Col, [Num|Adj], Updated),
        solution(Updated, Row, Col, Sol)
    ).

% :- pred update(sspec::in, int::in, int::in, field::in, sspec::out).
update(Spec, URow, UCol, NewVal, Updated) :-
    s(Size, _) = Spec,
    Interval is Size*Size,
    findall(Val, updatecells(Spec, URow, UCol, NewVal, Val), UpdatedCells),
    board(Interval, UpdatedCells, UpdatedBoard),
    reduce(s(Size, UpdatedBoard), Reduced),
    Updated = s(Size, Reduced).

% :- pred updatecells(sspec::in, int::in, int::in, field::in, field::out).
updatecells(Spec, URow, UCol, NewVal, Val) :-
    s(Size, Board) = Spec,
    Iter is (Size*Size)-1,
    between:between(0, Iter, Row),
    lists:nth0(Row, Board, Cols),
    between:between(0, Iter, Col),
    lists:nth0(Col, Cols, Cell),
    (
        Row =:= URow, Col =:= UCol -> Val = NewVal;
        Val = Cell
    ).

% :- pred reduce(sspec::in, board::out).
reduce(Spec, Reduced) :-
    s(Size, Board) = Spec,
    Interval is Size*Size,
    findall(ReducedCell, reducecells(Spec, ReducedCell), ReducedCells),
    board(Interval, ReducedCells, ReducedBoard),
    (
        ReducedBoard == Board -> Reduced = ReducedBoard, !;
        reduce(s(Size, ReducedBoard), Reduced)
    ).

% :- pred reducecells(sspec::in, field::out).
reducecells(Spec, Reduced) :-
    s(Size, Board) = Spec,
    Interval is Size*Size,
    Iter is Interval-1,
    between:between(0, Iter, Row),
    lists:nth0(Row, Board, Cols),
    between:between(0, Iter, Col),
    lists:nth0(Col, Cols, UnfilteredCell),
    filtercell(Board, Row, Col, UnfilteredCell, Cell),
    findall(N, nums(Cell, N), CellNums),
    (
        CellNums == [] ->
            findall(Val, fixcellvals(Board, Val), FixVals),
            board(Interval, FixVals, FixBoard),
            findall(N, usednums(s(Size, FixBoard), Row, Col, N), UsedNums),
            sets:subtract(Cell, UsedNums, Reduced);
        [_|[]] = CellNums ->
            Reduced = Cell;
        findall(N, rownums(Board, Row, N), RowNums),
        findall(N, unique(CellNums, RowNums, N), RowUnique),
        [R|U] = RowUnique, findall(I, adjinfo(Cell, I), Adj) ->
            (
                U == [] -> Reduced = [R|Adj];
                lists:append(RowUnique, Adj, Reduced)
            );
        findall(N, colnums(Board, Col, N), ColNums),
        findall(N, unique(CellNums, ColNums, N), ColUnique),
        [R|U] = ColUnique, findall(I, adjinfo(Cell, I), Adj) ->
            (
                U == [] -> Reduced = [R|Adj];
                lists:append(ColUnique, Adj, Reduced)
            );
        findall(N, subboardnums(Spec, Row, Col, N), SubboardNums),
        findall(N, unique(CellNums, SubboardNums, N), SubboardUnique),
        [R|U] = SubboardUnique, findall(I, adjinfo(Cell, I), Adj) ->
            (
                U == [] ->  Reduced = [R|Adj];
                lists:append(SubboardUnique, Adj, Reduced)
            );
        findall(Val, fixcellvals(Board, Val), FixVals),
        board(Interval, FixVals, FixBoard),
        findall(N, usednums(s(Size, FixBoard), Row, Col, N), UsedNums),
        sets:subtract(Cell, UsedNums, Reduced)
    ).

% :- pred cellvals(sspec::in, field::out).
cellvals(Spec, Vals) :-
    s(Size, Board) = Spec,
    Interval is Size*Size,
    Iter is Interval-1,
    between:between(0, Iter, Row),
    lists:nth0(Row, Board, Cols),
    between:between(0, Iter, Col),
    lists:nth0(Col, Cols, Cell),
    findall(N, nums(Cell, N), CellNums),
    findall(I, adjinfo(Cell, I), Adj),
    (
        [H|[]] = CellNums -> Vals = [H|Adj];
        findall(N, usednums(Spec, Row, Col, N), UsedNums),
        (
            member(e, Cell) -> findall(N,
                    (between:between(1, Interval, N),
                    N mod 2 =:= 0, \+ member(N, UsedNums)),
                Nums), lists:append(Nums, Adj, Vals);
            member(o, Cell) -> findall(N,
                    (between:between(1, Interval, N),
                    N mod 2 =:= 1, \+ member(N, UsedNums)),
                Nums), lists:append(Nums, Adj, Vals);
            findall(N,
                    (between:between(1, Interval, N),
                    \+ member(N, UsedNums)),
                Nums), lists:append(Nums, Adj, Vals)
        )
    ).

% :- pred fixcellvals(board::in, list(int)::out).
fixcellvals(Board, Vals) :-
    member(Row, Board),
    member(Cell, Row),
    findall(N, nums(Cell, N), CellNums),
    (
        [_|[]] = CellNums -> Vals = CellNums;
        Vals = []
    ).

% :- pred isdefective(board::in).
isdefective(Board) :-
    member(Row, Board),
    member(Cell, Row),
    \+ nums(Cell, _),
    !.

% :- pred filtercell(board::in, int::in, int::in, field::in, field::out).
filtercell(Board, Row, Col, Cell, Filtered) :-
    ColPlus is Col+1,
    RowMinus is Row-1,
    cell(Board, Row, ColPlus, ECell),
    parity(ECell, w, E),
    cell(Board, RowMinus, Col, NCell),
    parity(NCell, s, N),
    (
        E =:= 0, N =:= 0 -> Filtered = Cell;
        E =:= 2, N =\= 1 -> findall(I, parityfilter(Cell, 1, I), Filtered);
        N =:= 2, E =\= 1 -> findall(I, parityfilter(Cell, 1, I), Filtered);
        E =:= 1, N =\= 2 -> findall(I, parityfilter(Cell, 0, I), Filtered);
        N =:= 1, E =\= 2 -> findall(I, parityfilter(Cell, 0, I), Filtered);
        Filtered = []
    ).

% :- pred parityfilter(field::in, int::in, info::out).
parityfilter(Cell, Mod, Info) :-
    member(Info, Cell),
    (
        \+ number(Info) -> true;
        Info mod 2 =:= Mod -> true
    ).

% :- pred even(list(int)::in).
even(Nums) :-
    member(N, Nums),
    N mod 2 =:= 1,
    !.

% :- pred odd(list(int)::in).
odd(Nums) :-
    member(N, Nums),
    N mod 2 =:= 0,
    !.

% :- pred parity(field::in, info::in, int::out).
parity(Field, Type, Val) :-
    (
        member(Type, Field),
        findall(N, nums(Field, N), Nums),
        Nums \== [] ->
        (
            \+ even(Nums) -> Val = 2;
            \+ odd(Nums) -> Val = 1;
            Val = 0
        );
        Val = 0
    ).

% :- pred usednums(sspec::in, int::in, int::in, int::out).
usednums(Spec, _, Col, Num) :-
    s(_, Board) = Spec,
    colnums(Board, Col, Num).
usednums(Spec, Row, _, Num) :-
    s(_, Board) = Spec,
    rownums(Board, Row, Num).
usednums(Spec, Row, Col, Num) :-
    subboardnums(Spec, Row, Col, Num).

% :- pred colnums(board::in, int::in, int::out).
colnums(Board, Col, Num) :-
    member(Row, Board),
    lists:nth0(Col, Row, Field),
    nums(Field, Num).

% :- pred rownums(board::in, int::in, int::out).
rownums(Board, Row, Num) :-
    lists:nth0(Row, Board, RowFields),
    member(Field, RowFields),
    nums(Field, Num).

% :- pred subboardnums(sspec::in, int::in, int::in, int::out).
subboardnums(Spec, Row, Col, Num) :-
    s(Size, Board) = Spec,
    R is Row//Size*Size,
    C is Col//Size*Size,
    slice(Board, R, Size, Rows),
    member(RowElement, Rows),
    slice(RowElement, C, Size, Cols),
    member(Field, Cols),
    nums(Field, Num).

% :- pred adjinfo(field::in, field::out).
adjinfo(Field, Info) :-
    member(Info, Field),
    (
        Info == s; Info == w
    ).

% :- pred nums(field::in, int::out).
nums(Field, Num) :-
    member(Num, Field),
    number(Num).

% :- pred cell(board::in, int::in, int::in, field::out).
cell(Board, Row, Col, Cell) :-
    length(Board, L),
    (
        Row >= 0, Row < L, Col >= 0, Col < L ->
            lists:nth0(Row, Board, Cols), lists:nth0(Col, Cols, Cell);
        Cell = []
    ).

% :- pred unique(list(int)::in, list(field)::in, int::out).
unique(CellNums, Relevant, Num) :-
    member(Num, CellNums),
    lists:selectchk(Num, Relevant, Rest),
    \+ member(Num, Rest).

% :- pred board(int::in, list(field)::in, board::out).
board(_,[], Board) :-
    Board = [],
	!.
board(Interval, Vals, Board) :-
    lists:append_length(Row, Rest, Vals, Interval),
    board(Interval, Rest, Rows),
	Board = [Row|Rows].

% :- pred slice(list::in, int::in, int::in, list::out).
slice(List, Start, Len, Sub):-
    lists:append_length(_, Rest, List, Start),
    lists:append_length(Sub, _, Rest, Len).
