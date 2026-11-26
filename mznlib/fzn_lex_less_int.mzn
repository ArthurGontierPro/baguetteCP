% M18-coverage-T5 (docs/DECISIONS.md D-0239): lex_less over integers, the rows of
% fzn_lex_lesseq_int.mzn with the strict tail (x shorter than y, else false).

include "fzn_lex_lesseq_int.mzn";

predicate fzn_lex_less_int(array [int] of var int: xs, array [int] of var int: ys) =
  baguette_lex_rows(xs, ys, length(xs) < length(ys));
