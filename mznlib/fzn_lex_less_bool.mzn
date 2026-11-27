% M18-coverage-T5 (docs/DECISIONS.md D-0239): lex_less over Booleans, the rows of
% fzn_lex_lesseq_bool.mzn with the strict tail (x shorter than y, else false).

include "fzn_lex_lesseq_bool.mzn";

predicate fzn_lex_less_bool(array [int] of var bool: xs, array [int] of var bool: ys) =
  baguette_lex_rows_bool(xs, ys, length(xs) < length(ys));
