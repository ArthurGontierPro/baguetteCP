% =========================================================================================
%  Un mot de faible poids dans un code binaire fixé : le plan 2×2 de dom/report.md
% =========================================================================================
%  Le mot x (n bits) est dans le code s'il est orthogonal à chaque ligne de W, c'est-à-dire si
%  la somme de x sur chaque ligne est paire. Deux facteurs, choisis indépendamment :
%    - les lignes de W : 24 mots indépendants (une base, dom/sym_pP_wW_basis.dzn) ou les 17296
%      mots de poids minimal (l'orbite entière, dom/sym_pP_wW.dzn) ;
%    - l'écriture de chaque parité, ENC = 1 : une chaîne de XOR binaires égale à faux, que
%      baguette transforme en clauses ; ENC = 2 : somme = 2·y, une inégalité entière.
%  minweight_sym.mzn est le cas « orbite, ENC = 2 ». Les clauses FA/FB imposent trois coordonnées.
% =========================================================================================
int: n;  int: nW;  int: wd;  int: Wmax;  int: ENC;
array[1..nW, 1..n] of 0..1: W;
int: nF;  array[1..nF] of 1..n: FA;  array[1..nF] of 1..n: FB;

array[1..n] of var bool: x;

constraint if ENC = 2 then
  let { array[1..nW] of var 0..(min(wd, Wmax) div 2): y } in
  forall(w in 1..nW)(sum(i in 1..n where W[w, i] = 1)(bool2int(x[i])) = 2 * y[w])
else
  forall(w in 1..nW)(
    let { array[int] of int: R = [i | i in 1..n where W[w, i] = 1];
          int: r = length(R);
          array[1..r] of var bool: acc } in
    acc[1] = x[R[1]] /\ forall(t in 2..r)(acc[t] = (acc[t-1] xor x[R[t]])) /\ not acc[r])
endif;
constraint sum(i in 1..n)(bool2int(x[i])) >= 1;
constraint sum(i in 1..n)(bool2int(x[i])) <= Wmax;
constraint forall(t in 1..nF)(x[FA[t]] \/ not x[FB[t]]);

solve :: bool_search(x, input_order, indomain_max) satisfy;
output ["x = \(x)\n"];
