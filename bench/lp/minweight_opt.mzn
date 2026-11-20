% M13-codes-leads-T1 (D-0183): the optimisation face of codes-cp's models/minweight_chk.mzn with
% ENC = 2 (each parity check as sum = 2*y), the question "minimise weight(x), x != 0, Hx = 0".
% Same data files (.dzn from codes-cp's writers/write.py); Wmax is ignored.
int: n;  int: nW;  int: wd;  int: Wmax;
array[1..nW, 1..n] of 0..1: W;
int: nF;  array[1..nF] of 1..n: FA;  array[1..nF] of 1..n: FB;
array[1..n] of var bool: x;
array[1..nW] of var 0..(wd div 2): y;
constraint forall(w in 1..nW)(sum(i in 1..n where W[w, i] = 1)(bool2int(x[i])) = 2 * y[w]);
constraint sum(i in 1..n)(bool2int(x[i])) >= 1;
constraint forall(t in 1..nF)(x[FA[t]] \/ not x[FB[t]]);
var 1..n: weight = sum(i in 1..n)(bool2int(x[i]));
solve minimize weight;
