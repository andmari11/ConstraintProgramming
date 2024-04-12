int: k;
int: V;
int: n;
array [1..n] of int: volume; 

array[1..n,1..k] of var 0..1: asig;

%comprueba que solo se utilice cada volumen una sola vez
constraint forall (i in 1..n)(sum(j in 1..k)(asig[i,j])=1);

%comprueba en cada recipiente que no sobrepase
constraint forall(i in 1..k)(sum(j in 1..n)(asig[j,i]*volume[j])<=V);


solve satisfy;