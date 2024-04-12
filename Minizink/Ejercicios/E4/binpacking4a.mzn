int: k;
int: V;
int: n;
array [1..n] of int: volume; 

var 1..k: minK;
array[1..n] of var 1..k: asig;

%comprueba que no se utilicen los recipientes que sobran
constraint forall(i in 1..n)(asig[i]<=minK);

%comprueba en cada recipiente que no sobrepase
constraint forall(i in 1..minK)(sum(j in 1..n where asig[j]=i)(volume[j])<=V);

%evitar rebundancia de soluciones
constraint forall(i in 2..n where volume[i-1]=volume[i])(asig[i-1]<=asig[i]);

solve minimize minK;