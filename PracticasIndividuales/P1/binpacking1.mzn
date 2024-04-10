int: k;
int: V;
int: n;
array [1..n] of int: volume; 

array[1..n] of var 1..k: asig;

%comprueba en cada recipiente que no sobrepase
constraint forall(i in 1..k)(sum(j in 1..n where asig[j]=i)(volume[j])<=V);

%evitar rebundancia de soluciones
constraint forall(i in 2..n where volume[i-1]=volume[i])(asig[i-1]<=asig[i]);

solve satisfy;