int: n;
int: idaT;
int: vueltaT;

array [1..n,1..2] of int:matriz;

array [1..n] of var 0..1: ida;
array [1..n] of var 0..1: vuelta;


%no se pasa de tiempo
constraint (sum(i in 1..n)(ida[i]*matriz[i,1]))=idaT;
constraint (sum(i in 1..n)(vuelta[i]*matriz[i,1]))=vueltaT;

%no se reproduce 2 veces
constraint forall(i in 1..n)(ida[i]=0 \/ vuelta[i]=0);

%maximizar
var int: satisfaccion=sum(i in 1..n)(ida[i]*matriz[i,2]+vuelta[i]*matriz[i,2]);

solve maximize satisfaccion;





