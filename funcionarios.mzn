int: nfuncionarios;
array[1..nfuncionarios, 1..nfuncionarios] of int: matriz;
array[1..nfuncionarios] of var 1..nfuncionarios: asig;


constraint forall(i in 1..nfuncionarios) ((sum(j in 1..nfuncionarios) (asig[j]=i))=1);

var int: suma_asignaciones=sum(i in 1..nfuncionarios)(matriz[asig[i],i]);

solve minimize suma_asignaciones;

