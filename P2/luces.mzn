int: nLuces;
int: nColores;
int: consumoMax;

array[1..nColores] of int: colorConsumo;
array[1..nLuces] of var 1..nColores: rollos;

%luces de colores validos
constraint forall (i in 1..nLuces) (rollos[i]<=nColores);

%luces distintas
constraint forall (i in 2..nLuces-1) (rollos[i-1] != rollos[i] \/ rollos[i] != rollos[i+1]);

%consumo max
constraint (sum(i in 1..nLuces) (colorConsumo[rollos[i]]))<=consumoMax;

%luces no son mas de la mitad
constraint forall (i in 1..nLuces) (sum(j in 1..i)(rollos[j]=rollos[i])<=1+sum(j in 1..i)(rollos[i]!=rollos[j]));

solve satisfy;



