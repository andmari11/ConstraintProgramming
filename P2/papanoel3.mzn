%introducimos alguna función más para aumentar legibilidad

%introducimos la definición de predicados

include "alldifferent.mzn";

% Número de jugetes
int: m;
constraint assert ( m > 0, "La cantidad de juguetes debe ser mayor que cero" );

% Número de niños
int: n;
constraint assert ( n > 0, "El número de niños debe ser mayor que cero" );

% Número de jugetes a asignar a cada niño
int: ja;
constraint assert ( ja > 0, "El número de juguetes a asignar debe ser mayor que cero" );

% Satisfación mínima
int: s;
constraint assert ( s > 0, "La satisfacción mínima debe ser mayor que cero" );

% Disponibilidad de cada juguete
array[1..m] of int: disp;
constraint assert (forall (i in 1..m) ( disp[i] >= 0 ),
                            "La disponibilidad de cada juguete debe ser mayor o igual que cero" );

% Tipos de juguetes
enum Tipo;

% Tipo de cada juguete
array[1..m] of Tipo: jtipo;

% Satisfacción niño x juguete (puede ser negativa)
array[1..n,1..m] of int: jsat;

% Asignación de jugetes
array[1..n,1..ja] of var 1..m: asig;

% Asignacíon no supera disponibilidad
constraint forall (i in 1..m) ( sum (j in 1..n, k in 1..ja) ( bool2int(asig[j,k]=i) ) <= disp[i] );

% Todos mínima satisfacción
constraint forall (i in 1..n) ( sum (j in 1..ja) ( jsat[i,asig[i,j]] ) >= s);

function var int: mtipo(var 1..m: x) = jtipo[x];
%function var int: mtipo(var int: x) = jtipo[x];
%function var int: mtipo(var int: x) = if x in 1..m then jtipo[x] else jtipo[1] endif;

% Para cada niño ningún tipo igual 
constraint forall (i in 1..n)  (alldifferent( [mtipo(asig[i,j]) | j in 1..ja]));

%constraint forall (i in 1..n) ( jtipo[asig[i,1]] != jtipo[asig[i,2]] );


predicate ordered (array [1..ja] of var 1..m: l) =
            forall (i in 1..ja-1) ( l[i] <= l[i+1] );

%predicate ordered (array [int] of var int: l) =
%            forall (i in 1..length(l)-1) ( l[i] <= l[i+1] );

% Evitar redundancia de soluciones
constraint forall (i in 1..n) ( ordered([asig[i,j] | j in 1..ja]) );

% Obtener solución
solve satisfy;

output ["N:  "] ++ [ "\(i) " | i in 1..n ] ++ ["\n"] ++ 
       [ (if i==1 then "J\(j) :" else "" endif) ++ "\(asig[i,j]-1) " ++ (if i==n then "\n" else "" endif) | j in 1..ja, i in 1..n ]


%output [ "\(asig[i,j] " | i in 1..n, j in 1..ja]