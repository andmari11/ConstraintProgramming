% Número de jugetes
int: m;
constraint assert ( m > 0, "La cantidad de juguetes debe ser mayor que cero" );

% Número de niños
int: n;
constraint assert ( n > 0, "El número de niños debe ser mayor que cero" );

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
array[1..n,1..2] of var 1..m: asig;

% Asignacíon no supera disponibilidad
constraint forall (i in 1..m) ( sum (j in 1..n, k in 1..2) ( bool2int(asig[j,k]=i) ) <= disp[i] );

% Todos mínima satisfacción
constraint forall (i in 1..n) ( sum (j in 1..2) ( jsat[i,asig[i,j]] ) >= s);

% No dos tipos iguales
constraint forall (i in 1..n) ( jtipo[asig[i,1]] != jtipo[asig[i,2]] );

% Evitar redundancia de soluciones
constraint forall (i in 1..n) ( asig[i,1] < asig[i,2] );

% Obtener solución
% solve satify;
solve maximize sum (i in 1..n, j in 1..2) ( jsat[i,asig[i,j]] );

output ["N:  "] ++ [ "\(i) " | i in 1..n ] ++ ["\n"] ++ 
       ["J1: "] ++ [ "\(asig[i,1]) " | i in 1..n ] ++ ["\n"] ++ 
       ["J2: "] ++ [ "\(asig[i,2]) " | i in 1..n ];


%output [ "\(asig[i,1]-1) \(asig[i,2]-1) " | i in 1..n ]