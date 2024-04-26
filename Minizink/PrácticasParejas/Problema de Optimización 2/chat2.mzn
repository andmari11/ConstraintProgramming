include "globals.mzn"; % Importamos librerías globales para usar algunas funciones

% Datos del problema
int: nMeses = 6;
int: nAceites = 5;

int: VALOR;
int: MAXV;
int: MAXN;
int: MCAP;
int: CA;
float: MinD;
float: MaxD;
int: MinB;
int: PV;

array[1..nAceites] of float: dureza;
array[1..nMeses, 1..nAceites] of int: precios;
array[1..nAceites] of int: inicial;

% Variables de decisión
array[1..nMeses, 1..nAceites] of var 0..MCAP: almacen;
array[1..nMeses, 1..nAceites] of var 0..MCAP*nAceites: compra;
array[1..nMeses, 1..nAceites] of var 0..MCAP*nAceites: venta;

% Restricciones
constraint forall (m in 1..nMeses, v in 1..nAceites) (
    venta[m,v] >= 0 /\ compra[m,v] >= 0
);

% Restricciones de refinado
constraint forall (m in 1..nMeses) (
    sum(v in 1..2)(venta[m,v]) <= MAXV /\
    sum(v in 3..nAceites)(venta[m,v]) <= MAXN
);

% Restricciones de compra y venta
constraint forall(m in 1..nMeses)(forall(v in 1..nAceites)(venta[m,v]<=almacen[m,v]+compra[m,v]));
constraint forall(m in 1..nMeses-1)(forall(v in 1..nAceites)(compra[m,v]+almacen[m,v]-venta[m,v]=almacen[m+1,v]));


% Restricción de dureza
constraint forall (m in 1..nMeses) (
    sum(v in 1..nAceites)(venta[m,v]*dureza[v]) / sum(v in 1..nAceites)(venta[m,v]) > MinD /\
    sum(v in 1..nAceites)(venta[m,v]*dureza[v]) / sum(v in 1..nAceites)(venta[m,v]) < MaxD
);

% Restricción de variación de almacenamiento
constraint forall(m in 1..nMeses)(sum(v in 1..nAceites)(venta[m,v]*dureza[v])/sum(v in 1..nAceites)(venta[m,v])>MinD /\
                                  sum(v in 1..nAceites)(venta[m,v]*dureza[v])/sum(v in 1..nAceites)(venta[m,v])<MaxD);


% Restricción de beneficio mínimo
var int: beneficio_total = sum(m in 1..nMeses, v in 1..nAceites)(
    venta[m,v]*VALOR - compra[m,v]*precios[m,v] - almacen[m,v]*CA
);
constraint beneficio_total >= MinB;

solve satisfy;
