%Datos del problema
int: nMeses=6;
int: nAceites=5;

int: VALOR; %Valor por el que se vende el producto final por tonelada
int: MAXV; %Máximo de toneladas de aceite vegetal a refinar por mes
int: MAXN; %Máximo de toneladas de aceite no vegetal a refinar por mes

int: MCAP; %Capacidad de almacenamiento de la fábrica para cada tipo

int: CA; %Costes de almacenamiento por tonelada y mes
%Aceites refinados no pueden ser almacenados
float: MinD; %Mínima dureza
float: MaxD; %Máxima dureza
int: MinB; %Beneficio mínimo que tenemos que conseguir
%No más de dos meses de pérdidas consecutivos

int: PV; %No puede variar el almacenamiento del almacén desde el inicio hasta el fin más del PV%


array[1..nAceites] of float: dureza;
array[1..nMeses, 1..nAceites] of int: precios; %Tabla de precios de compra de aceite por mes

array[1..nAceites] of int: inicial; %Toneladas iniciales que tenemos


array [1..nMeses,1..nAceites] of var 0..MCAP: almacen;

array [1..nMeses,1..nAceites] of var 0..MCAP*nAceites: compra;
%refinado~=venta
array [1..nMeses,1..nAceites] of var 0..MCAP*nAceites: refinado;


%----------------------------------------------
%              RESTRICCIONES
%----------------------------------------------

%restriccion de almacenamiento inicial
constraint forall(a in 1..nAceites)(almacen[1,a]== inicial[a]);
%restriccion de almacenamiento coherente
constraint forall(m in 2..nMeses)(forall(a in 1..nAceites)(almacen[m-1,a]+compra[m-1,a]-refinado[m-1,a]==almacen[m,a]));

%restriccion  de refinado maximo(MAXN/MAXV limita a la suma o a cada aceite?)
constraint forall(m in 1..nMeses)(forall(a in 1..2)(refinado[m,a]=MAXV) /\ forall(a in 3..nAceites)(refinado[m,a]=MAXN));
%restriccion  de dureza de refinado
constraint forall(m in 1..nMeses)(sum(v in 1..nAceites)(refinado[m,v]*dureza[v])/sum(v in 1..nAceites)(refinado[m,v])>MinD /\
                                  sum(v in 1..nAceites)(refinado[m,v]*dureza[v])/sum(v in 1..nAceites)(refinado[m,v])<MaxD);
                                  
%restriccion cambio PV
constraint forall(v in 1..nAceites)(abs(inicial[v]-(compra[nMeses,v]+almacen[nMeses,v]-refinado[nMeses,v]))/inicial[v]*100<=PV);

% Función objetivo
%var int: beneficio;
%onstraint beneficio == sum(m in 1..nMeses)(sum(a in 1..nAceites)(refinado[m,a]*VALOR-compra[m,a]*precios[m,a]));
%solve maximize beneficio;

constraint sum(m in 1..nMeses)(sum(a in 1..nAceites)(refinado[m,a]*VALOR-compra[m,a]*precios[m,a]))-sum(m in 1..nMeses-1)(sum(a in 1..nAceites)(almacen[m,a]*CA))>=MinB;
solve satisfy;
