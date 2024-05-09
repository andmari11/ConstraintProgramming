%Datos del problema
int: nMeses=6;
int: nAceites=5;

int: K;
int: T;

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

array [1..nMeses,1..nAceites] of var 0..MCAP: compra;
%refinado~=venta
array [1..nMeses,1..nAceites] of var 0..max(MAXN,MAXV): refinado;
array [1..nMeses] of var -MinB..MinB: beneficios;
array [1..nMeses] of var -10..10: durezas;


%----------------------------------------------
%              RESTRICCIONES
%----------------------------------------------
%falta restriccion de no perdidas dos meses seguidos

%restriccion de almacenamiento inicial
constraint forall(a in 1..nAceites)(almacen[1,a] == inicial[a]);
%restriccion de almacenamiento coherente
constraint forall(m in 2..nMeses,a in 1..nAceites)(almacen[m-1,a]+compra[m-1,a]-refinado[m-1,a]==almacen[m,a]);

%restriccion  de refinado maximo(MAXN/MAXV limita a la suma o a cada aceite?)
constraint forall(m in 1..nMeses)(sum(a in 1..2)(refinado[m,a])=MAXV /\ sum(a in 3..nAceites)(refinado[m,a])=MAXN);

constraint forall(m in 1..nMeses)(durezas[m]==(sum(v in 1..nAceites)(refinado[m,v]*dureza[v]) / sum(v in 1..nAceites)(refinado[m,v])));


%restriccion  de dureza de refinado  
constraint forall(m in 1..nMeses)(
    (
        durezas[m] >= MinD /\
        durezas[m] <= MaxD
    )
    \/ sum(a in 3..nAceites)(refinado[m,a])== 0 
);

                                  
%restriccion cambio PV
constraint forall(v in 1..nAceites)(abs(inicial[v]-(compra[nMeses,v]+almacen[nMeses,v]-refinado[nMeses,v]))/inicial[v]*100<=PV);

%perdidas dos meses seguidos
constraint forall(m in 2..nMeses)(
    (beneficios[m]>= 0) \/
    (beneficios[m-1]>= 0)
);

constraint forall (m in 1..nMeses)(sum(a in 1..nAceites)(refinado[m,a]*VALOR-compra[m,a]*precios[m,a]-almacen[m,a]*CA)==beneficios[m]);

%EXTRA
%no se mezclan mas de k aceites
constraint forall (m in 1..nMeses)(count(a in 1..nAceites)(refinado[m,a]>0)<=K);

%utilizar un minimo de T toneladas
constraint forall (m in 1..nMeses, a in 1..nAceites)(refinado[m,a]>0->refinado[m,a]>=T);

%Si usamos el aceite ANV 1 o el aceite ANV 2 en un cierto mes, entonces VEG 2 tambi´en debe ser usado ese mes. 
%constraint forall(m in 1..nMeses)((refinado[m,3]>0 \/ refinado[m,4]>0) -> refinado[m,2]>0);

% Función objetivo
var int: beneficio_total;
constraint beneficio_total == sum(m in 1..nMeses)(beneficios[m]);

constraint beneficio_total>=MinB;

solve maximize beneficio_total;

% constraint sum(m in 1..nMeses)(sum(a in 1..nAceites)(refinado[m,a]*VALOR-compra[m,a]*precios[m,a]-almacen[m,a]*CA))>=MinB;

