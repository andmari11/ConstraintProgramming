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
%No se pueden vender más de MAXV/MAXN por mes


array [1..nMeses,1..nAceites] of var 0..MCAP: almacen;
array [1..nMeses,1..nAceites] of var 0..MCAP*nAceites: compra;

%refinado~=venta
array [1..nMeses,1..nAceites] of var 0..MCAP*nAceites: venta;

%limitamos el refinado de aceites, diferenciando entre vegetal y no vegetal
constraint forall (m in 1..nMeses)(sum(v in 1..2)(venta[m,v])=MAXV);
constraint forall (m in 1..nMeses)(sum(v in 3..nAceites)(venta[m,v])=MAXN);


%limitamos la compra
constraint forall (m in 1..nMeses)(forall(v in 1..nAceites)(compra[m,v]>=0 /\ venta[m,v]>=0));


%venta-compra-almacenaje->beneficios MinB
constraint sum(m in 1..nMeses)(sum(v in 1..nAceites)(venta[m,v]*VALOR-compra[m,v]*precios[m,v]-almacen[m,v]*CA))>=MinB;


%almacenamiento inicial
constraint forall(v in 1..nAceites)(almacen[1,v]=inicial[v]);
%regulamos que el almacenaje sea coherente
constraint forall(m in 1..nMeses-1)(forall(v in 1..nAceites)(compra[m,v]+almacen[m,v]-venta[m,v]=almacen[m+1,v]));
%max pv de cambio almacen inicial
constraint forall(v in 1..nAceites)(abs(inicial[v]-(compra[nMeses,v]+almacen[nMeses,v]-venta[nMeses,v]))/inicial[v]*100<=PV);


%no vender mas de la cuenta
constraint forall(m in 1..nMeses)(forall(v in 1..nAceites)(venta[m,v]<=almacen[m,v]+compra[m,v]));

%refinado dureza
constraint forall(m in 1..nMeses)(sum(v in 1..nAceites)(venta[m,v]*dureza[v])/sum(v in 1..nAceites)(venta[m,v])>MinD /\
                                  sum(v in 1..nAceites)(venta[m,v]*dureza[v])/sum(v in 1..nAceites)(venta[m,v])<MaxD);

solve satisfy;


