%Datos del problema
int: nMeses;
int: nVeg;
int: nNoVeg;
int: nAceites=nVeg+nNoVeg;

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

%----------------------------------------------
%              ASSERTS
%----------------------------------------------
constraint assert(nMeses > 0, "El número de meses debe ser mayor que cero");
constraint assert(nVeg >= 0, "El número de aceites vegetales no puede ser negativo");
constraint assert(nNoVeg >= 0, "El número de aceites no vegetales no puede ser negativo");
constraint assert(K > 0, "El número de aceites a mezclar debe ser mayor que cero");
constraint assert(T > 0, "El mínimo de toneladas a utilizar debe ser mayor que cero");
constraint assert(VALOR > 0, "El valor de venta por tonelada debe ser mayor que cero");
constraint assert(MAXV >= 0, "El máximo de toneladas de aceite vegetal a refinar por mes no puede ser negativo");
constraint assert(MAXN >= 0, "El máximo de toneladas de aceite no vegetal a refinar por mes no puede ser negativo");
constraint assert(MCAP > 0, "La capacidad de almacenamiento de la fábrica para cada tipo debe ser mayor que cero");
constraint assert(CA >= 0, "Los costes de almacenamiento por tonelada y mes no pueden ser negativos");
constraint assert(MinD >= 0, "La dureza mínima no puede ser negativa");
constraint assert(MaxD >= MinD, "La dureza máxima no puede ser menor que la dureza mínima");
constraint assert(MinB >= 0, "El beneficio mínimo que tenemos que conseguir no puede ser negativo");
constraint assert(PV >= 0, "El porcentaje de variación del almacenamiento no puede ser negativo");

%----------------------------------------------
%              RESTRICCIONES
%----------------------------------------------
%falta restriccion de no perdidas dos meses seguidos

%restriccion de almacenamiento inicial
constraint forall(a in 1..nAceites)(almacen[1,a] == inicial[a]);
%restriccion de almacenamiento coherente
constraint forall(m in 2..nMeses,a in 1..nAceites)(almacen[m-1,a]+compra[m-1,a]-refinado[m-1,a]==almacen[m,a]);

%restriccion  de refinado maximo(MAXN/MAXV limita a la suma o a cada aceite?)
constraint forall(m in 1..nMeses)(sum(a in 1..nVeg)(refinado[m,a])<=MAXV /\ sum(a in nVeg+1..nAceites)(refinado[m,a])<=MAXN);


%restriccion  de dureza de refinado  
constraint forall(m in 1..nMeses)(
    (
        sum(v in 1..nAceites)(refinado[m,v]*dureza[v]) >= sum(v in 1..nAceites)(MinD*refinado[m,v])/\
        sum(v in 1..nAceites)(refinado[m,v]*dureza[v]) <= sum(v in 1..nAceites)(MaxD*refinado[m,v])
    )
    \/ sum(a in 3..nAceites)(refinado[m,a])== 0 
);

                                  
%restriccion cambio PV
constraint forall(v in 1..nAceites)(abs(inicial[v]-(compra[nMeses,v]+almacen[nMeses,v]-refinado[nMeses,v]))<=PV*inicial[v]/100);

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
constraint forall(m in 1..nMeses)((refinado[m,nVeg+1]>0 \/ refinado[m,nVeg+2]>0) -> refinado[m,2]>0);

% Función objetivo
var int: beneficio_total;
constraint beneficio_total == sum(m in 1..nMeses)(beneficios[m]);

constraint beneficio_total>=MinB;

solve maximize beneficio_total;

