% Número de aceites vegetales.
int: NAceitesVegetales;

% Número de aceites no vegetales.
int: NAceitesNoVegetales;

% Número de aceites.
int: NAceites = NAceitesVegetales + NAceitesNoVegetales;

% Número de Meses para los que se desea planificar la fabricación.
int: Meses;

% Número de aceites máximos que se pueden mezclar mensualmente.
int: K;

% Toneladas mínimas a refinar de cualquier aceite que deseemos usar.
int :T;

% Tabla de Precios de los aceites por Meses.
array[1..Meses, 1..NAceites] of int: Precios;

%Precio de venta del producto final mensual.
array[1..Meses] of int: PreciosMensual;

% Máxima cantidad que se puede refinar de aceites vegetales.
int: MAXV;

% Máxima cantidad de aceites no vegetales que se puede refinar.
int: MAXN;

% Máxima capacidad del almacén de aceite sin refinar.
int: MCAP;

% Maxima capacidad del almacén de aceite refinado.
int: MCAPR;

% Costes de almacenamiento de aceite sin refinar.
int: CA;

% Costes de almacenamiento de aceites refinados.
int: CAR;

% Mínima dureza de nuestro producto final.
float: MinD;

% Máxima dureza de nuestro producto final.
float: MaxD;

% Lista de las Durezas de cada aceite sin refinar.
array[1..NAceites] of float: Durezas;

% Lista de las cantidades que tenemos que quedarnos al finalizar la producción.
array[1..NAceites] of int: RestanteFinal;

% Tabla que nos indica las restricciones de aceites a utilizar (los trues de la fila 0 indican los aceites a usar si se usa el aceite 0).
array [1..NAceites, 1..NAceites] of bool: AceitesAUsar;

% Mínimo beneficio obtenido.
int: MinB;

% Tabla que nos indica cuando realizar las compras, cantidad y de que aceite.
array[1..Meses, 1..NAceites] of var 0..MCAP: compras;

% Tabla de refinamientos que nos indica cuando, cuales y que cantidad refinar.
array[1..Meses, 1..NAceites] of var 0..max(MAXV, MAXN): refinado;

%  que nos indica las cantidades a vender de cada aceite.
array[1..Meses] of var 0..(MAXN + MAXV + MCAPR): ventaMensual;

% Variable que nos permitirá guardar el beneficio.
var int: beneficio;

%%%%%%%%%%%%%%%%%%%%%%%    Constraints Assert    %%%%%%%%%%%%%%%%%%%%%%%
constraint assert(MinD < MaxD, "El mínimo y el máximo se encuentran intercambiados");

constraint assert(max(RestanteFinal) < MCAP, "Los almacenes de aceite no refinado tienen tamaño \(MCAP), por lo que el restante final de cada aceite no puede superar esa cantidad.");

constraint assert(exists(i in 1..NAceites)(Durezas[i] >= MinD /\ Durezas[i] <= MaxD) \/ (exists(i in 1..NAceites)(Durezas[i] <= MinD) /\ exists(i in 1..NAceites)(Durezas[i] >= MaxD)), "Imposible alcanzar la dureza deseada.");

constraint assert((MAXN + MAXV) * max(PreciosMensual) * Meses > MinB, "Es imposible alcanzar el beneficio mínimo refinando como máximo MAXN + MAXV mensualmente con los Precios de venta del mercado.");

constraint assert(T <= MAXV /\ T <= MAXN, "T debe ser menor que MAXV y MAXN, si T es mayor que MAXV no se podría usar aceites vegetales, igualmente pasaría con los aceites no vegetales si T es mayor que MAXN.");
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Función que nos permite calcular el restante de un aceite concreto en un mes concreto.
function var int: restanteMes(array[1..Meses, 1..NAceites] of var int: compras, array[1..Meses, 1..NAceites] of var int: refinado, int: mes, int: aceite) = if mes = 0 then 0 
                                                                                                                                       else sum(i in 1..mes)(compras[i, aceite] - refinado[i, aceite]) endif;
                                                                                                                                     
% La función hace exactamente lo mismo que antes pero ahora nos permite usarla para imprimir.                                                                                                                          
function int: restanteMes(array[1..Meses, 1..NAceites] of int: compras, array[1..Meses, 1..NAceites] of int: refinado, int: mes, int: aceite) = if mes = 0 then 0
                                                                                                                                        else sum(i in 1..mes)(compras[i, aceite] - refinado[i, aceite])
                                                                                                                                        endif;

% Función que nos permite calcular el restante de aceite refinado en un mes (es aceite que se produce pero se guarda en el almacén para luego venderlo más caro).
function var int: restanteMesRefinado(array[1..Meses, 1..NAceites] of var int: refinado, array[1..Meses] of var int: ventaMensual, int: mes) = if mes = 0 then 0 
                                                                  else sum(i in 1..mes, j in 1..NAceites)(refinado[i, j]) - sum(i in 1..mes)(ventaMensual[i]) endif;
                                                                                                                                        
% Como maximo refinamos la cantidad disponible de cada aceite.
constraint forall(i in 1..Meses, j in 1..NAceites)(refinado[i, j] <= (compras[i, j] + restanteMes(compras, refinado, i - 1, j)));

% Como máximo se refinan MAXV toneladas de acites vegetales mensualmente y MAXN toneladas de aceites no vegetales.
constraint forall(i in 1..Meses)(sum(j in 1..NAceitesVegetales)(refinado[i, j]) <= MAXV /\ sum(j in NAceitesVegetales + 1..NAceites)(refinado[i, j]) <= MAXN);

% Como máximo se almacenan MCAP tonaladas de cada aceite.
constraint forall(i in 1..Meses, j in 1..NAceites)((compras[i, j] + restanteMes(compras, refinado, i - 1, j)) <= MCAP);

% Al final de los meses deben quedar en los almacenes la cantidad exacta de cada aceite.
constraint forall(i in 1..NAceites)(restanteMes(compras, refinado, Meses, i) = RestanteFinal[i]);

% La dureza final de nuestro producto está entre MinD y MaxD.
constraint forall(i in 1..Meses)(sum(j in 1..NAceites)(refinado[i, j] * Durezas[j]) <= MaxD * sum(j in 1..NAceites)(refinado[i, j]) /\ sum(j in 1..NAceites)(refinado[i, j] * Durezas[j]) >= MinD * sum(j in 1..NAceites)(refinado[i, j]));

% Beneficio (suponemos el almacenaje de julio no cuesta dinero).
constraint beneficio = sum(i in 1..Meses)(ventaMensual[i] * PreciosMensual[i]) - sum(i in 1..Meses, j in 1..NAceites)(compras[i, j] * Precios[i, j]) - sum(i in 1..Meses, j in 1..NAceites)(compras[i, j] + restanteMes(compras, refinado, i - 1, j)) * CA - sum(i in 1..Meses)(restanteMesRefinado(refinado, ventaMensual, i - 1)) * CAR;

% No usamos más de K aceites mensualmente.
constraint forall(i in 1..Meses)(sum(j in 1..NAceites)(bool2int(refinado[i, j] > 0)) <= K);

% Si un aceite es usado, debe usarse más de T toneladas.
constraint forall(i in 1..Meses, j in 1..NAceites)(refinado[i, j] > 0 -> refinado[i, j] >= T);

% Cumplimos las restricciones de uso de aceites.
constraint forall(i in 1..Meses, j in 1..NAceites, k in 1..NAceites)(refinado[i, j] > 0 /\ AceitesAUsar[j, k] = 1 -> refinado[i, k] > 0);

% No puedo vender a final de mes más de lo que tengo refinado.
constraint forall(i in 1..Meses)(ventaMensual[i] <= sum(j in 1..NAceites)(refinado[i, j]) + restanteMesRefinado(refinado, ventaMensual, i - 1));

% El almacén de aceite refinado no puede superar MCAPR toneladas.
constraint forall(i in 1..Meses)(restanteMesRefinado(refinado, ventaMensual, i) <= MCAPR);

% Alcanzamos el beneficio mínimo.

%%%%%%%%%%%%%%%%%%    Satisfy    %%%%%%%%%%%%%%%%%%%
%solve satisfy;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%    Maximize    %%%%%%%%%%%%%%%%%%
solve maximize beneficio;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%    Output    %%%%%%%%%%%%%%%%%%%%
output ["Beneficio\n\(beneficio)"] ++ ["\n\nTabla de compras\n"] ++ 
       [ "\(compras[i,j])" ++ if j == NAceites then "\n" else " " endif | i in 1..Meses, j in 1..NAceites] ++ ["\nTabla de refinado\n"] ++ 
       [ "\(refinado[i,j])" ++ if j == NAceites then "\n" else " " endif | i in 1..Meses, j in 1..NAceites] ++ ["\nLista de ventas\n"] ++ 
       [ "\(ventaMensual[i])\n" | i in 1..Meses] ++ ["\nTabla de restantes\n"] ++ 
       [ "\(restanteMes(compras, refinado, i,j))" ++ if j == NAceites then "\n" else " " endif | i in 1..Meses, j in 1..NAceites];
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%