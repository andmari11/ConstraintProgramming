%Datos del problema
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


array[1..CA] of float: dureza;
array[1..6, 1..CA] of int: precios; %Tabla de precios de compra de aceite por mes

array[1..5] of int: inicial; %Toneladas iniciales que tenemos
%No se pueden vender más de MAXV/MAXN por mes