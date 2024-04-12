%n objetos
int: n;
%presupuesto
int: p;
%1:precios 2:superficie
array [1..n,1..2] of int: matriz;

array [1..n] of var 0..1: compra;

constraint (sum(i in 1..n)(matriz[i, 1]*compra[i]))<=p;

var int: suma= sum(i in 1..n)(matriz[i, 2]*compra[i]);

solve maximize suma;
output ["Compra: \(compra) \n"];
output ["Area: \(suma)\n"];
output ["Precio: \(sum(i in 1..n)(matriz[i, 1]*compra[i])) \n"];