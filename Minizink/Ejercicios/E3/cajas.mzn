int :maxX;
int :maxY;

int :nPiezas;
array [1..nPiezas, 1..2] of int: piezas;

array [1..nPiezas, 1..2] of var int: sol;

array [1..nPiezas] of var bool: rotacion;

%dentro del tablero
constraint forall (i in 1..nPiezas)(

  sol[i, 1]<=maxX  /\ sol[i, 1]>=0 /\ sol[i, 2]<=maxY  /\ sol[i, 2]>=0
 
);


%q no sobresalgan
constraint forall (i in 1..nPiezas)(

       if rotacion[i]=false then
             (sol[i, 1]+ piezas[i, 1]<=maxX  /\ sol[i, 2]+ piezas[i, 2]<=maxY)
       else
             (sol[i, 2]+ piezas[i, 2]<=maxX  /\ sol[i, 1]+ piezas[i, 1]<=maxY)

       endif
);

%q no se monten;
% constraint forall (i,j in 1..nPiezas)(sol[i, 1] + piezas[i, 1] <= sol[j, 1] \/
%                                       sol[j, 1] + piezas[j, 1] <= sol[i, 1] \/
%                                       sol[i, 2] + piezas[i, 2] <= sol[j, 2] \/
%                                       sol[j, 2] + piezas[j, 2] <= sol[i, 2] \/
%                                       i=j);
                                      
constraint forall (i in 1..maxX-1, j in 1..maxY-1) (
   sum (k in 1..nPiezas) (
    
    
       if rotacion[i]=false then
    
                ((sol[k, 1] <= i /\ piezas[k, 1] + sol[k, 1] > i) /\
                (sol[k, 2] <= j /\ piezas[k, 2] + sol[k, 2] > j))
                
       else
       
                ((sol[k, 2] <= i /\ piezas[k, 2] + sol[k, 2] > i) /\
                (sol[k, 1] <= j /\ piezas[k, 1] + sol[k, 1] > j))
       endif
       )=1
);
                     
solve satisfy;



