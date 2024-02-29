int: nSalvajes=3;

int: nMisioneros=3;

int: nViajes=12;


%estado final
var 1..nViajes: estadoFinal;

%orilla salvajes, misioneros
array[1..nViajes, 1..2] of var 0..3:orilla1;

%orilla salvajes, misioneros
array[1..nViajes, 1..2] of var 0..3:orilla2;



%historial de movimientos
array[2..nViajes,1..2] of var -3..3:movimientos;



%no hay m/s de más

constraint forall(i in 1..nViajes)(orilla1[i,1]+orilla2[i,1]=nSalvajes /\ orilla1[i,1]>=0 /\ orilla2[i,1]>=0);

constraint forall(i in 1..nViajes)(orilla1[i,2]+orilla2[i,2]=nMisioneros /\ orilla1[i,2]>=0 /\ orilla2[i,2]>=0);



%no hay mas canibales q misioneros o hay 0 misioneros

constraint forall(i in 1..nViajes)((orilla1[i,1]<=orilla1[i,2] \/ orilla1[i,2]=0) /\ (orilla2[i,1]<=orilla2[i,2] \/ orilla2[i,2]=0) );



%acaba y empieza bn

constraint orilla1[1,1]=3 /\ orilla1[1,2]=3;

constraint (orilla2[estadoFinal,1]=3) /\ (orilla2[estadoFinal,2]=3);





%movimientos y orillas encajan

constraint forall(i in 2..nViajes)(orilla1[i-1,1]-orilla1[i,1]=movimientos[i,1] /\

orilla2[i-1,1]-orilla2[i,1]=-movimientos[i,1]);

constraint forall(i in 2..nViajes)(orilla1[i-1,2]-orilla1[i,2]=movimientos[i,2] /\

orilla2[i-1,2]-orilla2[i,2]=-movimientos[i,2]);



%max dos viajeros en barca

constraint forall(i in 2..nViajes)(abs(movimientos[i,1]+movimientos[i,2])>0 /\

abs(movimientos[i,1]+movimientos[i,2])<=2

% /\

% abs(movimientos[i,1])<=2/\

% abs(movimientos[i,2])<=2

);

%viaje de ida

constraint forall(i in 2..nViajes where i mod 2=0)((movimientos[i,1])>=0 /\

(movimientos[i,2])>=0);

%viaje de vuelta

constraint forall(i in 2..nViajes where i mod 2=1)((movimientos[i,1])<=0 /\

(movimientos[i,2])<=0);

solve minimize estadoFinal;