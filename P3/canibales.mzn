int: nSalvajes=3;
int: nMisioneros=3;

int: nViajes=10;

%orilla salvajes, misioneros
array[1..nViajes, 1..2] of var int:orilla1;

%orilla salvajes, misioneros
array[1..nViajes, 1..2] of var int:orilla2;

%no hay m/s de más
constraint forall(i in 1..nViajes)(orilla1[i,1]+orilla2[i,1]=nSalvajes /\ orilla1[i,1]>=0 /\ orilla2[i,1]>=0);
constraint forall(i in 1..nViajes)(orilla1[i,2]+orilla2[i,2]=nMisioneros /\ orilla1[i,2]>=0 /\ orilla2[i,2]>=0);

%no hay mas canibales q misioneros
constraint forall(i in 1..nViajes)(orilla1[i,1]<=orilla1[i,2] /\ orilla2[i,1]<=orilla2[i,2]);

%acaba y empieza bn
constraint orilla1[1,1]=3 /\ orilla1[1,2]=3;
constraint (orilla2[nViajes,1]=3) /\ (orilla2[nViajes,2]=3);





solve satisfy;
