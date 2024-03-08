int: T;%trabajadores
int: D;%dias laborables
int: A;%afines minimos

set of 1..T: R;

%trabajadores por turno
int:N1;
int:N2;
int:N3;

%max mins
int:MaxDT;
int:MaxDL;
int:MinDT;

array [1..T, 1..T] of bool: afines;
%2. Un trabajador solo puede estar en un turno cada día.
array [1..D, 1..T] of var 0..3: turnos;



%1. Cada turno tiene el número de trabajadores (“N1”, “N2” o “N3”) que le corresponde.
constraint forall(d in 1..D)(sum(t in 1..T)(turnos[d,t]=1)=N1);
constraint forall(d in 1..D)(sum(t in 1..T)(turnos[d,t]=2)=N2);
constraint forall(d in 1..D)(sum(t in 1..T)(turnos[d,t]=3)=N3);

%3. Dado un número “MaxDT”, garantizar que nadie trabaja “MaxDT” días consecutivos.
constraint forall(t in 1..T)(forall(d in 1..D-MaxDT)(sum(m in 0..MaxDT)(turnos[d+m,t]!=0)<=MaxDT));

%6. Si un trabajador hace el último turno de un día entonces no puede tener el primero del día siguiente.
constraint forall(t in 1..T)(forall(d in 1..D-1)(turnos[d,t]=3 -> turnos[d+1,t]!=1));

%7. Si un trabajador hace el último turno dos días seguidos entonces tiene que librar el día siguiente
constraint forall(t in 1..T)(forall(d in 1..D-2)((turnos[d,t]=3 /\ turnos[d+1,t]=3) -> turnos[d+2,t]=0));

%8. Dada una serie de parejas de trabajadores afines, cada trabajador de un turno tiene que estar con al menos A trabajadores afines en ese turno.

constraint forall(d in 1..D)(forall(i in 1..3)
          (forall(t1 in 1..T where (turnos[d,t1]=i))
          (sum (t2 in 1..T  where (turnos[d,t2]=i))(afines[t1,t2])>= A)));


%9. Sea “R” el conjunto de trabajadores  que tienen la categoría de encargados. En cada turno debe haber al menos un responsable.
constraint forall(d in 1..D)
          (forall(i in 1..3)
          (sum(t in R)(turnos[d, t]=i)>0));


%-------------------------OPTIMIZACION----------------------------

array [1..D, 1..T] of bool: vacaciones;

%4. Dado un número “MaxDL”, garantizar que nadie tiene “MaxDL” días libres consecutivos.
constraint forall(t in 1..T)(forall(d in 1..D-MaxDL)(sum(m in 0..MaxDL)(turnos[d+m,t]=0 /\ not vacaciones[d+m,t])<=MaxDL));

%5. Dado un número “MinDT”, garantizar que todos trabajan como mínimo “MinDT” en los “D” días.
constraint forall(t in 1..T)(sum(d in 1..D)(turnos[d,t]!=0 \/ vacaciones[d,t])>=MinDT);

% Optimización1: Minimizar el número de veces que hacemos trabajar a alguien cuandono quiere
solve minimize (sum(t in 1..T, d in 1..D)(turnos[d,t]!=0 /\ vacaciones[d,t]));