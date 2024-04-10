int: T;
int: D;
int: P;
int: Lim;

array[1..T] of 1..D: duracion;
array[1..T] of set of 1..T: dep;

%guardamos cuando se empieza cada tarea
array[1..T] of var 1..Lim: sol;

%comprobamos cuantas tareas coinciden, mirando cada hora (l) y contando el número de veces que l está entre el comienzo y fin de una tarea
constraint forall (l in 1..Lim)(count(t in 1..T)( l>=sol[t] /\ l<=sol[t] + duracion[t]-1 ) <= P); 

%comprobamos dependencias, mirando que el comienzo de t1 sea después del fin de la tarea de la que depende t2
constraint forall(t1 in 1..T)(forall(t2 in dep[t1])( sol[t1] > (sol[t2] + duracion[t2]-1) ));

%buscamos una solución en la que la tarea que acabe más tarde, sea lo más pronto posible
solve minimize (max(t in 1..T)( sol[t] + duracion[t]-1 ));