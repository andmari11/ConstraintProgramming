int: A;
int: P;
int: H;
int: CA;
int: CP;
int: CH;
int: N;
int: E;

%limitamos el número de abuelos, padres e hijos 
var 1..A:a;
var 1..P:p;
var 1..H:h;

%la suma de padres, hijos y abuelos debe ser N
constraint a + p + h = N;

%el coste total debe ser exactamente E
constraint a*CA + p*CP + h*CH = E;