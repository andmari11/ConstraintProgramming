% Data file
int: altura = 10;
array[1..3] of int: capacidad = [3, 5, 3];

enum Color={azul, rojo, verde};

array[1..altura] of var Color: torre;



%no más de x de cada color (i color, j altrura de cada torre)
var int: contador_azul = sum(i in 1..altura)(bool2int(torre[i] == azul));
var int: contador_rojo = sum(i in 1..altura)(bool2int(torre[i] == rojo));
var int: contador_verde = sum(i in 1..altura)(bool2int(torre[i] == verde));

constraint contador_azul<=capacidad[1];
constraint contador_rojo<=capacidad[2];
constraint contador_verde<=capacidad[3];


%rojo al principio
constraint torre[1]==rojo;

%no verdes seguidos
constraint forall (i in 1..(altura-1)) (torre[i]!= verde \/ torre[i+1]!=verde);

%no mas verdes q azules
constraint forall(i in 2..altura) ( sum(j in 1..i)(bool2int(torre[i] == azul)) >= sum(j in 1..i)(bool2int(torre[i] == verde)));

%más rojas q verdes y azules juntas
constraint contador_rojo>=contador_verde+contador_azul;



solve satisfy;

output [ "SOL: \n" ];

output [ "\(torre)\n"];
