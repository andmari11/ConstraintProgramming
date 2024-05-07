from z3 import *

# Datos del problema
nMeses = 6
nAceites = 5
K = 4
T = 30

VALOR = 150 # Valor por el que se vende el producto final por tonelada
dureza = [8.8, 6.1, 2.0, 4.2, 5.0]
precios = [[110, 120, 130, 110, 115],
           [130, 130, 110,  90, 115],
           [110, 140, 130, 100,  95],
           [120, 110, 120, 120, 125],
           [100, 120, 150, 110, 105],
           [ 90, 100, 140,  80, 135]]

MAXV = 200 # Máximo de toneladas de aceite vegetal a refinar por mes
MAXN = 250 # Máximo de toneladas de aceite no vegetal a refinar por mes

MCAP = 1000 # Capacidad de almacenamiento de la fábrica para cada tipo

CA = 5 # Costes de almacenamiento por tonelada y mes
# Aceites refinados no pueden ser almacenados
MinD = 3.0 # Mínima dureza
MaxD = 6.0 # Máxima dureza
MinB = 100000 # Beneficio mínimo que tenemos que conseguir
# No más de dos meses de pérdidas consecutivos

inicial = [500, 500, 500, 500, 500] #Aceites iniciales en el almacén
PV = 10 # No puede variar el almacenamiento del almacén desde el inicio hasta el fin más del PV%


#Declaración de variables solución
almacen = [ [ Int("almacen_{}_{}".format(m, a)) for a in range(0, nAceites) ] for m in range(0, nMeses) ]
compra = [ [ Int("compra_{}_{}".format(m, a)) for a in range(0, nAceites) ] for m in range(0, nMeses) ]
refinado = [ [ Int("refinado_{}_{}".format(m, a)) for a in range(0, nAceites) ] for m in range(0, nMeses) ]
beneficios = [ Int("beneficios_{}".format(m)) for m in range(0, nMeses) ]
durezas = [ Real("durezas_{}".format(m)) for m in range(0, nMeses) ]

# Restricciones de los rangos de las variables
s = SolverFor("QF_LIA")
for m in range(nMeses):
    for a in range(nAceites):
        s.add(almacen[m][a] >= 0, almacen[m][a] <= MCAP)
        s.add(compra[m][a] >= 0, compra[m][a] <= MCAP)
        s.add(refinado[m][a] >= 0, refinado[m][a] <= max(MAXN, MAXV))
    s.add(beneficios[m] >= -MinB, beneficios[m] <= MinB)
    s.add(durezas[m] >= -10, durezas[m] <= 10)


# constraint forall(a in 1..nAceites)(almacen[1,a] == inicial[a]);
for a in range(nAceites):
    s.add(almacen[0][a] == inicial[a])

# constraint forall(m in 2..nMeses,a in 1..nAceites)(almacen[m-1,a]+compra[m-1,a]-refinado[m-1,a]==almacen[m,a]);
for m in range(0, nMeses):
    for a in range(nAceites):
        s.add(almacen[m-1][a] + compra[m-1][a] - refinado[m-1][a] == almacen[m][a])

# constraint forall(m in 1..nMeses)(sum(a in 1..2)(refinado[m,a])=MAXV /\ sum(a in 3..nAceites)(refinado[m,a])=MAXN);
for m in range(nMeses):
    s.add(Sum([refinado[m][a] for a in range(2)]) <= MAXV)
    s.add(Sum([refinado[m][a] for a in range(2, nAceites)]) <= MAXN)

# constraint forall(m in 1..nMeses)(durezas[m]==(sum(v in 1..nAceites)(refinado[m,v]*dureza[v]) / sum(v in 1..nAceites)(refinado[m,v])));
for m in range(nMeses):
    s.add(durezas[m] == Sum([refinado[m][v]*dureza[v] for v in range(nAceites)]) / Sum([refinado[m][v] for v in range(nAceites)]))

# constraint forall(m in 1..nMeses)((durezas[m] >= MinD /\durezas[m] <= MaxD)\/ sum(a in 3..nAceites)(refinado[m,a])== 0 );
for m in range(1, nMeses):
    # durezas[m] >= MinD /\durezas[m] <= MaxD)
    durezaAceiteVegetal = And(durezas[m] >= MinD, durezas[m] <= MaxD)

    # sum(a in 3..nAceites)(refinado[m,a])== 0
    durezaFinal = Sum([refinado[m][a] for a in range(2, nAceites)]) == 0

    # Agregar la restricción al solucionador
    s.add(Or(durezaAceiteVegetal, durezaFinal))

# constraint forall(v in 1..nAceites)(abs(inicial[v]-(compra[nMeses,v]+almacen[nMeses,v]-refinado[nMeses,v]))/inicial[v]*100<=PV);
for v in range(0, nAceites):
    s.add(Abs(inicial[v] - (compra[nMeses - 1][v] + almacen[nMeses - 1][v] - refinado[nMeses - 1][v])) / inicial[v] * 100 <= PV)

# constraint forall(m in 2..nMeses)((beneficios[m]>= 0) \/ (beneficios[m-1]>= 0));
for m in range(1, nMeses):
    s.add(Or(beneficios[m] >= 0, beneficios[m - 1] >= 0))

# constraint forall (m in 1..nMeses)(sum(a in 1..nAceites)(refinado[m,a]*VALOR-compra[m,a]*precios[m,a]-almacen[m,a]*CA)==beneficios[m]);
for m in range(0, nMeses):
    s.add(Sum([refinado[m][a]*VALOR - compra[m][a]*precios[m][a] - almacen[m][a]*CA for a in range(0, nAceites)]) == beneficios[m])



if s.check() == sat:
    print("Compra:")
    for fila in compra:
        print([s.model().eval(elemento) for elemento in fila])
    
    print("Refinado:")
    for fila in refinado:
        print([s.model().eval(elemento) for elemento in fila])
    
    print("Almacen:")
    for fila in almacen:
        print([s.model().eval(elemento) for elemento in fila])

    print("Beneficios:")
    for i in range(nMeses):
        print(s.model().eval(beneficios[i]), end=" ")

else:
    print("unsat")

    