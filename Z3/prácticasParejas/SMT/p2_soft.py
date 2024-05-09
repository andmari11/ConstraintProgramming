#!/usr/bin/python3
from z3 import *
import sys


nVeg=2
nNoVeg=3
nAceites=nVeg+nNoVeg
nMeses=6

VALOR = int(input())

auxArray = input().split()
dureza=[]
for i in range(len(auxArray)):
    dureza.append(float(auxArray[i]))

precios=[]
for _ in range(nMeses):
    auxArray = input().split()
    fila = [int(valor) for valor in auxArray]
    precios.append(fila)

MAXV = int(input())
MAXN = int(input())
MCAP = int(input())


CA = int(input())

MinD = float(input())
MaxD = float(input())

MinB = int(input())

auxArray = input().split()
inicial=[]
for i in range(len(auxArray)):
    inicial.append(float(auxArray[i]))

PV = int(input())
K = int(input())
T = int(input())

def nAlmacen (i,j):
    return "almacen_"+str(i)+"_"+str(j)
def nCompra (i,j):
    return "compras_"+str(i)+"_"+str(j)
def nRefinado (i,j):
    return "refinado_"+str(i)+"_"+str(j)
def nBeneficio (i):
    return "beneficio_"+str(i)


def bool2int(b):
    return If(b, 1, 0)

def addexists(a):
    if len(a) == 0:
        return False
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return Or(x,addexists(a)) 

def addsum(a):
    if len(a) == 0:
        return 0
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return x + addsum(a) 
    
def Abs(x):
    return If(x >= 0, x, -x)

################################
# generamos un fichero smtlib2
################################

#s= SolverFor("QF_LIA")
s = Optimize()
#s = Solver()

#declaración de variables de la solución
compra=[]
refinado=[]
almacen=[]
beneficio=[]

for i in range(nMeses):
    fila_compra = []
    fila_refinado = []
    fila_almacen = []
    
    for j in range(nAceites):
        fila_compra.append(Int(nCompra(i, j)))
        fila_refinado.append(Int(nRefinado(i, j)))
        fila_almacen.append(Int(nAlmacen(i, j)))
    
    beneficio.append(Int(nBeneficio(i)))
    compra.append(fila_compra)
    refinado.append(fila_refinado)
    almacen.append(fila_almacen)

beneficioTotal=Sum(beneficio)
# fin declaración

#---------------SOFT CONSTRAINTS------------------------

#k aceites max utilizados
for m in range(nMeses):
    suma=[]
    for a in range(nAceites):
        suma.append(bool2int(refinado[m][a]>0))
    s.add_soft(addsum(suma)<=K,3,"k_aceites")

#T minimas al usar un aceite
for m in range(nMeses):
    for a in range(nAceites):
        s.add_soft(Implies(refinado[m][a]>0,refinado[m][a]>T),2,"T_Min")

#si usamos el aceite ANV 1 o el aceite ANV 2 en un cierto mes, entonces VEG 2 tambi´en debe ser usado ese mes. 
for m in range(nMeses):
    s.add_soft(Implies(Or(refinado[m][nVeg]>0,refinado[m][nVeg+1]>0), refinado[m][2]>0),2,"Mezcla_Def")


#---------------CONSTRAINTS------------------------

#limitamos las variables
for i in range(nMeses):
    for j in range(nAceites):
        s.add(And(compra[i][j]>=0,compra[i][j]<=MCAP))
        s.add(And(refinado[i][j]>=0,refinado[i][j]<=MCAP)) 
        s.add(And(almacen[i][j]>=0, almacen[i][j]<=MCAP))
    s.add(beneficio[i]>=0)


#restriccion de almacenamiento inicial
for a in range(nAceites):
    s.add(almacen[0][a]==inicial[a])

#restriccion de almacenamiento coherente
for m in range(1,nMeses):
    for a in range(nAceites):
        s.add(almacen[m-1][a]+compra[m-1][a]-refinado[m-1][a]==almacen[m][a])

#restriccion  de refinado maximo(MAXN/MAXV))
for m in range(nMeses):
    sumaV=[]
    sumaNV=[]

    for a in range(nVeg):
        sumaV.append(refinado[m][a])
    for a in range(nVeg,nAceites):
        sumaNV.append(refinado[m][a])

    s.add(addsum(sumaV)<=MAXV)
    s.add(addsum(sumaNV)<=MAXN)


#restriccion durezas
for m in range(nMeses):
    sumaMesDureza=[]
    sumaMesTotal=[]

    for a in range(nAceites):
        sumaMesDureza.append(refinado[m][a]*dureza[a])
        sumaMesTotal.append(refinado[m][a])

    durezaMes=addsum(sumaMesDureza)
    mesTotal=addsum(sumaMesTotal)
    s.add(Or(And(durezaMes>=MinD*mesTotal,durezaMes<=MaxD*mesTotal), Sum([refinado[m][a] for a in range(nVeg, nAceites)]) == 0 ))

#restriccion cambio de PV en almacen
for a in range(nAceites):
    
    s.add(Abs(inicial[a]-(compra[nMeses-1][a]+almacen[nMeses-1][a]-refinado[nMeses-1][a]))<=PV*inicial[a]/100)


#beneficios
for m in range(nMeses): 
    sumaMes=[]
    for a in range(nAceites):
        sumaMes.append(refinado[m][a]*VALOR-compra[m][a]*precios[m][a]-almacen[m][a]*CA)
    s.add(addsum(sumaMes)==beneficio[m])

#no dos meses con perdidas
for m in range(1,nMeses):
    s.add(Or(beneficio[m]>=0,beneficio[m-1]>=0))

s.add(beneficioTotal>=MinB)

#---------------Solución------------------------

if s.check() == sat:
    print("\n\nCompra:")
    for fila in compra:
        print([s.model().eval(elemento) for elemento in fila])
    
    print("Refinado:")
    for fila in refinado:
        print([s.model().eval(elemento) for elemento in fila])
    
    print("Almacen:")
    for fila in almacen:
        print([s.model().eval(elemento) for elemento in fila])

    print("Beneficios:")
    print([s.model().eval(elemento) for elemento in beneficio])

    print("Beneficio Total =", (s.model().eval(beneficioTotal)))

else:
    print("unsat")

    

exit(0)





