#!/usr/bin/python3
from z3 import *
import sys

# longitud : longitud de las luces
# nColores : colores disponibles
# consumo  : consumo max

longitud = int(input())
nColores = int(input())
consumoMax = int(input())

coloresInput=input().split()
colores=[]

for i in range(nColores):
    colores.append(int(coloresInput))

def addsum(a):
    if len(a) == 0:
        return 0
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return x + addsum(a) 
    
################################
# generamos un fichero smtlib2
################################

s = SolverFor("QF_LIA")
# s = Solver()

#declaración de variables de la solución
sol = []
for i in range(longitud):
    sol.append(Int(i))
# fin declaración

for i in range(longitud): 
    s.add(0 <= sol[i])
    s.add(sol[i] <= nColores)

