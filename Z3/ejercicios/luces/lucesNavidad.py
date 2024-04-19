#!/usr/bin/python3
from z3 import *
import sys

# longitud : longitud de las luces
# nColores : colores disponibles
# consumo  : consumo max

inputParam=input().split()
longitud = int(inputParam[0])
nColores = int(inputParam[1])
consumoMax = int(inputParam[2])

inputParam=input().split()
colores=[]

for i in range(nColores):
    colores.append(int(inputParam[i]))


def nluz (i):
    return "luz_"+str(i)

def costluz (i):
    return "cluz"+str(i)


def addsum(a):
    if len(a) == 0:
        return 0
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return x + addsum(a) 

def bool2int(b):
    return If(b, 1, 0)



################################
# generamos un fichero smtlib2
################################

s = SolverFor("QF_LIA")
# s = Solver()

#declaración de variables de la solución
sol = []
coste = []

for i in range(longitud):
    sol.append(Int(nluz(i)))
    coste.append(Int(costluz(i)))
# fin declaración


for i in range(longitud):
    for j in range(nColores):
        s.add(Implies(sol[i]==j, coste[i]==colores[j]))


#sólo se utilizan los colores definidos
for i in range(longitud): 
    s.add(0 <= sol[i])
    s.add(sol[i] < nColores)

#no dos luces seguidas del mismo color
for i in range(1,longitud): 
    l1=sol[i-1]
    l2=sol[i]
    s.add(Not(l1==l2))

# la suma de las luces en cualquier punto
#de un color no supere en mas de una unidad la suma de las luces de
#todos los demas colores

# for color in range(nColores):
#     sumaColor=0
#     sumaOthers=0
#     for i in range(longitud): 
#         if color==sol[i]:
#             sumaColor+=1
#         else:
#             sumaOthers+=1
#         s.add(Or(Not(sumaOthers>=sumaColor+1),Not(sumaColor>=sumaOthers+1)))

for color in range(nColores):
    sumaColor=[]
    sumaOthers=[]
    for i in range(longitud): 
        sumaColor.append(bool2int(color==sol[i]))
        sumaOthers.append(bool2int(color!=sol[i]))
        s.add(Or(Not(addsum(sumaOthers)>=addsum(sumaColor)+1), Not(addsum(sumaColor)>=addsum(sumaOthers)+1)))

##consumo

suma=0
for i in range(longitud): 
    suma+=coste[i]
s.add(suma<=consumoMax)



print(s.check())
if s.check() == z3.sat:
    print("sol:")
    for i in reversed(range(longitud)):
        print(s.model().eval(sol[i]),  end=' ')
    print()
    print("coste:")
    for i in reversed(range(longitud)):
        print(s.model().eval(coste[i]),  end=' ')
    print()

exit(0)
