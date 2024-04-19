#!/usr/bin/python3
from z3 import *
import sys

# nAdornos : max de elementos a comprar
# presipuesto : presupuesto max a gastar
# superficies: superficies de nAdornos

inputParam=input().split()
nAdornos = int(inputParam[0])
presupuesto = int(inputParam[1])

superficies=[]
coste=[]

for i in range(nAdornos):
    inputParam=input().split()
    coste.append(int(inputParam[0]))
    superficies.append(int(inputParam[1]))


def nAdorno (i):
    return "Adorno_"+str(i)

def costAdorno (i):
    return "coste_"+str(i)

def superficieAdorno (i):
    return "superficie_"+str(i)

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


################################
# generamos un fichero smtlib2
################################

#s = SolverFor("QF_LIA")
# s = Solver()
s=Optimize()

#declaración de variables de la solución
sol = []
for i in range(nAdornos):
    sol.append(Int(nAdorno(i)))
    
# fin declaración

for i in range(nAdornos):
    s.add(Or(sol[i]==0, sol[i]==1))

fcoste = Function('fcoste', IntSort(), IntSort())
fsuperficie= Function('fsuperficie', IntSort(), IntSort())

for j in range(nAdornos):
    s.add(fcoste(j) == coste[j])
    s.add(fsuperficie(j)== superficies[j])

ct=[]
for i in range(nAdornos):
    ct.append(sol[i]*fcoste(sol[i]))
s.add(addsum(ct)<=presupuesto)

ct=[]
for i in range(nAdornos):
    ct.append(sol[i]*fsuperficie(sol[i]))

s.maximize(sum(ct))
print(s.check())

for i in reversed(range(nAdornos)):
    print(nAdorno(i),s.model().eval(sol[i]))

