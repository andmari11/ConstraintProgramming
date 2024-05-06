#!/usr/bin/python3

import sys
sys.setrecursionlimit(100000)
# altura : altura de la torre
# disp : piezas disponibles
# Colores: Azul = 0, Rojo = 1 , Verde = 2;

NAceitesVegetales = int(input())
NAceitesNoVegetales = int(input())
NAceites = NAceitesVegetales + NAceitesNoVegetales
meses = int(input())
K = int(input())
T = int(input())

precios = []
for i in range(meses):
    precios1 = input().split()
    precios.append([])
    for j in range(len(precios1)):
        precios[i].append(int(precios1[j]))

preciosMensual1 = input().split()
preciosMensual = []
for i in range(len(preciosMensual1)):
    preciosMensual.append(int(preciosMensual1[i]))

MAXV = int(input())
MAXN = int(input())
MCAP = int(input())
MCAPR = int(input())
CA = int(input())
CAR = int(input())
MinD = int(float(input())*10)
MaxD = int(float(input())*10)
durezas1 = input().split()
durezas = []
for i in range(len(durezas1)):
    durezas.append(int(float(durezas1[i])*10))

restanteFinal1 = input().split()
restanteFinal = []
for i in range(len(restanteFinal1)):
    restanteFinal.append(int(restanteFinal1[i]))

aceitesAUsar = []
for i in range(NAceites):
    aceitesAUsar1 = input().split()
    aceitesAUsar.append([])
    for j in range(len(aceitesAUsar1)):
        aceitesAUsar[i].append(bool(aceitesAUsar1[j] == "true"))
MinB = int(input())

def compras(i, j):
    return "compras_"+str(i)+"_"+str(j)

def refinado(i, j):
    return "refinado_"+str(i)+"_"+str(j)

def ventas(i):
    return "venta_"+str(i)

def beneficio():
    return "beneficio"

def setlogic(l):
    return "(set-logic "+ l +")"

def intvar(v):
    return "(declare-fun "+v+" () Int)"

def bool2int(b):
    return "(ite "+b+" 1 0 )"

def addand(a1,a2):
    return "(and "+a1+" "+a2+" )"
def addor(a1,a2):
    return "(or "+a1+" "+a2+" )"
def addnot(a):
    return "(not "+a+" )"
def addimplies(a1,a2):
    return "(=> "+a1+" "+a2+" )"

def addexists(a):
    if len(a) == 0:
        return "false"
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return "(or " + x + " " + addexists(a) + " )" 

def addeq(a1,a2):
    return "(= "+a1+" "+a2+" )" 
def addle(a1,a2):
    return "(<= "+a1+" "+a2+" )" 
def addge(a1,a2):
    return "(>= "+a1+" "+a2+" )" 
def addlt(a1,a2):
    return "(< "+a1+" "+a2+" )"
def addgt(a1,a2):
    return "(> "+a1+" "+a2+" )" 

def addplus(a1,a2):
    return "(+ "+a1+" "+a2+" )"

def addless(a1, a2):
    return "(- "+a1+" "+a2+" )"

def addmul(a1, a2):
    return "(* "+a1+" "+a2+" )"

def addassert(a):
    return "(assert "+a+" )"

def addassertsoft(a):
    return "(assert-soft "+a+" )"

def addmaximize(a):
    return "(maximize "+a+" )"

def addsum(a):
    if len(a) == 0:
        return "0"
    elif len(a) == 1:
        return a[0]
    else :
        x = a.pop()
        return "(+ " + x + " " + addsum(a) + " )" 

def checksat():
    print("(check-sat)")
def getmodel():
    print("(get-model)")
def getvalue(l):
    print("(get-value " + l + " )")

################################
# generamos un fichero smtlib2
################################

print("(set-option :produce-models true)")
print(setlogic("QF_LIA"))

#declaración de variables de la solución
print(intvar(beneficio()))
for i in range(meses):
    print(intvar(ventas(i)))
    for j in range(NAceites):
        print(intvar(compras(i, j)))
        print(intvar(refinado(i, j)))
# fin declaración

#No se puede comprar, refinar ni vender negativo.
for i in range(meses):
    print(addassert(addge(ventas(i), str(0))))
    for j in range(NAceites):
        print(addassert(addand(addge(compras(i,j), str(0)), addge(refinado(i,j), str(0)))))

#Como máximo refinamos la cantidad disponible de cada aceite.
#constraint forall(i in 0..meses-1, j in 0..NAceites-1)(refinado[i, j] <= (compras[i, j] + if i = 0 then 0 else sum(k in 0..i-1)(compras[k, j] - refinado[k, j]) endif));
for i in range(meses):
    for j in range(NAceites):
        sumA = []
        sumA.append(compras(i,j))
        for k in range(i):
            sumA.append(addless(compras(k,j), refinado(k, j)))
        print(addassert(addle(refinado(i, j), addsum(sumA))))

#Como máximo se refinan MAXV toneladas de acites vegetales mensualmente y MAXN toneladas de aceites no vegetales.
#constraint forall(i in 0..meses-1)(sum(j in 0..NAceitesVegetales-1)(refinado[i, j]) <= MAXV /\ sum(j in NAceitesVegetales..NAceites - 1)(refinado[i, j]) <= MAXN);
for i in range(meses):
    sumRV = []
    sumRNV = []
    for j in range(NAceitesVegetales):
        sumRV.append(refinado(i,j))
    for j in range(NAceitesVegetales, NAceites):
        sumRNV.append(refinado(i,j))
    c1 = addle(addsum(sumRV), str(MAXV))
    c2 = addle(addsum(sumRNV), str(MAXN))
    print(addassert(addand(c1, c2)))

#Como máximo se almacenan MCAP tonaladas de cada aceite.
#constraint forall(i in 0..meses-1, j in 0..NAceites-1)((compras[i, j] + if i = 0 then 0 else sum(k in 0..i-1)(compras[k, j] - refinado[k, j]) endif) <= MCAP);
for i in range(meses):
    for j in range(NAceites):
        sumA = []
        sumA.append(compras(i,j))
        for k in range(i):
            sumA.append(addless(compras(k,j), refinado(k, j)))
        print(addassert(addle(addsum(sumA), str(MCAP))))

#Al final de los meses deben quedar en los almacenes la cantidad exacta de cada aceite.
#constraint forall(i in 1..NAceites)(sum(k in 0..meses-1)(compras[k, i] - refinado[k, i]) = restanteFinal[i]);
for i in range(NAceites):
    sumA = []
    for k in range(meses):
        sumA.append(addless(compras(k,i), refinado(k, i)))
    print(addassert(addeq(addsum(sumA), str(restanteFinal[i]))))

#La dureza final de nuestro producto está entre MinD y MaxD.
#constraint forall(i in 1..meses)((sum(j in 1..NAceites)(refinado[i, j] * durezas[j]) <= (MaxD * sum(j in 1..NAceites)(refinado[i, j]))) 
#                                 /\ (sum(j in 1..NAceites)(refinado[i, j] * durezas[j]) >= (MinD * sum(j in 1..NAceites)(refinado[i, j]))));
for i in range(meses):
    sumA = []
    sumB = []
    for j in range(NAceites):
        sumA.append(addmul(refinado(i, j), str(durezas[j])))
        sumB.append(refinado(i, j))
    sumAAux = addsum(sumA)
    sumBAux = addsum(sumB)
    c1 = addle(sumAAux, addmul(str(MaxD), sumBAux))
    c2 = addge(sumAAux, addmul(str(MinD), sumBAux))
    print(addassert(addand(c1, c2)))







#beneficio = sum(i in 1..meses)(ventaMensual[i] * preciosMensual[i]) 
#            - sum(i in 1..meses, j in 1..NAceites)(compras[i, j] * precios[i, j]) 
#            - sum(i in 1..meses, j in 1..NAceites)(compras[i, j] + restanteMes(compras, refinado, i - 1, j)) * CA 
#           - sum(i in 1..meses)(restanteMesRefinado(refinado, ventaMensual, i - 1)) * CAR;

######################################################################################
sumVentas = []
sumCompras = []
sumCostes = []
sumCostesR = []
sumVT = []
sumRT = []

for i in range(meses):
    sumVentas.append(addmul(ventas(i), str(preciosMensual[i])))

for i in range(meses):
    for j in range(NAceites):
        sumCompras.append(addmul(compras(i, j), str(precios[i][j])))

for i in range(meses):
    for j in range(NAceites):
        sumCostes.append(compras(i, j))
        for k in range(i):
            sumCostes.append(addless(compras(k,j), refinado(k, j)))

sumCostesR = []
for i in range(meses):
    sumRT = []
    sumVT = []
    for j in range(i):
        sumVT.append(ventas(j))
        for k in range(NAceites): 
            sumRT.append(refinado(j, k))
    sumCostesR.append(addless(addsum(sumRT), addsum(sumVT)))
print(addassert(addeq(beneficio(), addless(addsum(sumVentas), addplus(addsum(sumCompras), addplus(addmul(addsum(sumCostes), str(CA)), addmul(addsum(sumCostesR), str(CAR))))))))
###########################################################################################




#Beneficio minimo
print(addassert(addge(beneficio(), str(MinB))))

#No usamos más de K aceites mensualmente.
#constraint forall(i in 1..meses)(sum(j in 1..NAceites)(bool2int(refinado[i, j] > 0)) <= K);
for i in range(meses):
    sumUsados = []
    for j in range(NAceites):
        sumUsados.append(bool2int(addgt(refinado(i,j), str(0))))
    print(addassertsoft(addle(addsum(sumUsados), str(K))))


#Si un aceite es usado, debe usarse más de T toneladas.
#constraint forall(i in 1..meses, j in 1..NAceites)(refinado[i, j] > 0 -> refinado[i, j] >= T);
for i in range(meses):
    for j in range(NAceites):
        print(addassertsoft(addimplies(addgt(refinado(i,j), str(0)), addge(refinado(i, j), str(T)))))

#Deben cumplirse las restricciones de uso de aceites.
#constraint forall(i in 1..meses, j in 1..NAceites, k in 1..NAceites)(refinado[i, j] > 0 /\ aceitesAUsar[j, k] = 1 -> refinado[i, k] > 0);
for i in range(meses):
    for j in range(NAceites):
        for k in range(NAceites):
            if(aceitesAUsar[j][k]):
                print(addassertsoft(addimplies(addgt(refinado(i, j), str(0)), addgt(refinado(i, k), str(0)))))






##############################################################################

#No puedo vender a final de mes más de lo que tengo refinado.
#constraint forall(i in 1..meses)(ventaMensual[i] <= sum(j in 1..NAceites)(refinado[i, j]) + restanteMesRefinado(refinado, ventaMensual, i - 1));
for i in range(meses):
    sumR = []
    sumRT = []
    sumVT = []
    for l in range(NAceites):
        sumR.append(refinado(i, l))
    for j in range(i):
        sumVT.append(ventas(j))
        for k in range(NAceites): 
            sumRT.append(refinado(j, k))
    print(addassert(addle(ventas(i), addplus(addsum(sumR), addless(addsum(sumRT), addsum(sumVT))))))

#El almacén de aceite refinado no puede superar MCAPR toneladas.
#constraint forall(i in 1..meses)(restanteMesRefinado(refinado, ventaMensual, i) <= MCAPR);
for i in range(meses):
    sumRT = []
    sumVT = []
    for j in range(i):
        sumVT.append(ventas(j))
        for k in range(NAceites): 
            sumRT.append(refinado(j, k))
    print(addassert(addle(addless(addsum(sumRT), addsum(sumVT)), str(MCAPR))))

########################################################################################################



#Optimizacion
print(addmaximize(beneficio()))

checksat()

#getmodel()
getvalue("("+beneficio()+")")
for i in range(meses):
    for j in range(NAceites):
        getvalue("("+compras(i, j)+")")
for i in range(meses):
    for j in range(NAceites):
        getvalue("("+refinado(i, j)+")")
for i in range(meses):
    getvalue("("+ventas(i)+")")
exit(0)