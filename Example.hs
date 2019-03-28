module Main where

import Syntax
import Semantics


-- Funciones 
sumaM a b = a + b
restaM a b = a - b
prodM a b = a * b
expM a b = a^b

-- Predicados
prirel a b = gcd a b == 1

-- Interpretacion de simbolos de funcion
iF :: IntF Int
iF f l = case f of
    "s" -> sumaM (l!!0) (l!!1)
    "r" -> restaM (l!!0) (l!!1)
    "p" -> prodM (l!!0) (l!!1)
    "exp" -> expM (l!!0) (l!!1)
    _ -> read f :: Int

-- Interpretacion de simbolos de predicado
iP :: IntR Int
iP p l = case p of
    "Prirel" -> prirel (l!!0) (l!!1)
    "Par" -> mod (l!!0) 2 == 0

-- Estados de las variables
est = id :: Int -> Int

main = do
    putStrLn "PUNTOS EXTRA"
    putStrLn "Alfa-equivalencia:"
    let phi = All 1 (Imp (Neg (Eq (V 1) (F "0" []))) (Ex 2 (Eq (F "p" [V 1, V 2]) (F "1" []))))
    let psi = All 3 (Imp (Neg (Eq (V 3) (F "0" []))) (Ex 1 (Eq (F "p" [V 3, V 1]) (F "1" []))))
    print $ phi
    print $ psi
    print $ vAlfaEq phi psi
    putStrLn "\nrenVL:"
    let psi = Conj (Pr "Par" [V 1]) phi
    print $ psi
    print $ renVL psi 
    putStrLn "\nRenVLconj:"
    let l = [1]
    print $ psi
    print $ l
    print $ renVLconj psi l
    putStrLn "\napSubF2:"
    let sus = [(1,V 3)]
    print $ psi
    print $ sus
    print $ apSubF2 psi sus
    putStrLn "\nEJEMPLOS"
    putStrLn "Universo M: Numeros Naturales"
    putStrLn "Funciones: suma(s), resta(r), producto(p), exp (p), constantes"
    putStrLn "Predicados: Primos relativos (Prirel), Ser par (Par)"
    putStrLn "Estados: Identidad\n"
    let u = [0..]
    let phi1 = Ex 1 (Conj (Eq (F "p" [V 1,F "4" []]) (F "12" [])) (Eq (F "p" [F "4" [],V 1]) (F "12" [])))
    putStrLn "Esta formula no cicla el programa, ya que si existe un numero que multiplicado por 4 da 12"
    putStrLn "y al ser la implemntacion del Existe un OR, por corto circuito detendra la ejecucion cuando lo encuentre"
    print $ phi1
    print $ iForm (u, iF, iP) est phi1
    let phi2 = All 1 (Imp (Neg (Eq (V 1) (F "0" []))) (Pr "Prirel" [V 1,F "13" [] ]))
    putStrLn "Esta formula no cicla el programa, ya que hay un numero diferente de cero que no es primo relativo con 13"
    putStrLn "y al ser la implemntacion del Para todo un AND, por corto circuito detendra la ejecucion cuando lo encuentre"
    print $ phi2
    print $ iForm (u, iF, iP) est phi2
    let phi3 = All 1 (Disy (Pr "Par" [V 1]) (Neg (Pr "Par" [V 1])))
    putStrLn "Esta formula cicla el programa, ya que todos los numeros son pares o impares"
    putStrLn "y al ser la implemntacion del Para todo un AND, tendra que evaluar para todos los naturales a menos que encuentre"
    putStrLn "uno que no lo cumpla, y al no haberlo y ser infinitos los naturales, jamas se detendra"
    print $ phi3
    print $ iForm (u, iF, iP) est phi3