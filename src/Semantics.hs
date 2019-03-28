module Semantics where

import Syntax

-- Tipo de interpretacion de una funcion
-- Recibe el nombre de la funcion, la lista de argumentos y devuelve un elemento de M
type IntF a = Nombre -> [a] -> a
-- Tipo de interpretacion de un predicado
-- Recibe el nombre del predicado, la lista de argumentos y devuelve un booleano
type IntR a = Nombre -> [a] -> Bool
-- Tipo de estado
-- Recibe el indice de una variable y devuelve un elemento de M
type Estado a = Ind -> a

-- La estrcutura, que se compone del conjunto M, y la interpretacion de funciones y predicados
type Estructura a = ([a], IntF a, IntR a)

-- Recibe un estado, el indice de la variable a remplazar, y un elemento de M
-- Devuelve un nuevo estado, si el indice de la variable a evaluar es igual al del estado original
-- el estado devolvera el nuevo elemento de M, en caso contrario devolvera el mismo elemento que el estado original
actEst :: Estado a -> Ind -> a -> Estado a
-- e es una funcion
actEst e x n = ne 
    where ne y = if x == y then n else e y

-- Interpretacion de terminos
-- Recibe un estado de las variables, la interpretacion de una funcion y un termino
-- Devuelve un elmento de M (que depende del estado y la interpretacion de la funcion, si aplica)
iTerm :: Estado a -> IntF a -> Term -> a
iTerm e iF t = case t of
    V x -> e x
    F f lt -> iF f [iTerm e iF t | t <- lt]

-- Interpretacion de formulas
-- Recibe una estructura, un estado de las variables y una formula
-- Devuelve verdadero, si la formula es satisfacible con esa estructura y estado de las variables
-- Devuelve falso en caso contrario
iForm :: Eq a => Estructura a -> Estado a -> Form -> Bool
iForm str e phi = case phi of
    FalseF -> False
    TrueF -> True
    Pr p lt -> iR p (map (iTerm e iF) lt) where (_,iF, iR) = str
    Eq t1 t2 -> (iTerm e iF t1) == (iTerm e iF t2) where (_,iF,_) = str
    Neg p -> not (iForm str e p)
    Conj p q -> (iForm str e p) && (iForm str e q)
    Disy p q -> (iForm str e p) || (iForm str e q)
    Imp p q -> iForm str e (Disy (Neg p) q)
    Equiv p q -> iForm str e (Conj (Imp p q) (Imp q p))
    All x p -> and [(iForm str (actEst e x m) p)|m <-u] where (u,_,_) = str
    Ex x p -> or [(iForm str (actEst e x m) p)|m <-u] where (u,_,_) = str