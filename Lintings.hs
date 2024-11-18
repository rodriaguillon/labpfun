module Lintings where

import AST
import LintTypes


--------------------------------------------------------------------------------
-- AUXILIARES
--------------------------------------------------------------------------------

linteadoAux :: Expr -> (Expr, [LintSugg])
linteadoAux newExpr = case newExpr of
    Infix Add (Lit (LitInt _)) (Lit (LitInt _)) -> lintComputeConstant newExpr
    Infix Sub (Lit (LitInt _)) (Lit (LitInt _)) -> lintComputeConstant newExpr
    Infix Mult (Lit (LitInt _)) (Lit (LitInt _)) -> lintComputeConstant newExpr
    Infix Div (Lit (LitInt _)) (Lit (LitInt _)) -> lintComputeConstant newExpr
    _ -> (newExpr, [])

-- Función que obtiene las variables libres de una expresión
freeVariables :: Expr -> [Name]
freeVariables (Var x) = [x]  -- Una variable es libre por definición
freeVariables (Lit _) = []  -- Los literales no tienen variables libres
freeVariables (Infix _ e1 e2) = freeVariables e1 ++ freeVariables e2  -- Variables libres de ambos operandos
freeVariables (App e1 e2) = freeVariables e1 ++ freeVariables e2  -- Variables libres de ambos operandos
freeVariables (Lam x e) = filter (/= x) (freeVariables e)  -- Variables libres de la expresión, excluyendo 'x'
freeVariables (Case e1 e2 (x, y, e3)) = 
  freeVariables e1 ++ freeVariables e2 ++ filter (`notElem` [x, y]) (freeVariables e3)  -- Variables libres de las expresiones
freeVariables (If e1 e2 e3) = freeVariables e1 ++ freeVariables e2 ++ freeVariables e3  -- Variables libres de las tres expresiones


--------------------------------------------------------------------------------
-- LINTINGS
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
-- Computación de constantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Reduce expresiones aritméticas/booleanas
-- Construye sugerencias de la forma (LintCompCst e r)
lintComputeConstant :: Linting Expr
lintComputeConstant expr = case expr of
    -- Suma
    Infix Add (Lit (LitInt x)) (Lit (LitInt y)) ->
        let result = x + y
        in if result >= 0
            then (Lit (LitInt result), [LintCompCst expr (Lit (LitInt result))])
            else (expr, [])
    
    -- Resta
    Infix Sub (Lit (LitInt x)) (Lit (LitInt y)) ->
        let result = x - y
        in if result >= 0
            then (Lit (LitInt result), [LintCompCst expr (Lit (LitInt result))])
            else (expr, [])
    
    -- Multiplicacion
    Infix Mult (Lit (LitInt x)) (Lit (LitInt y)) ->
        let result = x * y
        in if result >= 0
            then (Lit (LitInt result), [LintCompCst expr (Lit (LitInt result))])
            else (expr, [])
    
    -- Division (evita divisiones por cero)
    Infix Div (Lit (LitInt x)) (Lit (LitInt y)) ->
        if y == 0
            then (expr, [])  -- No sugerir divisiones por cero
            else let result = x `div` y
                in if result >= 0
                    then (Lit (LitInt result), [LintCompCst expr (Lit (LitInt result))])
                    else (expr, [])

    -- Operador AND booleano
    Infix And (Lit (LitBool x)) (Lit (LitBool y)) ->
        let result = x && y
        in (Lit (LitBool result), [LintCompCst expr (Lit (LitBool result))])

    -- Operador OR booleano
    Infix Or (Lit (LitBool x)) (Lit (LitBool y)) ->
        let result = x || y
        in (Lit (LitBool result), [LintCompCst expr (Lit (LitBool result))])
        
    -- Casos recursivos para otras expresiones
    Infix op e1 e2 ->
        let (e1', suggs1) = lintComputeConstant e1
            (e2', suggs2) = lintComputeConstant e2
            (simplifiedExpr, suggsAux) = linteadoAux (Infix op e1' e2')
        in (simplifiedExpr,  suggs1 ++ suggs2 ++ suggsAux )
        
    App e1 e2 ->
        let (e1', suggs1) = lintComputeConstant e1
            (e2', suggs2) = lintComputeConstant e2
        in (App e1' e2', suggs1 ++ suggs2)
        
    Lam n e ->
        let (e', suggs) = lintComputeConstant e
        in (Lam n e', suggs)
        
    Case e1 e2 (n1, n2, e3) ->
        let (e1', suggs1) = lintComputeConstant e1
            (e2', suggs2) = lintComputeConstant e2
            (e3', suggs3) = lintComputeConstant e3
        in (Case e1' e2' (n1, n2, e3'), suggs1 ++ suggs2 ++ suggs3)
        
    If e1 e2 e3 ->
        let (e1', suggs1) = lintComputeConstant e1
            (e2', suggs2) = lintComputeConstant e2
            (e3', suggs3) = lintComputeConstant e3
        in (If e1' e2' e3', suggs1 ++ suggs2 ++ suggs3)
        
    -- Casos base que no necesitan transformación
    e -> (e, [])

--------------------------------------------------------------------------------
-- Eliminación de chequeos redundantes de booleanos
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Elimina chequeos de la forma e == True, True == e, e == False y False == e
-- Construye sugerencias de la forma (LintBool e r)
lintRedBool :: Linting Expr
lintRedBool expr = case expr of
    -- e == True -> e
    Infix Eq e (Lit (LitBool True)) -> 
        let (e', suggs) = lintRedBool e
            originalExpr = Infix Eq e' (Lit (LitBool True)) 
        in (e', suggs ++ [LintBool originalExpr e'])
    
    -- True == e -> e    
    Infix Eq (Lit (LitBool True)) e -> 
        let (e', suggs) = lintRedBool e
            originalExpr = Infix Eq (Lit (LitBool True)) e'
        in (e', suggs ++ [LintBool originalExpr e'])
        
    -- e == False -> NOT(e)
    Infix Eq e (Lit (LitBool False)) ->
        let (e', suggs) = lintRedBool e
            notExpr = App (Var "not") e'
            originalExpr = Infix Eq e' (Lit (LitBool False))
        in (notExpr, suggs ++ [LintBool originalExpr notExpr] )
        
    -- False == e -> NOT(e)
    Infix Eq (Lit (LitBool False)) e ->
        let (e', suggs) = lintRedBool e  
            notExpr = App (Var "not") e'  
            originalExpr = Infix Eq (Lit (LitBool False)) e' 
        in (notExpr, suggs ++ [LintBool originalExpr notExpr])
        
    -- Casos recursivos para otras expresiones
    Infix op e1 e2 ->
        let (e1', suggs1) = lintRedBool e1
            (e2', suggs2) = lintRedBool e2
        in (Infix op e1' e2', suggs1 ++ suggs2)
        
    App e1 e2 ->
        let (e1', suggs1) = lintRedBool e1
            (e2', suggs2) = lintRedBool e2
        in (App e1' e2', suggs1 ++ suggs2)
        
    Lam n e ->
        let (e', suggs) = lintRedBool e
        in (Lam n e', suggs)
        
    Case e1 e2 (n1, n2, e3) ->
        let (e1', suggs1) = lintRedBool e1
            (e2', suggs2) = lintRedBool e2
            (e3', suggs3) = lintRedBool e3
        in (Case e1' e2' (n1, n2, e3'), suggs1 ++ suggs2 ++ suggs3)
        
    If e1 e2 e3 ->
        let (e1', suggs1) = lintRedBool e1
            (e2', suggs2) = lintRedBool e2
            (e3', suggs3) = lintRedBool e3
        in (If e1' e2' e3', suggs1 ++ suggs2 ++ suggs3)
        
    -- Casos base que no necesitan transformación
    e -> (e, [])
    


--------------------------------------------------------------------------------
-- Eliminación de if redundantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Sustitución de if con literal en la condición por la rama correspondiente
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfCond :: Linting Expr
lintRedIfCond expr = case expr of
    -- Primero, simplificamos cualquier `if` en las subexpresiones
    If cond e1 e2 ->
        let (cond', suggsCond) = lintRedIfCond cond
            (e1', suggs1) = lintRedIfCond e1
            (e2', suggs2) = lintRedIfCond e2
            simplifiedExpr = If cond' e1' e2'
        in case simplifiedExpr of
            -- Caso if True -> solo queda e1
            If (Lit (LitBool True)) eThen _ ->
                (eThen, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf simplifiedExpr eThen])
            -- Caso if False -> solo queda e2
            If (Lit (LitBool False)) _ eElse ->
                (eElse, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf simplifiedExpr eElse])
            -- Caso if (x == False) then False else True -> not x
            If (Infix Eq x (Lit (LitBool False))) (Lit (LitBool False)) (Lit (LitBool True)) ->
                let notExpr = App (Var "not") x
                in (notExpr, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf simplifiedExpr notExpr])
            -- Caso if (x == True) then True else False -> x
            If (Infix Eq x (Lit (LitBool True))) (Lit (LitBool True)) (Lit (LitBool False)) ->
                (x, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf simplifiedExpr x])
            -- Caso if (x == True) then y else False -> x && y
            If (Infix Eq x (Lit (LitBool True))) y (Lit (LitBool False)) ->
                (Infix And x y, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf simplifiedExpr (Infix And x y)])
            -- Caso if c then x else False -> c && x
            If cond x (Lit (LitBool False)) ->
                let andExpr = Infix And cond x
                in (andExpr, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf simplifiedExpr andExpr])
            -- Caso if c then True else x -> c || x
            If cond (Lit (LitBool True)) x ->
                let orExpr = Infix Or cond x
                in (orExpr, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf simplifiedExpr orExpr])
            -- Caso general si no hay simplificación
            _ -> (simplifiedExpr, suggsCond ++ suggs1 ++ suggs2)

    -- Casos recursivos para otras expresiones
    Infix op e1 e2 ->
        let (e1', suggs1) = lintRedIfCond e1
            (e2', suggs2) = lintRedIfCond e2
        in (Infix op e1' e2', suggs1 ++ suggs2)

    App e1 e2 ->
        let (e1', suggs1) = lintRedIfCond e1
            (e2', suggs2) = lintRedIfCond e2
        in (App e1' e2', suggs1 ++ suggs2)

    Lam n e ->
        let (e', suggs) = lintRedIfCond e
        in (Lam n e', suggs)

    Case e1 e2 (n1, n2, e3) ->
        let (e1', suggs1) = lintRedIfCond e1
            (e2', suggs2) = lintRedIfCond e2
            (e3', suggs3) = lintRedIfCond e3
        in (Case e1' e2' (n1, n2, e3'), suggs1 ++ suggs2 ++ suggs3)

    -- Casos base que no necesitan transformación
    e -> (e, [])




--------------------------------------------------------------------------------
-- Sustitución de if por conjunción entre la condición y su rama _then_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfAnd :: Linting Expr
lintRedIfAnd expr = case expr of
    -- Primero, simplificamos cualquier `if` en las subexpresiones
    If cond e1 e2 ->
        let (cond', suggsCond) = lintRedIfAnd cond
            (e1', suggs1) = lintRedIfAnd e1
            (e2', suggs2) = lintRedIfAnd e2
            simplifiedExpr = If cond' e1' e2'
        in case simplifiedExpr of
            -- Caso: if (x == True) then True else False -> x
            If (Infix Eq (Var "x") (Lit (LitBool True))) (Lit (LitBool True)) (Lit (LitBool False)) ->
                (Var "x", suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf expr (Var "x")])

            -- Caso: if (y == True) then (z == True) else False -> y && z
            If (Infix Eq (Var "y") (Lit (LitBool True))) (Infix Eq (Var "z") (Lit (LitBool True))) (Lit (LitBool False)) ->
                (Infix And (Var "y") (Var "z"), suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf expr (Infix And (Var "y") (Var "z"))])

            -- Caso: if (x == True) then y else False -> x && y
            If (Infix Eq (Var "x") (Lit (LitBool True))) y (Lit (LitBool False)) ->
                (Infix And (Var "x") y, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf expr (Infix And (Var "x") y)])

            -- Caso general sin simplificación, pero con comparación redundante
            -- Reemplazar `x == True` por la variable booleana directamente.
            If (Infix Eq cond' (Lit (LitBool True))) e1 (Lit (LitBool False)) ->
                (Infix And cond' e1, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf expr (Infix And cond' e1)])

            -- Caso general sin simplificación
            _ -> (simplifiedExpr, suggsCond ++ suggs1 ++ suggs2)

    -- Casos recursivos para otras expresiones
    Infix op e1 e2 ->
        let (e1', suggs1) = lintRedIfAnd e1
            (e2', suggs2) = lintRedIfAnd e2
        in (Infix op e1' e2', suggs1 ++ suggs2)

    App e1 e2 ->
        let (e1', suggs1) = lintRedIfAnd e1
            (e2', suggs2) = lintRedIfAnd e2
        in (App e1' e2', suggs1 ++ suggs2)

    Lam n e ->
        let (e', suggs) = lintRedIfAnd e
        in (Lam n e', suggs)

    Case e1 e2 (n1, n2, e3) ->
        let (e1', suggs1) = lintRedIfAnd e1
            (e2', suggs2) = lintRedIfAnd e2
            (e3', suggs3) = lintRedIfAnd e3
        in (Case e1' e2' (n1, n2, e3'), suggs1 ++ suggs2 ++ suggs3)

    -- Casos base que no necesitan transformación
    e -> (e, [])

--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfOr :: Linting Expr
lintRedIfOr expr = case expr of
    -- Primero, simplificamos cualquier `if` en las subexpresiones
    If cond e1 e2 ->
        let (cond', suggsCond) = lintRedIfOr cond
            (e1', suggs1) = lintRedIfOr e1
            (e2', suggs2) = lintRedIfOr e2
            simplifiedExpr = If cond' e1' e2'
        in case simplifiedExpr of
            -- Caso específico: if (x == True) then True else False -> x
            If (Infix Eq x (Lit (LitBool True))) (Lit (LitBool True)) (Lit (LitBool False)) ->
                (x, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf expr x])

            -- Caso específico: if (x == True) then True else y -> x || y
            If (Infix Eq x (Lit (LitBool True))) (Lit (LitBool True)) y ->
                let orExpr = Infix Or x y
                in (orExpr, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf expr orExpr])

            -- Caso general sin simplificación
            _ -> (simplifiedExpr, suggsCond ++ suggs1 ++ suggs2)

    -- Casos recursivos para otras expresiones
    Infix op e1 e2 ->
        let (e1', suggs1) = lintRedIfOr e1
            (e2', suggs2) = lintRedIfOr e2
        in (Infix op e1' e2', suggs1 ++ suggs2)

    App e1 e2 ->
        let (e1', suggs1) = lintRedIfOr e1
            (e2', suggs2) = lintRedIfOr e2
        in (App e1' e2', suggs1 ++ suggs2)

    Lam n e ->
        let (e', suggs) = lintRedIfOr e
        in (Lam n e', suggs)

    Case e1 e2 (n1, n2, e3) ->
        let (e1', suggs1) = lintRedIfOr e1
            (e2', suggs2) = lintRedIfOr e2
            (e3', suggs3) = lintRedIfOr e3
        in (Case e1' e2' (n1, n2, e3'), suggs1 ++ suggs2 ++ suggs3)

    -- Casos base que no necesitan transformación
    e -> (e, [])

--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r)

-- Sugiere el uso de `null` para verificar si una lista está vacía
-- Reemplaza `e == []` o `length e == 0` con `null e`
lintNull :: Linting Expr
lintNull expr = case expr of
    -- Caso `e == []` o `[] == e`, reemplazable por `null e`
    Infix Eq e (Lit LitNil) ->
        let (e', suggs) = lintNull e
            nullExpr = App (Var "null") e'
        in (nullExpr, suggs ++ [LintNull expr nullExpr])

    Infix Eq (Lit LitNil) e ->
        let (e', suggs) = lintNull e
            nullExpr = App (Var "null") e'
        in (nullExpr, suggs ++ [LintNull expr nullExpr])

    -- Caso `length e == 0` o `0 == length e`, reemplazable por `null e`
    Infix Eq (App (Var "length") e) (Lit (LitInt 0)) ->
        let (e', suggs) = lintNull e
            nullExpr = App (Var "null") e'
        in (nullExpr, suggs ++ [LintNull expr nullExpr])

    Infix Eq (Lit (LitInt 0)) (App (Var "length") e) ->
        let (e', suggs) = lintNull e
            nullExpr = App (Var "null") e'
        in (nullExpr, suggs ++ [LintNull expr nullExpr])

    -- Recursión en subexpresiones
    If cond e1 e2 ->
        let (cond', suggsCond) = lintNull cond
            (e1', suggs1) = lintNull e1
            (e2', suggs2) = lintNull e2
        in (If cond' e1' e2', suggsCond ++ suggs1 ++ suggs2)

    Infix op e1 e2 ->
        let (e1', suggs1) = lintNull e1
            (e2', suggs2) = lintNull e2
        in (Infix op e1' e2', suggs1 ++ suggs2)

    App e1 e2 ->
        let (e1', suggs1) = lintNull e1
            (e2', suggs2) = lintNull e2
        in (App e1' e2', suggs1 ++ suggs2)

    Lam n e ->
        let (e', suggs) = lintNull e
        in (Lam n e', suggs)

    Case e1 e2 (n1, n2, e3) ->
        let (e1', suggs1) = lintNull e1
            (e2', suggs2) = lintNull e2
            (e3', suggs3) = lintNull e3
        in (Case e1' e2' (n1, n2, e3'), suggs1 ++ suggs2 ++ suggs3)

    -- Casos base que no necesitan transformación
    e -> (e, [])



--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r)

-- Función principal lintAppend
lintAppend :: Linting Expr
lintAppend expr = case expr of
    -- Caso (e:[] ++ es) -> (e:es)
    
    -- Caso recursivo para otras expresiones Infix Append
    Infix Append e1 e2 ->
        let (e1', suggs1) = lintAppend e1
            (e2', suggs2) = lintAppend e2
        in case e1' of 
            Infix Cons e (Lit LitNil) -> (Infix Cons e e2', suggs1 ++ suggs2 ++ [LintAppend(Infix Append e1' e2') (Infix Cons e e2')])
            _ -> (Infix Append e1' e2', suggs1 ++ suggs2)

    Infix op e1 e2 ->
        let (e1', suggs1) = lintAppend e1
            (e2', suggs2) = lintAppend e2
        in (Infix op e1' e2', suggs1 ++ suggs2)
    
    -- Caso App
    App e1 e2 ->
        let (e1', suggs1) = lintAppend e1
            (e2', suggs2) = lintAppend e2
        in (App e1' e2', suggs1 ++ suggs2)

    -- Caso Lam
    Lam n e ->
        let (e', suggs) = lintAppend e
        in (Lam n e', suggs)

    -- Caso Case
    Case e1 e2 (n1, n2, e3) ->
        let (e1', suggs1) = lintAppend e1
            (e2', suggs2) = lintAppend e2
            (e3', suggs3) = lintAppend e3
        in (Case e1' e2' (n1, n2, e3'), suggs1 ++ suggs2 ++ suggs3)

    -- Caso If
    If e1 e2 e3 ->
        let (e1', suggs1) = lintAppend e1
            (e2', suggs2) = lintAppend e2
            (e3', suggs3) = lintAppend e3
        in (If e1' e2' e3', suggs1 ++ suggs2 ++ suggs3)

    -- Casos base que no necesitan transformación
    e -> (e, [])


--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r)

lintComp :: Linting Expr
lintComp expr = case expr of

    -- Caso de composición con dos funciones anidadas: f (g x)
    App e1 e2 ->
        let (e1', suggs1) = lintComp e1
            (e2', suggs2) = lintComp e2
        in case e2' of
            App e3 e4 -> (App (Infix Comp e1' e3) e4, suggs1 ++ suggs2 ++ [LintComp (App e1' e2') (App (Infix Comp e1' e3) e4)])
            _ -> (App e1' e2', suggs1 ++ suggs2)

    Infix op e1 e2 ->
        let (e1', suggs1) = lintComp e1
            (e2', suggs2) = lintComp e2
        in (Infix op e1' e2', suggs1 ++ suggs2)


    -- Caso de If con transformaciones en ambas ramas
    If cond thenExpr elseExpr ->
        let (transformedThen, suggsThen) = lintComp thenExpr
            (transformedElse, suggsElse) = lintComp elseExpr
            transformedIf = If cond transformedThen transformedElse
        in (transformedIf, suggsThen ++ suggsElse)

    -- Caso de Case con transformaciones
    Case expr caseNil (name1, name2, caseCons) ->
        let (transformedExpr, suggsExpr) = lintComp expr
            (transformedCaseNil, suggsNil) = lintComp caseNil
            (transformedCaseCons, suggsCons) = lintComp caseCons
        in (Case transformedExpr transformedCaseNil (name1, name2, transformedCaseCons),
            suggsExpr ++ suggsNil ++ suggsCons)

    -- Caso de Lambda con transformaciones en el cuerpo
    Lam name body ->
        let (transformedBody, suggestions) = lintComp body
        in (Lam name transformedBody, suggestions)

    -- Otros casos: no transformar
    e -> (e, [])



--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)

-- Eta Reducción
--------------------------------------------------------------------------------
-- Se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)

lintEta :: Linting Expr
lintEta expr = case expr of

      -- Caso genérico de eta-reducción
    Lam x e1 -> 
        let (e1', suggs1) = lintEta e1  -- Aplicamos recursión al cuerpo de la lambda
        in case e1' of
            App e2 (Var y) | x == y && notElem x (freeVariables e2) ->
                -- Si cumple las condiciones de eta-reducción
                (e2, suggs1 ++ [LintEta (Lam x e1') e2])
            _ -> (Lam x e1', suggs1)  -- Si no aplica, devolvemos la lambda transformada recursivamente
    
    -- Lam name body ->
    --     let (transformedBody, suggestions) = lintEta body
    --     in (Lam name transformedBody, suggestions)

    App e1 e2 ->
        let (e1', suggs1) = lintEta e1
            (e2', suggs2) = lintEta e2
        in (App e1' e2', suggs1 ++ suggs2)

    Infix op e1 e2 ->
        let (e1', suggs1) = lintEta e1
            (e2', suggs2) = lintEta e2
        in (Infix op e1' e2', suggs1 ++ suggs2)

    If cond thenExpr elseExpr ->
        let (transformedThen, suggsThen) = lintEta thenExpr
            (transformedElse, suggsElse) = lintEta elseExpr
            transformedIf = If cond transformedThen transformedElse
        in (transformedIf, suggsThen ++ suggsElse)

    Case expr caseNil (name1, name2, caseCons) ->
        let (transformedExpr, suggsExpr) = lintEta expr
            (transformedCaseNil, suggsNil) = lintEta caseNil
            (transformedCaseCons, suggsCons) = lintEta caseCons
        in (Case transformedExpr transformedCaseNil (name1, name2, transformedCaseCons),
            suggsExpr ++ suggsNil ++ suggsCons)

    -- Otros casos: no transformar
    e -> (e, [])

-- ver como actualizar la sugerencia

--------------------------------------------------------------------------------
-- Eliminación de recursión con map
--------------------------------------------------------------------------------

-- Sustituye recursión sobre listas por `map`
-- Construye sugerencias de la forma (LintMap f r)
lintMap :: Linting FunDef
lintMap = \fndf ->
    case fndf of
        FunDef funcname (Lam paramname (Case (Var paramname') (Lit (LitNil)) (n1, n2, Infix Cons e (App (Var funcname') (Var n2')))))
            | funcname == funcname' && paramname == paramname' && n2 == n2' ->
                let freeVars = freeVariables e
                in if paramname `elem` freeVars || n2 `elem` freeVars
                    then (fndf, [])
                    else
                        let suggestion = FunDef funcname (App (Var "map") (Lam n1 e))
                        in (suggestion, [LintMap fndf suggestion])
        _ -> (fndf, [])



--------------------------------------------------------------------------------
-- Combinación de Lintings
--------------------------------------------------------------------------------


-- Dada una transformación a nivel de expresión, se construye
-- una transformación a nivel de función
liftToFunc :: Linting Expr -> Linting FunDef
liftToFunc lint (FunDef name expr) = 
    let (expr', suggs) = lint expr
    in (FunDef name expr', suggs)

-- encadenar transformaciones:
(>==>) :: Linting a -> Linting a -> Linting a
lint1 >==> lint2 = \x -> 
    let (x', suggs1) = lint1 x
        (x'', suggs2) = lint2 x'
    in (x'', suggs1 ++ suggs2)

-- aplica las transformaciones 'lints' repetidas veces y de forma incremental,
-- hasta que ya no generen más cambios en 'func'
lintRec :: Linting a -> Linting a
lintRec lints func = 
    let 
        (res, sugg) = lints func
    in  
        if null sugg
        then (res, sugg)
        else 
            let (res2, sugg2) = lintRec lints res
            in (res2, sugg ++ sugg2)