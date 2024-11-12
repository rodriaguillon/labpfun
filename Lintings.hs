module Lintings where

import AST
import LintTypes


--------------------------------------------------------------------------------
-- AUXILIARES
--------------------------------------------------------------------------------

-- Computa la lista de variables libres de una expresión
freeVariables :: Expr -> [Name]
freeVariables = undefined


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
        in (Infix op e1' e2', suggs1 ++ suggs2)
        
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
            If (Lit (LitBool True)) _ eElse ->
                (e1', suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf expr e1'])
            -- Caso if False -> solo queda e2
            If (Lit (LitBool False)) eThen _ ->
                (e2', suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf expr e2'])
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
            -- Caso if c then e else False -> c && e
            If c e (Lit (LitBool False)) ->
                let andExpr = Infix And c e
                    originalExpr = If c e (Lit (LitBool False))
                in (andExpr, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf originalExpr andExpr])
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
            -- Caso if c then True else e -> c || e
            If c (Lit (LitBool True)) e ->
                let orExpr = Infix Or c e
                    originalExpr = If c (Lit (LitBool True)) e
                in (orExpr, suggsCond ++ suggs1 ++ suggs2 ++ [LintRedIf originalExpr orExpr])
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

lintNull :: Linting Expr
lintNull = undefined

--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r)

lintAppend :: Linting Expr
lintAppend = undefined

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r)

lintComp :: Linting Expr
lintComp = undefined


--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)

lintEta :: Linting Expr
lintEta = undefined


--------------------------------------------------------------------------------
-- Eliminación de recursión con map
--------------------------------------------------------------------------------

-- Sustituye recursión sobre listas por `map`
-- Construye sugerencias de la forma (LintMap f r)
lintMap :: Linting FunDef
lintMap = undefined


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
lintRec :: Eq a => Linting a -> a -> (a, [LintSugg])
lintRec lints func =
    let (func', suggs) = lints func
    in if func == func'
        then (func, suggs)
        else let (func'', suggs') = lintRec lints func'
                in (func'', suggs ++ suggs')