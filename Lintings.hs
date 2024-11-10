module Lintings where

import AST
import LintTypes


--------------------------------------------------------------------------------
-- AUXILIARES
--------------------------------------------------------------------------------

-- Computa la lista de variables libres de una expresión
freeVariables :: Expr -> [Name]
freeVariables (Var v) = [v]                    -- Una variable es libre por sí misma
freeVariables (Lit _) = []                        -- Los literales no tienen variables libres
freeVariables (App e1 e2) = freeVariables e1 ++ freeVariables e2  -- Variables libres en ambas partes de la aplicación
freeVariables (Lam v e) = filter (/= v) (freeVariables e) -- En una lambda, quitamos la variable vinculada
freeVariables (Case e ncase (x, xs, ccase)) = freeVariables e ++ filter (`notElem` [x, xs]) (freeVariables ncase) ++ freeVariables ccase
freeVariables (If cond t e) = freeVariables cond ++ freeVariables t ++ freeVariables e
freeVariables (Infix _ l r) = freeVariables l ++ freeVariables r



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
lintComputeConstant = Linting $ \expr -> case expr of
  -- Aquí se pueden agregar más patrones según sea necesario
  Lit (LitInt i) -> Right (Lit (LitInt i))   -- Si ya es una constante, no cambia
  Lit (LitBool b) -> Right (Lit (LitBool b)) -- Lo mismo para los booleanos
  Infix op l r -> do
    -- Evaluamos las subexpresiones
    left <- lintComputeConstant l
    right <- lintComputeConstant r
    -- Intentamos evaluar la expresión
    case (left, right) of
      (Lit (LitInt li), Lit (LitInt ri)) -> Right (Lit (LitInt (computeInt op li ri))) -- Computamos el resultado
      (Lit (LitBool lb), Lit (LitBool rb)) -> Right (Lit (LitBool (computeBool op lb rb))) -- Computamos booleanos
      _ -> Right (Infix op left right)  -- Si no podemos simplificar, devolvemos la expresión original

  App f arg -> do
    -- Aplicamos el linting recursivamente en función y argumento
    f' <- lintComputeConstant f
    arg' <- lintComputeConstant arg
    Right (App f' arg')  -- Retornamos la aplicación sin cambios

  Lam v body -> do
    body' <- lintComputeConstant body
    Right (Lam v body')  -- Retornamos la lambda sin cambios

  _ -> Right expr  -- Cualquier otra expresión no es simplificable aquí



--------------------------------------------------------------------------------
-- Eliminación de chequeos redundantes de booleanos
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Elimina chequeos de la forma e == True, True == e, e == False y False == e
-- Construye sugerencias de la forma (LintBool e r)
lintRedBool :: Linting Expr
lintRedBool = Linting $ \expr -> case expr of
  -- Si la expresión es una comparación con True
  Infix Eq (Lit (LitBool True)) e -> Right e  -- True == e -> e
  Infix Eq e (Lit (LitBool True)) -> Right e  -- e == True -> e
  -- Si la expresión es una comparación con False
  Infix Eq (Lit (LitBool False)) e -> Right (Not e)  -- False == e -> Not e
  Infix Eq e (Lit (LitBool False)) -> Right (Not e)  -- e == False -> Not e
  -- Si no se cumple ninguno de los casos anteriores, retornamos la expresión sin cambios
  _ -> Right expr


--------------------------------------------------------------------------------
-- Eliminación de if redundantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Sustitución de if con literal en la condición por la rama correspondiente
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfCond :: Linting Expr
lintRedIfCond = Linting $ \expr -> case expr of
  -- Si la condición es True, retornamos la rama 'then'
  If (Lit (LitBool True)) thenBranch _ -> Right thenBranch
  -- Si la condición es False, retornamos la rama 'else'
  If (Lit (LitBool False)) _ elseBranch -> Right elseBranch
  -- Si no es un literal, retornamos la expresión sin cambios
  _ -> Right expr

--------------------------------------------------------------------------------
-- Sustitución de if por conjunción entre la condición y su rama _then_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfAnd :: Linting Expr
lintRedIfAnd = Linting $ \expr -> case expr of
  If cond thenBranch elseBranch ->
    -- Si la rama 'then' es una expresión que tiene valor booleana
    -- construimos una nueva expresión de la forma (cond && thenBranch)
    Right (Infix And cond thenBranch)
  _ -> Right expr  -- Si no es un if, devolvemos la expresión original

--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfOr :: Linting Expr
lintRedIfOr = Linting $ \expr -> case expr of
  If cond thenBranch elseBranch ->
    -- Si la rama 'else' es una expresión que tiene valor booleana
    -- construimos una nueva expresión de la forma (cond || elseBranch)
    Right (Infix Or cond elseBranch)
  _ -> Right expr  -- Si no es un if, devolvemos la expresión original

--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r)

lintNull :: Linting Expr
lintNull = Linting $ \expr -> case expr of
  Infix Eq list (Lit (LitList [])) -> 
    -- Si tenemos una expresión del tipo `list == []`, la reemplazamos por `null list`
    Right (App (Var "null") list)
  _ -> 
    -- Si no es una comparación de lista vacía, devolvemos la expresión original
    Right expr

--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r)

lintAppend :: Linting Expr
lintAppend = Linting $ \expr -> case expr of
  Infix Append (Cons e (Lit (LitList []))) es ->
    -- Si tenemos una expresión de la forma (e : [] ++ es), la reemplazamos por (e : es)
    Right (Cons e es)
  
  _ ->
    -- Si no coincide con el patrón, devolvemos la expresión original
    Right expr

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r)

lintComp :: Linting Expr
lintComp = Linting $ \expr -> case expr of
  App f (App g t) ->
    -- Si tenemos una expresión de la forma (f (g t)), la transformamos en (f . g) t
    Right (App (Infix Comp f g) t)
  
  _ ->
    -- Si no coincide con el patrón, devolvemos la expresión original
    Right expr


--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)

lintEta :: Linting Expr
lintEta = Linting $ \expr -> case expr of
  Lam x (App e (Var y)) | x == y ->
    -- Si la expresión es de la forma \x -> e x y, aplicamos la reducción eta
    Right e
  
  _ ->
    -- Si no coincide con el patrón, devolvemos la expresión original
    Right expr


--------------------------------------------------------------------------------
-- Eliminación de recursión con map
--------------------------------------------------------------------------------

-- Sustituye recursión sobre listas por `map`
-- Construye sugerencias de la forma (LintMap f r)
lintMap :: Linting FunDef
lintMap = Linting $ \funDef -> case funDef of
  FunDef name args body -> do
    -- Evaluamos el cuerpo de la función
    let freeVars = freeVariables body
    
    -- Verificamos si se puede sustituir la recursión
    if canUseMap args body
      then
        -- Si es posible, construimos la expresión usando map
        let (arg:_) = args  -- Suponemos que hay al menos un argumento
            mapBody = App (App (Var "map") (Lam arg body)) (Var arg)
        in Right (FunDef name [arg] mapBody)
      else
        -- Si no, devolvemos la definición original
        Right funDef

  _ -> Right funDef  -- Manejo de otros tipos de definiciones de funciones

-- Verifica si la función puede ser reemplazada por map
canUseMap :: [Name] -> Expr -> Bool
canUseMap args body =
  case body of
    App (Var f) (Var x) -> f == head args && x == head args  -- Asegura que la función y el argumento sean los correctos
    _ -> False  -- En otros casos, no se puede usar map


--------------------------------------------------------------------------------
-- Combinación de Lintings
--------------------------------------------------------------------------------


-- Dada una transformación a nivel de expresión, se construye
-- una transformación a nivel de función
liftToFunc :: Linting Expr -> Linting FunDef
liftToFunc = undefined

-- encadenar transformaciones:
(>==>) :: Linting a -> Linting a -> Linting a
lint1 >==> lint2 = undefined

-- aplica las transformaciones 'lints' repetidas veces y de forma incremental,
-- hasta que ya no generen más cambios en 'func'
lintRec :: Linting a -> Linting a
lintRec lints func = undefined
