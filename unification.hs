-- UNIFICATION PROJECT - CS440 IIT
-- Ritwik Divakaruni
-- A20386609

-- Import statements
import Data.Char
import Data.List

-- Designing Unification -- Initial thoughts
-- solve :: String -> String
-- parse :: String -> Unification Expression
-- unify :: Input from parse -> Solution to unification problem
-- pprint :: Unification Expression -> String
-- substitute :: Unification Expression -> Variable -> Unification Expression -> Unification Expression

-- Basic definitons
type Equation = (Ptree, Ptree)
type Expression = [Equation]
type Substitution = Equation
-----------------------------------------------------------------
-- FULL DISCLOSURE: Most of this was taken from homework parsing solutions
-- Parser
-- Few rules to follow:
-- 1. The string inputs need to begin with { and end with }
-- We need to parse for
-- 1. Variables (Capital Alphabets),
-- 2. Constants (String | alphaNum which is lowercase)
-- 3. Functions (Character|String followed by open parenthesis)

data Ptree =
    Empty
    | Constant String
    | Variable String
    | Function String [Ptree]
    | Exp Ptree Ptree
    | Term Ptree Ptree
    | Ttail Symbol Ptree Ptree
    | Ftail Symbol Ptree Ptree
    | Negative Ptree
    | Equation Ptree Symbol Ptree
    | Expression Ptree Ptree
    | Error String
    deriving (Eq, Show, Read)

-- We are just converting the string
extractVals :: Ptree -> [Char]
extractVals (Variable value) = value
extractVals (Constant value) = value
extractVals (Function value tree) = value ++ "(" ++ concat (intersperse "," (map extractVals tree)) ++ ")"
extractVals _ = ""

-- Taken directly from homeworks
type Symbol = Char
type Input  = [Symbol]

-- Symbols we might encounter
comma  = ',' :: Symbol
lparen = '(' :: Symbol
minus  = '-' :: Symbol
plus   = '+' :: Symbol
rparen = ')' :: Symbol
star   = '*' :: Symbol
lcurlybrackets = '{' :: Symbol
rcurlybrackets = '}' :: Symbol
equal = '=' :: Symbol

type Parser t = Input -> Maybe (t, Input)
type Parser1 t = Input -> Maybe(t,Input,Expression)


isVariable :: Ptree -> Bool
isVariable (Variable _) = True
isVariable _ = False

isFunc :: Ptree -> Bool
isFunc (Function string _) = True
isFunc _ = False

isConstant :: Ptree -> Bool
isConstant (Constant _) = True
isConstant _ = False

getFuncName :: Ptree -> [Char]
getFuncName (Function name _) = name

getFuncArgs :: Ptree -> [Ptree]
getFuncArgs (Function name args) = args

parse :: String -> Expression
parse input = case parse_input input of
    Just (parsing, "", eqs) -> eqs
    _ -> []

parse_input :: Parser1 Ptree
parse_input input =
    next_symbol lcurlybrackets input          `bind` (\ (_, input1) ->
    parse_expressions input1              `bind` (\ (equations, input2,arr1) ->
    next_symbol rcurlybrackets input2         `bind` (\ (_, input3) ->
    Just (equations, input3,arr1))))

parse_expressions :: Parser1 Ptree
parse_expressions input =
    parse_equation input            `bind` (\ (equation, input1, arr1) ->
    parse_equationTail input1       `bind` (\ (equationTail, input2,arr2) ->
    Just (Expression equation equationTail, input2, arr1 ++ arr2)))

parse_equation :: Parser1 Ptree
parse_equation input =
    parse_E input               `bind` (\ (expr, input1) ->
    next_symbol equal input1    `bind` (\ (equals, input2) ->
    parse_E input2              `bind` (\ (expr1, input3) ->
    Just (Equation expr equals expr1,input3,[(expr, expr1)]))))

parse_equationTail :: Parser1 Ptree
parse_equationTail input =
    next_symbol comma input             `bind` (\ (_, input1) ->
    parse_expressions input1              `bind` (\ (equations, input2,arr2) ->
    Just (equations, input2,arr2)))
                                        `fails` (\() -> Just(Empty, dropSpaces input,[]))

parse_E :: Parser Ptree
parse_E input =
    (parse_T input)         `bind` (\ (term, input1) ->
    (parse_Ttail input1)    `bind` (\ (ttail, input2) ->
    Just (make_tail Exp term ttail, input2) ))

parse_T :: Parser Ptree
parse_T input =
    parse_F input       `bind`  (\ (factor, input1) ->
    parse_Ftail input1  `bind`  (\ (ftail, input2) ->
    Just (make_tail Term factor ftail, input2) ))

parse_Ttail :: Parser Ptree
parse_Ttail input =
    next_symbol plus input      `bind` (\ (symbol, input1) ->
    parse_T input1              `bind` (\ (term, input2) ->
    parse_Ttail input2          `bind` (\ (ttail, input3) ->
    Just (Ttail symbol term ttail, input3) )))
                                `fails` (\() ->
    parse_empty input )

parse_F :: Parser Ptree
parse_F input =
    parse_id_or_call input  `fails` (\() ->
    parse_paren_E input     `fails` (\() ->
    parse_negative input ))

parse_Ftail :: Parser Ptree
parse_Ftail input =
    next_symbol star input      `bind` (\ (symbol, input1) ->
    parse_F input1              `bind` (\ (factor, input2) ->
    parse_Ftail input2          `bind` (\ (ftail, input3) ->
    Just (Ftail symbol factor ftail, input3) )))
                                `fails` (\() ->
    parse_empty input )

parse_id_or_call :: Parser Ptree
parse_id_or_call input =
    getConstant (dropSpaces input)        `bind`  (\ (idstring, input1) ->
    parse_arguments input1          `bind`  (\ (argtail, input2) ->
    Just (Function idstring argtail, input2) )
                                    `fails` (\ () ->
    Just (Constant idstring, input1) ))   `fails` (\ () ->
    getVariable (dropSpaces input)       `bind` (\ (varString, input3) ->
    parse_arguments input3          `bind` (\ (argtail1, input4) ->
    Just (Function varString argtail1, input4))
                                    `fails` (\() ->
    Just (Variable varString, input3))))

parse_arguments :: Parser [Ptree]
parse_arguments input =
    next_symbol lparen input    `bind`  (\ (_, input1) ->
    parse_E input1              `bind`  (\ (arg1, input2) ->
    parse_argtail input2        `bind`  (\ (args, input3) ->
    next_symbol rparen input3   `bind`  (\ (_, input4) ->
    Just (arg1:args, input4) ))))

parse_argtail :: Parser [Ptree]
parse_argtail input =
    next_symbol comma input     `bind`  (\(_, input1) ->
    parse_E input1              `bind`  (\(arg, input2) ->
    parse_argtail input2        `bind`  (\(args, input3) ->
    Just (arg:args, input3))))
                                `fails` (\() ->
    Just ([], input) )

parse_paren_E :: Parser Ptree
parse_paren_E input =
    next_symbol lparen input    `bind` (\ (_, input1) ->
    parse_E input1              `bind` (\ (etree, input2) ->
    next_symbol rparen input2   `bind` (\ (_, input3) ->
    Just (etree, input3) )))

parse_negative :: Parser Ptree
parse_negative input =
    next_symbol minus input     `bind`  (\(_, input1) ->
    parse_F input1              `bind`  (\(factor, input2) ->
    Just (Negative factor, input2)))

parse_empty input = Just(Empty, dropSpaces input)

next_symbol :: Symbol -> Parser Symbol
next_symbol symbol input =
    case dropSpaces input of
        [] -> Nothing
        (h:input1) | h == symbol -> Just(symbol, input1)
        _ -> Nothing

make_tail :: (Ptree -> Ptree -> Ptree) -> Ptree -> Ptree -> Ptree
make_tail _ ptree Empty = ptree
make_tail build ptree tailtree =
    build ptree tailtree

bind :: Maybe a -> (a -> Maybe b) -> Maybe b
bind Nothing f = Nothing
bind (Just val) f = f val

fails :: Maybe a -> (() -> Maybe a) -> Maybe a
fails Nothing f = f()
fails ok _ = ok

-- basically getId
getConstant :: Parser String
getConstant [] = Nothing
getConstant (h:input1)
    | (isLetter h && isLower h) || isDigit h =
        let (idtail, input2) = span (\c -> isAlphaNum c || c == '_') input1
        in Just (h:idtail, input2)
    | otherwise = Nothing

-- basically getVar. Renamed to reflect the use case of unification more and for me to understand wtf is happening
getVariable :: Parser String
getVariable [] = Nothing
getVariable (h:input1)
    | isLetter h && isUpper h =
        let (idtail, input2) = span (\c -> isAlphaNum c || c == '_') input1
        in Just (h:idtail, input2)
    | otherwise = Nothing

dropSpaces x = dropWhile isSpace x

-----------------------------------------------------------------
-- Unification
-- unify :: Input from parse -> Solution to unification problem

unify :: Expression -> Maybe (Expression, [Substitution])
unify solution = unifyStarter(solution, [])

-- checking if the expression still contains values and that error hasnt occured before running the helper function
unifyStarter :: (Expression, [Substitution]) -> Maybe (Expression, [Substitution])
unifyStarter temp =
    do
    let
        expr = fst temp
        sub = snd temp
    if (length expr > 0) && ((Empty, Error "Error") `notElem` sub) then unifyHelper(expr, sub) else Just (expr, sub)

--- This algorithm is literally taken from the lecture 16 and converted into haskell code
unifyHelper :: (Expression, [Substitution]) -> Maybe (Expression, [Substitution])
unifyHelper temp =
    do
        let
--  while P has an equation (t ≡ u)
-- . let P′ ← P less the member (t ≡ u) -- Basically select the first eq
            expr = fst temp
            sub = snd temp
            -- printExpr expr
            -- printSub sub
            leftEq = fst (expr !! 0)
            rightEq = snd (expr !! 0)
--  . let X be the variable and s be the non-variable (or other variable) in
-- . . . if s is also a variable and X ≡ s then skip
-- . . . else // add [X ↦ s] as a substitution but apply it to P′ and S first
-- . . . . s]et P′ ← P′ [X ↦ s // see note below
-- . . . . set S ← S [X ↦ s] ∪ {[X ↦ s]} // see note below
        if isVariable leftEq || isVariable rightEq then
            (let
                x = if isVariable leftEq then leftEq else rightEq
                s = if (x == leftEq) then rightEq else leftEq in
            if x == s
                then
                    unifyStarter (drop 1 expr, sub)
                else
                    unifyStarter (compareSubs (susbtituteExpr expr (x,s)), (susbtituteList sub (x,s)) ++ [(x, s)])) -- set S ← S [X ↦ s] ∪ {[X ↦ s]}
    -- . else if t is a constant or identifier then
    --      if u ≡ the same constant or identifier, then skip else fail
            else
                (if isConstant leftEq then
                    (if leftEq == rightEq then unifyStarter (drop 1 expr, sub)
                     else unifyStarter (expr, sub ++ [(Empty, Error "Error")]))
--          else if t ≡ f(v₁, v₂, …, v n) then
            -- . . if u is a function call g(w₁, w₂, …, wm) where f ≡ g and m = n
            -- . . then add the equations (v₁ ≡ w₁), (v₂ ≡ w₂), …, (vn≡ wn ) to P′
                else (if isFunc leftEq && isFunc rightEq then
                    (if compFunc leftEq rightEq
                        then unifyStarter ((drop 1 expr) ++ zip (getFuncArgs leftEq) (getFuncArgs rightEq), sub)
                        else Just (expr, sub ++ [(Empty, Error "Error")]))
                    else Just (expr, sub ++ [(Empty, Error "Error")])))

compFunc :: Ptree -> Ptree -> Bool
compFunc leftEq rightEq = (getFuncName leftEq == getFuncName rightEq) && (length (getFuncArgs leftEq) == length (getFuncArgs rightEq))

substitute :: Equation -> Substitution -> Equation
substitute equation sub =
    do
        let
            newLeft = if fst equation == fst sub then snd sub else fst equation
            newRight = if snd equation == fst sub then snd sub else snd equation
        (newLeft, newRight)

susbtituteExpr :: Expression -> Substitution -> Expression
susbtituteExpr expr sub = map (\x -> substitute x sub) expr

susbtituteList :: [Substitution] -> Substitution -> [Substitution]
susbtituteList subList sub = map (\x -> substitute x sub) subList

compareSubs :: Expression -> Expression
compareSubs = filter (\(leftEq, rightEq) -> leftEq /= rightEq)
----------------------------------------------------------------------------
-- Converting from Ptrees to Strings for expressions and substitions
printExpr :: Expression -> String
printExpr [] = ""
printExpr expr =
    do
        let
            frstExpr = expr !! 0
        extractVals (fst frstExpr) ++ " = " ++ extractVals (snd frstExpr) ++ ", " ++ printExpr (drop 1 expr)

printSub :: [Substitution] -> String
printSub [] = ""
printSub sub =
    do
        let firstVal = sub !! 0
        extractVals (fst firstVal) ++ " -> " ++ extractVals (snd firstVal) ++ ", " ++ printSub (drop 1 sub)

pprint :: (Expression, [Substitution]) -> String
pprint (expr, sub) =
    do
        let
            result = if length expr == 0 then "Unified" else "Not Unifyable" -- If the expression is still not equal to 0 it means that there is something that hasn't been unified yet.
            substitution =
                if (Empty, Error "Error") `elem` sub then printSub (take (length sub - 1) sub)
                else printSub sub
            prettySub = "{" ++ take (length (substitution) - 2) substitution ++ "}"
            prettySolution = if result == "Unified" then result ++ " : " ++ prettySub else "FAIL"
        prettySolution
-----------------------------------------------------------------------------------
-- Solve function which starts the process and goes through all the steps
solve :: String -> String
solve input =
    do
        let
            parsedVal = parse input
            unifiedVal = unify (parse input)
            convertStr = printExpr parsedVal
            prettyPrint = "Expression: "++ "{" ++ take (length convertStr - 2) convertStr ++ "}"
            pprintVal = case unifiedVal of
                        Just (expr, sub) -> pprint (expr,sub)
                        _ -> "Error"
            solution = if (pprintVal /= "FAIL" || pprintVal /= "Error") then prettyPrint ++ " ---> " ++ pprintVal else "FAIL"
        solution
-----------------------------------------------------------------------------------
-- Unit Testing for unification

test1 = "{X=Y,X=3}" -- [Y ↦ 3, X ↦ 3]
test2 = "{X=1,X=3}" -- Failure
test3 = "{f(a,Y)=f(X,b),c=Z}" -- [Z ↦ c, Y ↦ b, X ↦ a]
test4 = "{f(X)=g(Y)}" -- Failure
test5 = "{f(X,Y)=f(X)}" -- Failure
test6 = "{f(f(f(f(a,Z),Y),X),W) = f(W,f(X,f(Y,f(Z,a))))}" -- [ Z ↦ a, Y ↦ f(a, a), X ↦ f(f(a, a), f(a, a)), W ↦ f(f(f(a, a), f(a, a)), f(f(a, a), f(a, a))) ]
test7 = "{f(X,X,2)=f(5,Y,Z)}" -- [X ↦ 5, Y ↦ 5, Z ↦ 2]
test8 = "{f(X,Y,Z)=f(X,X,Z),f(X,Y,Z)=f(Y,Z,Z),f(A,B,B)=f(x,x,x)}" -- {Y -> Z, X -> Z, A -> x, B -> x}

main :: IO()
main = do
    putStrLn("TEST 1: " ++ solve test1)
    putStrLn("TEST 2: " ++ solve test2)
    putStrLn("TEST 3: " ++ solve test3)
    putStrLn("TEST 4: " ++ solve test4)
    putStrLn("TEST 5: " ++ solve test5)
    putStrLn("TEST 6: " ++ solve test6)
    putStrLn("TEST 7: " ++ solve test7)
    putStrLn("TEST 8: " ++ solve test8)
-- RUN main in ghci to run all the test cases to see the inputs
