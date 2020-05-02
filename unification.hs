-- Ritwik Divakaruni
-- A20386609

-- Import statements
import Data.Char
import Data.List

-- Designing Unification (Key Functions)
-- solve :: String -> String
-- parse :: String -> Unification Expression 
-- unify :: Input from parse -> Solution to unification problem 
-- pprint :: Unification Expression -> String
-- substitute :: Unification Expression -> Variable -> Unification Expression -> Unification Expression

type Equation = (Ptree, Ptree) 
type Expression = [Equation]
type Substitution = Equation
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
    | ErrMsg String
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
lbracket = '{' :: Symbol
rbracket = '}' :: Symbol
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
getFuncName (Function string _) = string

getFuncArgs :: Ptree -> [Ptree]
getFuncArgs (Function string args) = args

parse :: String -> Expression
parse input = case parse_problem input of
    Just (parsing, "", eqs) -> eqs
    _ -> []

parse_problem :: Parser1 Ptree
parse_problem input =
    next_symbol lbracket input          `bind` (\ (_, input1) ->
    parse_equations input1              `bind` (\ (equations, input2,arr1) ->
    next_symbol rbracket input2         `bind` (\ (_, input3) ->
    Just (equations, input3,arr1))))

parse_equations :: Parser1 Ptree
parse_equations input = 
    parse_equation input            `bind` (\ (equation, input1, arr1) ->
    parse_equationTail input1       `bind` (\ (equationTail, input2,arr2) ->
    Just (Expression equation equationTail, input2, arr1 ++ arr2)))

parse_equationTail :: Parser1 Ptree
parse_equationTail input =
    next_symbol comma input             `bind` (\ (_, input1) ->
    parse_equations input1              `bind` (\ (equations, input2,arr2) ->
    Just (equations, input2,arr2)))
                                        `fails` (\() -> Just(Empty, dropSpaces input,[]))

parse_equation :: Parser1 Ptree
parse_equation input =
    parse_E input               `bind` (\ (expr, input1) ->
    next_symbol equal input1    `bind` (\ (equals, input2) ->
    parse_E input2              `bind` (\ (expr1, input3) ->
    Just (Equation expr equals expr1,input3,[(expr, expr1)]))))

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

getConstant :: Parser String
getConstant [] = Nothing
getConstant (h:input1)
    | (isLetter h && isLower h) || isDigit h =
        let (idtail, input2) = span (\c -> isAlphaNum c || c == '_') input1
        in Just (h:idtail, input2)
    | otherwise = Nothing

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

unifyStarter :: (Expression, [Substitution]) -> Maybe (Expression, [Substitution])
unifyStarter temp = 
    do
    let 
        problemArr = fst temp
        sub = snd temp
    if (ErrMsg "Const/Constant", Error "Error") `elem` sub || (ErrMsg "Func", Error "Error") `elem` sub || (ErrMsg "Exp", Error "Error") `elem` sub then Just (problemArr, sub)
    else (if length problemArr > 0 then unifyHelper(problemArr, sub) else Just (problemArr, sub))


unifyHelper :: (Expression, [Substitution]) -> Maybe (Expression, [Substitution])
unifyHelper temp =
    do
        let
            expr = fst temp
            sub = snd temp
            equation = expr !! 0
            leftSide = fst equation
            rightSide = snd equation
        if isVariable leftSide || isVariable rightSide then
            (let 
                x = if isVariable leftSide then leftSide else rightSide
                s = if x == leftSide then rightSide else leftSide
            in if isVariable s && x == s then unifyStarter (drop 1 expr, sub) else unifyStarter (cmpSubstitutions (substituteAll expr (x,s)), (substituteAllSub sub (x,s)) ++ [(x, s)]))
            else 
                (if isConstant leftSide then 
                    (if leftSide == rightSide then unifyStarter (drop 1 expr, sub) else unifyStarter (expr, sub ++ [(ErrMsg "Const/Constant", Error "Error")]))
                else (if isFunc leftSide then 
                    (if isFunc rightSide && getFuncName leftSide == getFuncName rightSide && length (getFuncArgs leftSide) == length (getFuncArgs rightSide)
                        then unifyStarter ((drop 1 expr) ++ zip (getFuncArgs leftSide) (getFuncArgs rightSide), sub) else Just (expr, sub ++ [(ErrMsg "Func", Error "Error")]))
                    else Just (expr, sub ++ [(ErrMsg "Exp", Error "Error")])))


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
        let
            firstVal = sub !! 0
        extractVals (fst firstVal) ++ " -> " ++ extractVals (snd firstVal) ++ ", " ++ printSub (drop 1 sub)


substitute :: Equation -> Substitution -> Equation
substitute equation sub =
    do
        let
            newLeft = if fst equation == fst sub then snd sub else fst equation
            newRight = if snd equation == fst sub then snd sub else snd equation
        (newLeft, newRight)


substituteAll :: Expression -> Substitution -> Expression
substituteAll problem sub = map (\x -> substitute x sub) problem

substituteAllSub :: [Substitution] -> Substitution -> [Substitution]
substituteAllSub problem sub = map (\x -> substitute x sub) problem


cmpSubstitutions :: Expression -> Expression
cmpSubstitutions = filter (\(leftSide, rightSide) -> leftSide /= rightSide)

solve :: String -> String
solve problem = 
    do
        let
            parsed = parse problem
            unified = unify parsed
            prob = printExpr parsed
            prettyProb = "Expression: "++ "{" ++ take (length prob - 2) prob ++ "}"
            solution = case unified of
                        Just (expr, sub) -> pprint (expr,sub)
                        _ -> "Error"
        prettyProb ++ " ---> " ++ solution

pprint :: (Expression, [Substitution]) -> String
pprint (expr, sub) =
    do
        let
            result = if length expr == 0 then "Unified" else "Not Unifyable" -- If the expression is still not equal to 0 it means that there is something that hasn't been unified yet. 
            substitution = 
                if (Constant "Const/Constant", Error "Error") `elem` sub || (Constant "Func", Error "Error") `elem` sub || (Constant "Exp", Error "Error") `elem` sub then printSub (take (length sub - 1) sub)
                else printSub sub
            prettySub = "{" ++ take (length (substitution) - 2) substitution ++ "}"
            prettySolution = result ++ " : " ++ prettySub
        prettySolution

-----------------------------------------------------------------------------------
-----------------------------------------------------------------------------------
-- Testing for unification

test1 = "{X=Y,X=3}" -- [Y ↦ 3, X ↦ 3]
test2 = "{X=1,X=3}" -- Failure
test3 = "{f(a,Y)=f(X,b),c=Z}" -- [Z ↦ c, Y ↦ b, X ↦ a]
test4 = "{f(X)=g(Y)}" -- Failure
test5 = "{f(X,Y)=f(X)}" -- Failure
test6 = "{f(f(f(f(a,Z),Y),X),W) = f(W,f(X,f(Y,f(Z,a))))}" -- [ Z ↦ a, Y ↦ f(a, a), X ↦ f(f(a, a), f(a, a)), W ↦ f(f(f(a, a), f(a, a)), f(f(a, a), f(a, a))) ] 

main :: IO()
main = do
    putStrLn("TEST 1: " ++ solve test1)
    putStrLn("TEST 2: " ++ solve test2)
    putStrLn("TEST 3: " ++ solve test3)
    putStrLn("TEST 4: " ++ solve test4)
    putStrLn("TEST 5: " ++ solve test5)
    putStrLn("TEST 6: " ++ solve test6)

-- RUN main in ghci to run all the test cases to see the inputs