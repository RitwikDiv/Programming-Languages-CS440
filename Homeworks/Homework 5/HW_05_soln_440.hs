-- CS 440 Spring 2020
-- Solution to Homework 5: Lectures 9 & 10

--------------------------------------------------------------------------------
-- Programming Problem:

-- Lexical scanner (solution)
--
-- The scanner matches regular expressions against some input and
-- returns a list of the captured tokens (and leftover input).

-- scan input produces Just (list of tokens, remaining input)
--
data Token = Const Int | Id String | Op String | Punct String | Space
    deriving (Show, Read, Eq)

-- scan input runs the scan algorithm on the input and returns the list of
-- resulting tokens (if any).  It calls a helper routine with an empty list
-- of result tokens.
--
scan :: String -> [Token]
scan input = case scan' scan_rexps [] input of
    Just(tokens,_) -> tokens
    Nothing -> []

-- scan' rexps revtokens input applies the first regular expression of
-- the list rexps to the input.  If the match succeeds, the captured
-- string is passed to a token-making routine associated with the reg
-- expr, and we add the new token to the head of our reversed list of
-- tokens found so far.  Exception: We don't add a Space token.
--
scan' _ revtokens []  = Just (reverse revtokens, [])

scan' ((regexpr, mkToken) : rexps) revtokens input
    = case capture regexpr input of
        Nothing -> scan' rexps revtokens input
        Just(tokenString, input') ->        -- found a token string
            case mkToken tokenString of     -- build the token
                Space -> scan' rexps revtokens input' -- don't add token for spaces
                token -> scan' rexps (token : revtokens) input'

-- scan_rexps are the regexprs to use to break up the input.  The format of each
-- pair is (regexpr, fcn); if capture regexpr produces a string str, apply the function
-- to it to get a token.  scan_rexps is an infinite cycle of the regular expressions
-- the scanner is looking for
--
scan_rexps = cycle
   [(num_const, Const . read),    -- Read string to get number for token
    (identifier, Id), (operators, Op), (punctuation, Punct), (spaces, \_ -> Space) ]

num_const       = RE_and [digit1_9, RE_star digit]
digit1_9        = RE_in_set "123456789"
digit           = RE_in_set "0123456789"
operators       = RE_in_set "+-*/"
punctuation     = RE_in_set "[](){},;:.?!&#$%"

identifier      = RE_and[lead_id_symbol, RE_star next_id_symbols]
letters_        = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_"
lead_id_symbol  = RE_in_set letters_
next_id_symbols = RE_or [digit, lead_id_symbol]
spaces          = RE_star(RE_in_set " \t")

-- Regular expressions
data RegExpr a
    = RE_const a
    | RE_or [RegExpr a]
    | RE_and [RegExpr a]
    | RE_star (RegExpr a)
    | RE_in_set [a]           -- [...] - any symbol in list
    | RE_end                  -- $  - at end of input
    | RE_empty                -- epsilon - empty (no symbols)
        deriving (Eq, Read, Show)

-- Regular expressions have their own types for token, reversed token,
-- and input.  (They're used to make type annotations more understandable.)
--
type RE_Token a = [a]
type RE_RevToken a = [a]
type RE_Input a = [a]

-- capture matches a regular expression against some input; on success,
-- it returns the matching token (= list of input symbols) and the
-- remaining input.  E.g. capture abcd abcdef = Just(abcd, ef)
--
capture  :: Eq a => RegExpr a -> RE_Input a -> Maybe(RE_Token a, RE_Input a)

-- top-level capture routine calls assistant with empty built-up token to start
--
capture rexp input = case capture' rexp ([], input) of
    Nothing -> Nothing
    Just (revtoken, input') -> Just (reverse revtoken, input')


-- capture' rexp (partial_token input) matches the expression against
-- the input given a reversed partial token; on success, it returns
-- the completed token and remaining input. The token is in reverse
-- order. E.g., capture' cd (ba, cdef) = (dcba, ef)
--
capture' :: Eq a => RegExpr a -> (RE_RevToken a, RE_Input a) -> Maybe(RE_RevToken a, RE_Input a)

-- RE_const checks for a given symbol
--
capture' (RE_const _) (_, []) = Nothing
capture' (RE_const symbol) (revtoken, head_inp : input')
    | head_inp == symbol = Just (head_inp : revtoken, input')
    | otherwise = Nothing

-- the OR of no clauses fails; else try regexprs and stop on first success
--
capture' (RE_or []) _ = Nothing
capture' (RE_or (rexp : regexprs')) (revtoken, input) =
    case capture' rexp (revtoken, input) of
        Nothing -> capture' (RE_or regexprs') (revtoken, input)
        ok @ (Just _) -> ok

-- the AND of no clauses succeeds; else try regexprs and fail on first failure
--
capture' (RE_and []) (revtoken, input) = Just (revtoken, input)
capture' (RE_and (rexp : regexprs)) (revtoken, input) =
    case capture' rexp (revtoken, input) of
        Nothing -> Nothing
        Just (revtoken', input')
            -> capture' (RE_and regexprs) (revtoken', input')

-- Kleene star of expr converts to equivalent recursive reg expr
--
capture' (RE_star regexpr) state =
    capture' (RE_or [RE_and [regexpr, RE_star regexpr], RE_empty]) state

-- Check for symbol in a list of symbols
--
capture' (RE_in_set symbols) (revtoken, head_inp : input')
    | head_inp `elem` symbols = Just (head_inp : revtoken, input')
capture' (RE_in_set _) _ = Nothing

-- Match end of input; captures nothing if successful
--
capture' RE_end (revtoken, []) = Just (revtoken, [])
capture' RE_end _ = Nothing

-- empty regexpr matches but captures nothing
--
capture' RE_empty state = Just state


--------------------------------------------------------------------------------
-- Lec 10. Problem 1
-- Grammar rules for identifiers and function calls.  Below, \( and \) indicate literal parentheses.
--
-- Factor      -> Id_or_Call
-- Id_or_Call  -> Id ParenArgsOp
-- ParenArgsOp -> \( ArgListOp \) | ε
-- ArgListOp   -> Exp ArgTail | ε
-- ArgTail     -> , Exp ArgTail | ε

--------------------------------------------------------------------------------
-- Lec 10. Problem 2

-- (Rewrite ambiguous grammar for regular expressions to get LL(1) grammar)
--
-- Ambiguous grammar:
-- R → R R | R \| R | R \* | \[ Cs \] | \ε | \( R \)
-- Cs  → c Ctail
-- Ctail → c Ctail | ε

-- Top     -> Regexp $
-- Regexp  -> Term Ttail
-- Ttail   -> \| Term Ttail | ε
-- Term    -> Starred Ftail            
-- Starred -> Factor StarsOp
-- StarsOp -> Stars | ε
-- Stars   -> \* Stars | ε
-- Factor  -> Set | Paren | char | \ε
-- Ftail   -> Factor Ftail | ε
--
-- Set     -> \[ Chars \]
-- Chars   -> char CharsOp
-- CharsOp -> Chars | ε
-- Paren   -> \( Regexp \)
