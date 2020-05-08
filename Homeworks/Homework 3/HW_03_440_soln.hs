-- CS 440 Homework 3 Solution, Spring 2020

-- Problem 1:
-- common x y = (cp, x', y') where cp is the longest common prefix of x and y and x' and y' are leftover if you remove cp from x and y.  I.e., x == cp ++ x', y == cp ++ y', and cp can't be increased:
-- i.e., one or both of x' or y' are [] or the heads of x' and y' are unequal.

common :: Eq a => [a] -> [a] -> ([a], [a], [a])

common x y = common' [] x y

common' rev_cis (h1:t1) (h2:t2)
    | h1 == h2 = common' (h1 : rev_cis) t1 t2
common' rev_cis x y    -- x or y = []
    = (reverse rev_cis, x, y)

--------------------------------------------------------------------------------
-- Problem 2:
-- listShow mimics show for List t where t is not a datatype.
-- (So no List (List Int), e.g.)

-- data List a = LNode a (List a) | LNil deriving (Eq, Show) -- for testing
data List a = LNode a (List a) | LNil deriving (Eq) -- for not testing

listShow :: Show a => List a -> String
listShow LNil = "LNil"
listShow (LNode head LNil) = "LNode " ++ show head ++ " LNil"
listShow (LNode head tail) = "LNode " ++ show head ++ " (" ++ listShow tail ++ ")"

--------------------------------------------------------------------------------
-- Problem 3:
-- isFull tree is true if every node has two leafs or two Nodes for children.

data Tree a b = Leaf b | Node a (Tree a b) (Tree a b) deriving (Read, Show, Eq)

isFull (Leaf _) = True
isFull (Node _ (Leaf _) (Leaf _)) = True
isFull (Node _ (left@(Node _ _ _)) (right@(Node _ _ _)))
    = isFull left && isFull right
isFull _ = False

------------------------------
-- Problem 4:
-- eval exprtree = value of tree where an exprtree :: Tree String p
-- (1) has numeric leaf data and (2) node data is "+", "-", "*", or "/"

eval :: Fractional p => Tree [Char] p -> p
eval (Leaf val) = val
eval (Node optr left_opnd right_opnd)
    = evalOptr optr (eval left_opnd) (eval right_opnd)

-- just to be different, I put the case split for operators in its
-- own function, evalOptr.  It returns the function for the operator.
-- (You didn't have to do this.)
--
evalOptr :: Fractional p => String -> p -> p -> p
evalOptr "+" = (+)
evalOptr "-" = (-)
evalOptr "*" = (*)
evalOptr "/" = (/)

--------------------------------------------------------------------------------
-- Problem 5: ^0$|^[1-9]\d?\d?(,\d\d\d)*$ 

-- Problem 6: ^([^ \t]+[ \t])*[^ \t]+$

-- Problem 7: ^(w[a-vx-z]{0,3}|[a-vx-z]w[a-vx-z]{0,2}|[a-vx-z]{2}w[a-vx-z]?)$


--------------------------------------------------------------------------------
-- jts test data
-- #1
common ([1..5] ++ [100..105]) ([1..8])
common [2..6] [2..6]
common [1..3] [4..9]
common [] [4..8]
common [1..5] []

------------------------------
-- #2
vals = [LNil, LNode 1 LNil, LNode 1 (LNode 2 LNil), LNode 1 (LNode 2 (LNode 3 LNil))]
vals2 = [LNil, LNode [1] LNil, LNode [1,2] (LNode [] LNil), LNode [3] (LNode [3,4] (LNode [5,6,7] LNil))]

-- test function compares against real show; have to add deriving (Show)
-- to data declaration to do these tests.  (And then you delete it :-)
--
-- try vals = [show x == listShow x | x <- vals]
-- try vals
-- try vals2

------------------------------
-- #3
-- Full:
f1 = Leaf 1
f2 = Node 1 f1 f1
f3 = Node 1 f2 f2
f4 = Node 1 f2 f3
map isFull [f1,f2,f3,f4]

-- Not full:
u1 = Node 1 f1 f2
u2 = Node 1 f2 f1
map isFull [u1,u2]

------------------------------
-- #4
l2p0 = Leaf 2
l3p0 = Leaf 3
l6p0 = Leaf 6
t5p0 = Node "+" l2 l3
t30p0 = Node "*" l6 t5
t2p5 = Node "/" t30 (Leaf 12)
map eval [l2p0,l3p0,l6p0,t5p0,t30p0,t2p5]
