-- The grammar
-- The second Int argument for TmVar: 
--     contains the total length of the context in which the variable occurs
--     as a consistency check
-- The String argument:
--     as a hint for the name of the bound variable
--     for printing bound variables instead of in nameless form
data Term = TmVar Int Int
          | TmAbs String Term
          | TmApp Term Term
     deriving (Show, Eq)

data Binding = Binding String
     deriving (Show, Eq)

data Context = Nil
             | Cons (String, Binding) Context
     deriving (Show, Eq)

ctxLength :: Context -> Int
ctxLength Nil = 0
ctxLength (Cons x y) = 1 + (ctxLength y)

nthCtx :: Context -> Int -> (String, Binding)
nthCtx Nil _ = ("", Binding "")
nthCtx (Cons x y) n
       | n == 0    = x
       | otherwise = nthCtx y (n - 1)

namingCtx :: String -> Int
namingCtx "x" = 4
namingCtx "y" = 3
namingCtx "z" = 2
namingCtx "a" = 1
namingCtx "b" = 0

namingCtxR :: Int -> String
namingCtxR 4 = "x"
namingCtxR 3 = "y"
namingCtxR 2 = "z"
namingCtxR 1 = "a"
namingCtxR 0 = "b"

-- Looks up the string name of a variable from its indix
idx2name :: Context -> Int -> String
idx2name ctx x
         | ctxLength ctx > x = fst (nthCtx ctx x)
         | otherwise         = namingCtxR (x - (ctxLength ctx))






printTm :: Context -> Term -> IO ()
--printTm ctx (TmVar x n)
--        | ctxLength ctx == n =
printTm _ _ = putStrLn "yaya"

bnd = Binding "lala"
ctx = Cons ("lala", bnd) Nil
ctx2 = Cons ("lala", bnd) ctx

main = print (ctxLength ctx2)
