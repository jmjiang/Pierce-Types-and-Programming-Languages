-- The grammar
data Term = TmTrue
          | TmFalse
          | TmIf Term Term Term
          | TmZero
          | TmSucc Term
          | TmPred Term
          | TmIsZero Term
      deriving (Show, Eq)



-- Checks whether a term is a numeric value
isNumericVal :: Term -> Bool
isNumericVal TmZero = True
isNumericVal (TmSucc x) = isNumericVal x
isNumericVal _ = False

-- Checks whether a term is a value
isVal :: Term -> Bool
isVal TmTrue = True
isVal TmFalse = True
isVal x
      | isNumericVal x == True = True
      | otherwise              = False

-- One-step evaluation rules
eval1 :: Term -> Term
eval1 (TmIf TmTrue y _) = y
eval1 (TmIf TmFalse _ z) = z
eval1 (TmIf x y z) = TmIf (eval1 x) y z
eval1 (TmSucc x) = TmSucc (eval1 x)
eval1 (TmPred TmZero) = TmZero
eval1 (TmPred (TmSucc x)) | isVal x == True = x
eval1 (TmPred x) = TmPred (eval1 x)
eval1 (TmIsZero TmZero) = TmTrue
eval1 (TmIsZero (TmSucc x)) | isVal x == True = TmFalse
eval1 (TmIsZero x) = TmIsZero (eval1 x)
eval1 x = x

-- Takes a term and finds its normal form by repeatedly calling eval1
eval :: Term -> Term
eval x
     | eval1 x == x = x
     | otherwise    = eval (eval1 x)



-- Checks if a term is receded by TmSucc
succPre :: Term -> Bool
succPre (TmSucc x) = True
succPre _ = False

-- Get the rest of term except for the first TmSucc
succRemove :: Term -> Term
succRemove (TmSucc x) = x
succRemove x = x

-- Multi-steps evaluation rules
evalM :: Term -> Term
evalM (TmIf x y z)
      | evalM x == TmTrue = y
      | evalM x == TmFalse = z
evalM (TmSucc x) | isVal (evalM x) = TmSucc (evalM x)
evalM (TmPred x)
      | evalM x == TmZero         = TmZero
      | succPre (evalM x) == True = succRemove (evalM x)
evalM (TmIsZero x)
      | evalM x == TmZero         = TmTrue
      | succPre (evalM x) == True = TmFalse
evalM x = x



-- test = TmTrue
-- test = TmFalse
-- test = TmIf (TmIsZero (TmSucc TmZero)) TmZero (TmSucc TmZero)
-- test = TmZero
-- test = TmSucc (TmSucc (TmPred TmZero))
test = TmPred (TmPred (TmSucc TmZero))
test2 = TmIsZero test
array = [1,2,3,5,7,9,10,11,14,16,20]
main = print (evalM test)
