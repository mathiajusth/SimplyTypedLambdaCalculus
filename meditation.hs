{-# LANGUAGE GADTs #-}

module TypeTheoryMeditation where

import Data.List (find, partition)

type Symbol = String

type ValueSymbol = Symbol

type TypeSymbol = Symbol

-------------
-- Terms
-------------
data Term = Var ValueSymbol
          | Lambda TypeSymbol Term
          | Apply Term Term
          deriving (Eq)

instance Show Term where
  show term =
    case term of
         Var x -> x
         Lambda x innerTerm -> concat
           [ "λ"
           , x
           , "."
           , show innerTerm
           ]
         Apply f x -> concat 
           [ "[" 
           , show f
           , " " 
           , show x 
           , "]"
           ]

-- Term Examples
identityTerm :: Term
identityTerm = Lambda "x" (Var "x")

oneTerm :: Term
oneTerm = Apply identityTerm (Var "one")

-------------
-- Type
-------------
data Type = Type TypeSymbol
          | Type :-> Type
          deriving (Eq)
infixr 9 :->

instance Show Type where
  show t =
    case t of
         Type symbol -> symbol
         (a :-> b)  -> show a ++ " -> " ++ show b

unaryFunction:: Type
unaryFunction= Type "a" :-> Type "b"

binaryFunction :: Type
binaryFunction = Type "a" :-> Type "b" :-> Type "c"

-------------
-- Type Assignment & Context
-------------
data TypeAssignment = ValueSymbol ::: Type
                    deriving (Eq)

instance Show TypeAssignment where
  show (v ::: t) = v ++ " : " ++ show t

typeAssignment :: TypeAssignment
typeAssignment = "x" ::: Type "Nat"

type Context = [TypeAssignment]

-------------
-- Type with Context
-------------

data ContextedType = ContextedType { context :: Context
                                   , typ    :: Type
                                   }
                   deriving (Eq)

infixr 8 |-
(|-) :: Context -> Type -> ContextedType
ctx |- t = ContextedType { context = ctx
                         , typ     = t
                         }

instance Show ContextedType where
  show ctype = show (context ctype) ++ " |- " ++ show (typ ctype)

ctxType :: ContextedType
ctxType = ["p" ::: Type "Int", "p" ::: Type "Nat"] |- Type "Fraction"

-------------
-- Type Inference
-------------

-- defaultTypeSymbols = [ a..z, aa..zz, aaa..zzz, aaaa.. ]
defaultTypeSymbols :: [TypeSymbol]
defaultTypeSymbols =
  let alphabet :: [String]
      alphabet = (: []) <$> ['a'..'z']
    in (concat . iterate (zipWith (++) alphabet)) alphabet

-- indexedPrimitiveType 1 = [ a1..z1, aa1..zz1, aaa1..zzz1, aaaa1.. ]
indexedPrimitiveType :: Int -> [Type]
indexedPrimitiveType n = Type <$> zipWith (++) defaultTypeSymbols (show <$> repeat n)

-- next [ a1..z1, aa1..zz1, aaa1.. ] = [ a2..z2, aa2..zz2, aaa2... ]
-- next [ c1..z1, aa1..zz1, aaa1.. ] = [ a2..z2, aa2..zz2, aaa2... ]
next :: [Type] -> [Type]
next (Type s:_) =
  case read [last s] :: Int of
       n -> indexedPrimitiveType (n + 1)
next _ = error "wrong input to next function"

data Equality = Type :=: Type
                        deriving (Show,Eq)

type Equalities = [Equality]

combine :: Context -> (Context, Equalities) -> (Context, Equalities)
combine [] ctx = ctx
combine (ta@(x ::: a):tas) (ctx,eqs) =
  case find (\y -> let (z ::: _) = y in x == z) ctx of
       Nothing -> combine tas (ta:ctx,eqs)
       Just (_ ::: b)  -> combine tas (ctx, a:=:b : eqs)

infer :: Term -> (ContextedType, Equalities)
infer = infer' (indexedPrimitiveType 0) 

infer' :: [Type] -> Term -> (ContextedType, Equalities)
infer' [] _ = error "list of types provided to infer' is empty"
infer' (t:_) (Var x) = ([x ::: t] |- t, []) 
infer' (t:ts) (Apply f e) =
  let (ContextedType{context = ctxF, typ = typF}, eqF) =  infer' (next ts) f
      (ContextedType{context = ctxE, typ = typE}, eqE) =  infer' (next . next $ ts) e
      (newCtx, ctxEqs) = combine ctxF (ctxE, [])
      in (newCtx |- t, typF :=: (typE :-> t) : (ctxEqs ++ eqE ++ eqF))
infer' (t:ts) (Lambda x e) = 
  let (ContextedType{context = ctxE, typ = typE}, eqE) =  infer' (next ts) e
    in case partition (\y -> let (z ::: _) = y in x == z) ctxE of
            ([],_)               -> (ctxE    |- t :-> typE, eqE)
            ([_ ::: b], restCtx) -> (restCtx |- b :-> typE, eqE)
            _ -> error $ "ERROR: Context " ++ show ctxE ++ "has more than one "
