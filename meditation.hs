{-# LANGUAGE GADTs #-}

module TypeTheoryMeditation where

type Symbol = String

type ValueSymbol = Symbol

type TypeSymbol = Symbol

-------------
-- Terms
-------------
data Term = Var ValueSymbol
          | Lambda ValueSymbol TypeSymbol Term
          | Apply Term Term
          deriving (Eq)

instance Show Term where
  show term =
    case term of
         Var x -> x
         Lambda x t innerTerm -> concat
           [ "λ"
           , x
           , ":"
           , t
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
identityTerm = Lambda "x" "a" (Var "x")

oneTerm :: Term
oneTerm = Apply identityTerm (Var "one")

-------------
-- Type
-------------
data Type = Typ TypeSymbol
          | Type :-> Type
          deriving (Eq)
infixr 9 :->

instance Show Type where
  show t =
    case t of
         Typ symbol -> symbol
         (a :-> b)  -> show a ++ " -> " ++ show b

unaryFunction:: Type
unaryFunction= Typ "a" :-> Typ "b"

binaryFunction :: Type
binaryFunction = Typ "a" :-> Typ "b" :-> Typ "c"

-------------
-- Type Assignment & Context
-------------
data TypeAssignment = ValueSymbol ::: Type
                    deriving (Eq)

instance Show TypeAssignment where
  show (v ::: t) = v ++ " : " ++ show t

typeAssignment :: TypeAssignment
typeAssignment = "x" ::: Typ "Nat"

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
ctxType = ["p" ::: Typ "Int", "p" ::: Typ "Nat"] |- Typ "Fraction"

-------------
-- Type Inference
-------------

-- defaultTypeSymbols = [ a..z, aa..zz, aaa..zzz, aaaa .. ]
defaultTypeSymbols :: [TypeSymbol]
defaultTypeSymbols =
  let alphabet :: [String]
      alphabet = (: []) <$> ['a'..'z']
    in (concat . iterate (zipWith (++) alphabet)) alphabet

indexedPrimitiveType :: Int -> [Type]
indexedPrimitiveType n = Typ <$> zipWith (++) defaultTypeSymbols (show <$> repeat n)

next :: [Type] -> [Type]
next (Typ s:_) =
  case read [last s] :: Int of
       n -> indexedPrimitiveType (n + 1)
next _ = error "wrong input to next function"


-- unify :: Type -> Type -> [()]

data InferenceTree = Var' ContextedType
                   | Apply' (ContextedType, InferenceTree) ContextedType (ContextedType, InferenceTree)  
                   | Lambda' ContextedType (ContextedType, InferenceTree)
                   deriving (Show, Eq)

mkInferenceTree :: Term -> InferenceTree
mkInferenceTree = mkInferenceTree' (indexedPrimitiveType 0)

mkInferenceTree' :: [Type] -> Term -> InferenceTree
mkInferenceTree' (a:b:vars) (Apply e1 e2) =
  Apply'
    ([] |- b :-> a, mkInferenceTree' (next vars) e1)
    ([] |- a)
    ([] |- b      , mkInferenceTree' (next (next vars)) e2)
mkInferenceTree' (a:b:c:vars) (Lambda x _ e) =
  Lambda'
    ([] |- b :-> a)  
    ([x ::: c] |- c , mkInferenceTree' (next vars) e)
mkInferenceTree' (a:_) (Var x) = Var' $ [x ::: a] |- a 


-- infer :: Term -> ContextedType
-- infer = infer' defaultTypeSymbols

-- substitute :: Type -> Type -> Context -> Context 
-- substitute _ _ = id

-- infer' :: [Type] -> Term -> ContextedType
-- infer' (a:b:ts) term =
--     case term of
--          Apply f x ->
--            let [fCT,xCT] = map (infer' ts) [f,x]
--              in case typ fCT of
--                      p@(Typ _) ->
--                        let fRecomputedCtx :: Context
--                            fRecomputedCtx = substitute p (a :-> b) (context fCT)
--                            xRecomputedCtx = substitute a (typ xCT) (context xCT)
--                          in 
--                      (_ :-> _) -> context fCT

