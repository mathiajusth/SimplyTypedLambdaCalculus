{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}

module TypeTheoryMeditation where

import Data.List (find, partition, groupBy, nub)
import Data.Tuple.Extra (second)
import Data.Foldable (toList)
import Control.Monad (ap)

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

term1 :: Term
term1 = Apply
          (Lambda "f" $ Lambda "x" $ Apply (Var "f") (Var "x"))
          (Lambda "y" $ Var "y")

-------------
-- Type
-------------
data FreeArrowType a = Type a
                     | FreeArrowType a :-> FreeArrowType a
          deriving (Eq)
infixr 9 :->

concatFAT :: forall a. FreeArrowType (FreeArrowType a) -> FreeArrowType a
concatFAT (a :-> b) = concatFAT a :-> concatFAT b
concatFAT (Type (Type x)) = Type x
concatFAT (Type (y :-> z)) = y :-> z

instance Functor FreeArrowType where
  fmap :: (a -> b) -> FreeArrowType a -> FreeArrowType b
  fmap f (p :-> q) = fmap f p :-> fmap f q
  fmap f (Type x) = Type $ f x

instance Applicative FreeArrowType where
  pure = Type
  (<*>) = ap

instance Monad FreeArrowType where
  return :: forall a. a -> FreeArrowType a
  return = pure
  (>>=) :: forall a b. FreeArrowType a -> (a -> FreeArrowType b) -> FreeArrowType b
  mx >>= mf = concatFAT (mf <$> mx)

instance Foldable FreeArrowType where
  foldMap f (Type x) = f x
  foldMap f (a :-> b) = foldMap f a `mappend` foldMap f b

type Type = FreeArrowType String 

instance Show a => Show (FreeArrowType a) where
  show t =
    case t of
         Type symbol -> show symbol
         (a :-> b)  -> show a ++ " :-> " ++ show b

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

combineCtxs :: Context -> (Context, [Equation]) -> (Context, [Equation])
combineCtxs [] ctx = ctx
combineCtxs (ta@(x ::: a):tas) (ctx,eqs) =
  case find (\y -> let (z ::: _) = y in x == z) ctx of
       Nothing -> combineCtxs tas (ta:ctx,eqs)
       Just (_ ::: b)  -> combineCtxs tas (ctx, a:=:b : eqs)

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

--
-- TYPE VARIABLES
--

defaultTypeSymbols :: [TypeSymbol]
-- defaultTypeSymbols = [ a..z, aa..zz, aaa..zzz, aaaa.. ]
defaultTypeSymbols =
  let alphabet :: [String]
      alphabet = (: []) <$> ['a'..'z']
    in (concat . iterate (zipWith (++) alphabet)) alphabet

indexedPrimitiveType :: Int -> [Type]
-- indexedPrimitiveType 1 = [ a1..z1, aa1..zz1, aaa1..zzz1, aaaa1.. ]
indexedPrimitiveType n = Type <$> zipWith (++) defaultTypeSymbols (show <$> repeat n)

next :: [Type] -> [Type]
-- next [ a1..z1, aa1..zz1, aaa1.. ] = [ a2..z2, aa2..zz2, aaa2... ]
-- next [ c1..z1, aa1..zz1, aaa1.. ] = [ a2..z2, aa2..zz2, aaa2... ]
next (Type s:_) =
  case read [last s] :: Int of
       n -> indexedPrimitiveType (n + 1)
next _ = error "wrong input to next function"

--
-- INFERENCE
--

infer :: Term -> (ContextedType, [Equation])
infer = second (concatMap simplifyEq) . infer' (indexedPrimitiveType 0) 

infer' :: [Type] -> Term -> (ContextedType, [Equation])
infer' [] _ = error "list of types provided to infer' is empty"
infer' (t:_) (Var x) = ([x ::: t] |- t, []) 
infer' (t:ts) (Apply f e) =
  let (ContextedType{context = ctxF, typ = typF}, eqF) =  infer' (next ts) f
      (ContextedType{context = ctxE, typ = typE}, eqE) =  infer' (next . next $ ts) e
      (newCtx, ctxEqs) = combineCtxs ctxF (ctxE, [])
      in (newCtx |- t, typF :=: (typE :-> t) : (ctxEqs ++ eqE ++ eqF))
infer' (t:ts) (Lambda x e) = 
  let (ContextedType{context = ctxE, typ = typE}, eqE) =  infer' (next ts) e
    in case partition (\y -> let (z ::: _) = y in x == z) ctxE of
            ([],_)               -> (ctxE    |- t :-> typE, eqE)
            ([_ ::: b], restCtx) -> (restCtx |- b :-> typE, eqE)
            _ -> error $ "ERROR: Context " ++ show ctxE ++ "has more than one type assignemnts for the same variable"

-- TODO - MOVE to Utils
eqBy :: Eq b => (a -> b) -> a -> a -> Bool
eqBy f x y = f x == f y

--
-- EQUATIONS
--

data Equation = Type :=: Type
                        deriving (Show,Eq)


swap :: Equation -> Equation
swap (p :=: r) = r :=: p

simplifyEq :: Equation -> [Equation]
simplifyEq eq  = filter (not . isTrivial) $
                   case eq of
                        Type _    :=:  _        -> [eq]
                        _         :=:  Type _   -> [swap eq]
                        (o :-> p) :=: (r :-> q) -> simplifyEq (o :=: r) ++ simplifyEq (p :=: q) 


leftHand :: Equation -> Type
leftHand (a :=: _) = a

rightHand :: Equation -> Type
rightHand (_ :=: b) = b

eqLeft :: Equation -> Equation -> Bool
eqLeft = eqBy leftHand

eqRight :: Equation -> Equation -> Bool
eqRight = eqBy rightHand

isTrivial :: Equation -> Bool
isTrivial eq = leftHand eq == rightHand eq

-- newtype SpecificationTree  = SpecificationTree{iso:: (String, [FreeArrowType SpecificationTree])}
--   deriving (Show, Eq)

-- shorterOrEqual :: Int -> SpecificationTree -> Bool
-- shorterOrEqual n pt = case iso pt of
--                             (_,[]) -> n >= 0 || error ""
--                             (_, subs) -> case n of
--                                                   0 -> False
--                                                   _ -> all (shorterOrEqual $ n - 1) (concatMap toList subs)


-- mkSpecificationTree :: [Equation] -> String -> SpecificationTree
-- mkSpecificationTree eqs s =
--   SpecificationTree $ (s,) $
--     ( map (fmap (mkSpecificationTree eqs) . rightHand)
--     . filter (\eq -> leftHand eq == Type s)
--     ) eqs

-- areCyclic :: [Equation] -> Bool
-- areCyclic eqs = ( not
--                 . all (shorterOrEqual $ length eqs)
--                 . map (mkSpecificationTree eqs)
--                 . nub
--                 . map ( \a -> case a of
--                                    Type s -> s
--                                    _ -> error "left hands side of equation should be a simple type"
--                       )
--                 . map leftHand
--                 ) eqs

--
-- EQUALITY
--

data Specification m a =
  Specification { origin :: a
                , target :: m a
                }
                  deriving (Eq)

-- subs :: String -> Type -> Specification
-- subs s = Specification (Type s)

instance (Show a, Show (m a)) => Show (Specification m a) where
  show (Specification s a) = show s ++ " ==> " ++ show a

isTrivialSpecification :: (Monad m, Eq (m a)) => Specification m a -> Bool
isTrivialSpecification (Specification a b) = return a == b 

-- type Equality = [Specification Char FreeArrowType]

-- newtype SpecificationTree a = SpecificationTree (Specification a Inner)

newtype SpecificationTree :: (* -> *) -> * -> * where
  SpecificationTree :: Specification (SpecForest m) a -> SpecificationTree m a
--   :: Specification a (List . m . SpecificationTree m)
--   if type constructors could be composed

newtype SpecForest :: (* -> *) -> * -> * where
  SpecForest :: forall a m. [m (SpecificationTree m a)] -> SpecForest m a

newtype R l m a = MkR (l (Compose m (R l m)) a)
newtype ST a = MkSt (R Specification (Compose [] FreeArrowType) a)

-- data ST :: (* -> *) where
--   MkST :: R Specification (Compose [] FreeArrowType) a -> ST a

-- type ST = R Specification (Compose [] FreeArrowType)

newtype Compose :: (* -> *) -> (* -> *) -> (* -> *) where
  Compose :: m (n a) -> Compose m n a
  

type Composition a = [FreeArrowType a]

data DecisionTree :: * -> * where
  Leaf :: forall a. a -> DecisionTree a
  (:|)   :: forall a. DecisionTree a -> DecisionTree a -> DecisionTree a
  (:&)  :: forall a. DecisionTree a -> DecisionTree a -> DecisionTree a
  deriving (Show,Eq)

-- mkSpecificationTree :: [Equation] -> String -> SpecificationTree
-- mkSpecificationTree eqs s =
--   SpecificationTree $ (s,) $
--     ( map (fmap (mkSpecificationTree eqs) . rightHand)
--     . filter (\eq -> leftHand eq == Type s)
--     ) eqs

-- instance Functor SpecificationTree where
--   fmap :: forall a b. (a -> b) ->  SpecificationTree a -> SpecificationTree b
--   fmap f mx = 


----------
-- OLD
----------
-- newtype SpecificationTree  = SpecificationTree{iso:: (String, [FreeArrowType SpecificationTree])}
--   deriving (Show, Eq)

-- shorterOrEqual :: Int -> SpecificationTree -> Bool
-- shorterOrEqual n pt = case iso pt of
--                             (_,[]) -> n >= 0 || error ""
--                             (_, subs) -> case n of
--                                                   0 -> False
--                                                   _ -> all (shorterOrEqual $ n - 1) (concatMap toList subs)


-- mkSpecificationTree :: [Equation] -> String -> SpecificationTree
-- mkSpecificationTree eqs s =
--   SpecificationTree $ (s,) $
--     ( map (fmap (mkSpecificationTree eqs) . rightHand)
--     . filter (\eq -> leftHand eq == Type s)
--     ) eqs

-- areCyclic :: [Equation] -> Bool
-- areCyclic eqs = ( not
--                 . all (shorterOrEqual $ length eqs)
--                 . map (mkSpecificationTree eqs)
--                 . nub
--                 . map ( \a -> case a of
--                                    Type s -> s
--                                    _ -> error "left hands side of equation should be a simple type"
--                       )
--                 . map leftHand
--                 ) eqs

-- toSpecification :: Equation -> [Specification]
-- toSpecification eq  = filter (not . isTrivialSpecification) $
--                case eq of
--                     Type s    :=:  a        -> [Specification s a]
--                     a         :=:  Type s   -> [Specification s a]
--                     (o :-> p) :=: (r :-> q) -> toSpecification (o :=: r) ++ toSpecification (p :=: q) 

-- toEquality :: [Equation] -> Equality
-- toEquality eqs = if  areCyclic eqs
--                      then error "Unsolvable"
--                      else concatMap toSpecification eqs
