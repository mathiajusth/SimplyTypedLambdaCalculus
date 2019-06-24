{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExplicitForAll #-}

module Unification where

---------
-- Typ
---------

data Typ :: * where
  Typ :: Char -> Typ
  (:->) :: Typ -> Typ -> Typ
  deriving (Show,Eq)

---------
-- DecisionTree
---------

data DecisionTree :: * -> * where
  Leaf :: forall a. a -> DecisionTree a
  Or   :: forall a. DecisionTree a -> DecisionTree a -> DecisionTree a
  And  :: forall a. DecisionTree a -> DecisionTree a -> DecisionTree a
  deriving (Show,Eq)


(.&) :: forall a. DecisionTree a -> DecisionTree a -> DecisionTree a
(.&) = And

-- (.|) :: forall a. DecisionTree a -> DecisionTree a -> DecisionTree a
-- (.|) = Or

---------
-- Specify
---------

data Specification = Specify Typ Typ
  deriving (Show,Eq)

specify :: Char -> Typ -> Specification
specify i = Specify (Typ i)

---------
-- Unification
---------

eq :: Typ -> Typ -> DecisionTree Specification
eq t1 t2 = case (t1,t2) of
                (Typ i  , Typ j  ) -> Leaf (specify i t2) .| Leaf (specify j t1)
                (Typ i  , _ :-> _) -> Leaf (specify i t2)
                (_ :-> _, Typ j  ) -> Leaf (specify j t1)
                (_ :-> _, _ :-> _) -> unify t1 t2 

unify :: Typ -> Typ -> DecisionTree Specification
unify t1 t2 = case (t1, t2) of
                (o :-> p, r :-> q) -> unify o r .& unify p q 
                _ -> eq t1 t2
                -- (Typ _  , Typ _  ) -> eq t1 t2
                -- (Typ _  , _ :-> _) -> eq t1 t2
                -- (_ :-> _, Typ _  ) -> eq t1 t2

t1 = Typ 'a' :-> Typ 'b'
t2 = (Typ 'b' :-> Typ 'c') :-> Typ 'd'

-- Result
-- And
--   (Leaf
--     (Specify
--       (Typ 'a') 
--       ((:->) (Typ 'b') (Typ 'c'))))
--   (Or
--     (Leaf
--       (Specify
--         (Typ 'b')
--         (Typ 'd')))
--     (Leaf
--       (Specify
--         (Typ 'd')
--         (Typ 'b'))))

