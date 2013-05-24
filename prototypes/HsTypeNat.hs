{-# LANGUAGE DataKinds #-}              -- to declare the kinds
{-# LANGUAGE KindSignatures #-}         -- (used all over)
{-# LANGUAGE TypeFamilies #-}           -- for declaring operators + sing family
{-# LANGUAGE TypeOperators #-}          -- for declaring operator
{-# LANGUAGE EmptyDataDecls #-}         -- for declaring the kinds
{-# LANGUAGE GADTs #-}                  -- for examining type nats
{-# LANGUAGE PolyKinds #-}              -- for Sing family
{-# LANGUAGE UndecidableInstances #-}   -- for a bunch of the instances
{-# LANGUAGE FlexibleInstances #-}      -- for kind parameters
{-# LANGUAGE FlexibleContexts #-}       -- for kind parameters
{-# LANGUAGE ScopedTypeVariables #-}    -- for kind parameters
{-# LANGUAGE MultiParamTypeClasses #-}  -- for <=, singRep, SingE

module HsTypeNat where

import GHC.TypeLits

-- example code playing around with type-level literal nats:

-- array with its size as a type (kind: Nat)
newtype Arr (size :: Nat) a = C [a]
    deriving (Eq,Show)

arrSize :: SingI n => Arr n a -> Sing n -- size returned as a type
arrSize _ = sing  -- sing is the singleton value inhabiting each Sing type

-- index type with maximum size
newtype Ix (size :: Nat) = I Int
    deriving (Eq,Ord,Show)

-- desired: cannot produce index bigger than max size
mkIx :: Sing size -> Int -> Ix size -- type-level size
mkIx size n | n < 0     = error "negative index"
            | n < limit = I n
            | otherwise = error ("index too large (limit " ++ show limit ++ ")")
       where limit = singToNum size -- value-level size

singToNum :: Num a => Sing (n :: Nat) -> a
singToNum = fromInteger . fromSing

-- safely generating all valid indexes
indexes :: SingI n => Arr n a -> [ Ix n ]
indexes arr = [ I i | i <- [0..limit-1]]
    where limit = singToNum (arrSize arr)

-- creating arrays of given size
iota_ :: Sing n -> Arr n Integer
iota_ size = C [ 0..singToNum size - 1 ]

iota :: (SingI n) => Arr n Integer
iota = withSing iota_

-- adding pointwise, controlling length
addArr :: (Num a) => Arr n a -> Arr n a -> Arr n a
addArr (C l1) (C l2) = C (zipWith (+) l1 l2)

{-
*HaskellTypeNats2> :set -XDataKinds
*HaskellTypeNats2> let i1 = iota :: Arr 12 Integer
*HaskellTypeNats2> let i2 = iota :: Arr 11 Integer
*HaskellTypeNats2> addArr i1 i2

<interactive>:18:11:
    Couldn't match type `11' with `12'
    Expected type: Arr 12 Integer
      Actual type: Arr 11 Integer
    In the second argument of `addArr', namely `i2'
    In the expression: addArr i1 i2
    In an equation for `it': it = addArr i1 i2
-}

-- cutting an array short, or extending it (a casting operation)
cut_ :: Arr m a -> Sing n -> Arr n a
cut_ (C xs) size = C (take n xs)
    where n = singToNum size

cut :: (SingI n) => Arr m a -> Arr n a
cut a = withSing (cut_ a)
{-
*HaskellTypeNats2> cut i1 :: Arr 11 Integer
C [0,1,2,3,4,5,6,7,8,9,10]
*HaskellTypeNats2> addArr (cut i1) i2
C [0,2,4,6,8,10,12,14,16,18,20]
*HaskellTypeNats2> 
-}

{- Note the bug: 
*HaskellTypeNats2> addArr i1 (cut i2)
C [0,2,4,6,8,10,12,14,16,18,20]
-}
-- cannot just do nothing if already shorter than required!
-- better: extend the array by something (for instance, repeat last element) 
cast_ :: Arr m a -> Sing n -> Arr n a
cast_ (C xs) size = C (take n (xs ++ repeat x))
    where n = singToNum size
          x = last xs

cast :: (SingI n) => Arr m a -> Arr n a
cast a = withSing (cast_ a)

addArrL :: (Num a, SingI n) =>
              Arr n a -> Arr m a -> Arr n a
addArrL a1 a2 = addArr a1 (cast a2)

-- definition for minNat (using a class, type family variant seemingly
-- cannot specify the class context which is essential here)

class MinNatC (n::Nat) (m::Nat) where
    type MinNat (n::Nat) (m::Nat) :: Nat

instance (n <= m) => MinNatC n m where
    type MinNat n m = n

-- TODO: THIS DOES NOT WORK!
addArrMin :: (Num a, SingI n, SingI m) =>
             Arr n a -> Arr m a -> Arr (MinNat n m) a
addArrMin a1 a2 = -- addArr (cast a1) (cast a2)
                  error "addArrMin does not work!"

------------------------------------------------------
-- now for something which requires constraint-solving

-- append: result length is sum of both
appendArr :: Arr n a -> Arr m a -> Arr (n+m) a
appendArr (C xs) (C ys) = C (xs ++ ys)

(.:.) :: a -> Arr n a -> Arr (n+1) a
x .:. (C xs) = C (x:xs)

shouldTypeCheck x arr  -- (n+1)+n == n+n+1
  = if appendArr (x .:. arr) arr == x .:. (appendArr arr arr)
       then appendArr ( x .:. arr) arr else error "should not happen"
shouldBeFineAsWell x arr -- n+1+n+1 = (n+1)+(n+1)
  = let xarr = C [x]::Arr 1 Int -- use "2" here: type checker will complain
        app  = x .:. arr
    in if appendArr xarr (appendArr arr (appendArr xarr arr)) == appendArr app app
        then appendArr app app else error "should not happen"

-------------------------------------
-- willFail x arr = x .:. arr == arr -- not just false, but a type error
-------------------------------------

-- we cannot usefully type a "replicate" function (no "toSing")
-- replicateArr :: Int -> Arr n a -> Arr ??*n a
replicateArr 0 arr = error "replicate 0"
replicateArr 1 arr = arr
replicateArr k arr 
  | k <= 0    = error "replicate: non-positive argument"
  | k == 1    = arr
  | otherwise = appendArr arr (replicateArr (k-1) arr)
-- ghci infers type (Eq a, Num a) => a -> Arr 0 b -> Arr 0 b, smart!

-- not even if the information is available at type level...
replicateArr2 :: Sing n -> Arr m a -> Arr (n*m) a
replicateArr2 l (C xs)
    = C (concat (replicate l_int xs)) 
  where l_int    = singToNum l -- Int

appendAllArr [] = error "no array"
appendAllArr [arr] = arr 
appendAllArr (arr:rest) = appendArr arr (appendAllArr rest)


-- type can be checked when we know the replicate argument value
tripleArr :: Arr n a -> Arr (3*n) a
tripleArr (C xs) = C (concat (replicate 3 xs))

shouldBeOK arr = if appendArr arr (appendArr arr arr) == tripleArr arr
                    then tripleArr arr else error "should not happen"
-- inferred context contains a tautology (3*n) ~ t1, (n+t) ~ t1, (n+n) ~ t

andEatThis x arr = if tripleArr app /= appendArr xxx (tripleArr arr)
                      then tripleArr app else error "should not happen"
  where app = x .:. arr
        xxx = C [x,x,x] :: Arr 3 Integer

---------------------------------------------
-- back to useful things:

mapArr :: (a -> b) -> Arr n a -> Arr n b
mapArr f (C xs) = C (map f xs)
