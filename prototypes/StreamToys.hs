{-# LANGUAGE DataKinds #-}              -- to declare the kinds
{-# LANGUAGE KindSignatures #-}         -- (used all over)
{-# LANGUAGE TypeFamilies #-}           -- for declaring operators + sing family
{-# LANGUAGE TypeOperators #-}          -- for declaring operator
{-# LANGUAGE EmptyDataDecls #-}         -- for declaring the kinds

module StreamToys
       -- there will be an export list in this place
       where

import GHC.TypeLits -- freq. operations in types
import Data.Maybe   -- modelling possible bottoms in streams

-- data stream without timing, possible bottoms
data Stream a = Str [Maybe a]

-- We make our lives easy by using lists, a real stream would enforce its
-- infinite nature by not providing a nil constructor [], like so:
-- data Stream a = Str (Maybe a) (Stream a)

instance Show a => Show (Stream a) where
    show (Str xs) = "Str " ++ (showMaybe (take 30 xs)) ++ "..."

showMaybe :: Show a => [Maybe a] -> String
showMaybe [] = ""
showMaybe (Nothing : xs) = "_|_, " ++ showMaybe xs
showMaybe (Just x  : xs) = show x ++ ", " ++ showMaybe xs

-- stream with timing
-- frequencies/speeds represented as type-level nat.s. 
newtype FStream (freq :: Nat) a = FStr (Stream a)

freq :: SingI f => FStream f a -> Sing f
freq _ = sing

freqN :: (SingI f, Num b) => FStream f a -> b
freqN = singToNum . freq

freqI s = freqN s :: Int

singToNum :: Num a => Sing (n :: Nat) -> a
singToNum = fromInteger . fromSing

-- Up to here, these frequencies/speeds are merely (type-level) numbers
-- without semantics. We could, for instance, represent ld(n) instead of n,
-- restricting possible freq.s, but ensuring conversions that otherwise might
-- not be possible.

instance (SingI f, Show a) => Show (FStream f a) where
    show str@(FStr (Str xs)) = "FStr (" ++ fr ++ ") "
                               ++ (showMaybe (take 30 xs)) ++ "..."
        where fr = show (2 ^ freqI str) ++ " Hz"

-- For example, this interpretation would lead to the following: 
example :: FStream 7 Double 
example = FStr (Str ( cycle (map Just [1..32])))
-- is a stream repeating 1 to 32 (as doubles) at frequency 1/2^7 = 1/128. 128
-- elements per second arrive, thus one element per 1/128 sec.

-- type TimeD = Int -- duration, encoded as ld (n)
data TimeD = TimeD Int -- duration 1/n second, encoded as ld (n)

timeD :: Double -> TimeD -- encoding, truncating to nearest lower frequency
timeD d | d <= 0    = error "non-positive duration"
        | d > 1     = error "cannot do > 1 sec" -- :-(
        | otherwise = TimeD (floor_ld (  truncate (1 / d) ))

-- poor man's log_2, truncating decimals.
floor_ld k |   k <= 0  = error "floor_log2: k <=0"
           | otherwise = cl2 0 k
cl2 acc 0 = acc
cl2 acc 1 = acc
cl2 acc k = cl2 (acc+1) (k `div` 2)

-----------------------

-- API draft from meeting, with types

delayS, dropS :: FStream f a -> TimeD -> FStream f a
delayS = undefined -- insert some Nothing elements at the head
dropS  = undefined -- replace some head elements by Nothing elements

-- take elements during a time. Dual to "dropS" above.
takeS :: SingI f => FStream f a -> TimeD -> [Maybe a]
takeS str@(FStr (Str xs)) t = undefined
    where f = freqN str :: Int

repeatS :: (SingI f1, SingI f2, f1 <= f2) => 
          FStream f1 a -> Sing f2 -> FStream f2 a
repeatS str@(FStr (Str xs)) f 
    = FStr $ Str $ concatMap (replicate n) xs
    where -- n = 2^( (singToNum f::Int) - (freqN str :: Int) )
      -- forcefully typing to Int here (type inference cannot figure it out)
          k1 = singToNum f :: Int
          k2 = freqN str -- :: Int
          n = 2 ^ (k1 - k2)
-- eliminating the "sing" parameter by "withSing" (type inference will determine f2)
repeatS_ :: (SingI f1, SingI f2, f1 <= f2) => 
            FStream f1 a -> FStream f2 a
repeatS_ str = withSing (repeatS str)
            
-- sampling a stream, from left or right (underlying general method)
sampleL, sampleR :: (SingI f1, SingI f2, f2 <= f1) =>
                    FStream f1 a -> Sing f2 -> FStream f2 a
sampleL = sampleS listToMaybe
sampleR = sampleS (listToMaybe . reverse)
-- this could also easily express an average sampling, max sampling, etc.

sampleS :: (SingI f1, SingI f2, f2 <= f1) =>
           ([a] -> Maybe a) -> -- function to compute a value from a chunk
           FStream f1 a -> Sing f2 -> FStream f2 a
sampleS select str@(FStr (Str xs)) f
    = FStr (Str (map (select . catMaybes) chunks)) 
    where chunks = map fst (iterate (splitAt n . snd) (splitAt n xs))
          n      = 2^((freqN str :: Int ) - ( singToNum f))
          -- f2 <= f1, so we select 2^(f1-f2) >= 1 element per chunk

-- pointwise arithmetics on streams is easy and straightforward, also
-- including casting to higher/lower precision as desired.
-- A small complication is the Maybe type, plus has to be "lifted".
sumS :: Num a => FStream f a -> FStream f a -> FStream f a
sumS (FStr (Str xs)) (FStr (Str ys)) = FStr (Str (zipWith liftPlus xs ys))
    -- could use Control.Applicative.liftA2, but we do it "on foot" for clarity:
    where liftPlus (Just x) (Just y) = Just (x+y)
          liftPlus    _        _     = Nothing
-- other sum operations, involving repeat to get the maximum frequency, can be
-- defined using the "<=" relation on frequencies... left as an exercise

-- We could think of other operations, like this one: 

-- interleaving two streams at the same frequency, leading to the double
-- frequency. NB a bit ugly with the ld representation. Could be hidden inside
-- other type operators ( 2.*. on frequencies is +1 on type-level Nats).
mixS :: SingI f => FStream f a -> FStream f a -> FStream (f+1) a
mixS (FStr (Str xs)) (FStr (Str ys)) = FStr (Str (interleave xs ys))
    where interleave (x:xs) (y:ys) = x:y:interleave xs ys

example2 = mixS example (FStr (Str (repeat Nothing)))
{- The show instance for this onefails in a standard ghc(i):
*StreamToys> example2

<interactive>:5:1:
    No instance for (SingI Nat (7 + 1)) arising from a use of ‛print’
    In a stmt of an interactive GHCi command: print it
*StreamToys>

The type-nat branch supports it.
-}
