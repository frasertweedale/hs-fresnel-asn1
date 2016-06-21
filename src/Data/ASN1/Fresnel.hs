-- This file is part of fresnel-asn1
-- Copyright (C) 2015  Fraser Tweedale
--
-- fresnel is free software: you can redistribute it and/or modify
-- it under the terms of the GNU Affero General Public License as published by
-- the Free Software Foundation, either version 3 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU Affero General Public License for more details.
--
-- You should have received a copy of the GNU Affero General Public License
-- along with this program.  If not, see <http://www.gnu.org/licenses/>.

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.ASN1.Fresnel
  (
  -- | Primitive types
    boolean
  , integer
  , octetString
  , oid
  , generalizedTime
  , string
  , enumerated

  -- | Products and collections
  , sequence
  , sequenceOf
  , sequenceOf1
  , setOf

  -- | Tagging
  , tag
  , application

  -- | Constraint prisms
  , constrain
  , natural
  , boundedIntegral

  -- | Encoding and decoding
  , encode
  , decode

  -- | Re-exports
  , module Data.ASN1.BinaryEncoding
  , module Data.ASN1.Types
  , module Data.Fresnel
  )  where

import Prelude hiding (sequence)
import Control.Monad ((>=>))

import Control.Lens hiding (sequenceOf)
import Data.ASN1.BinaryEncoding
import Data.ASN1.BitArray (BitArray)
import Data.ASN1.Encoding
import Data.ASN1.Types
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as L
import Data.Fresnel
import Data.List.NonEmpty (NonEmpty)
import Data.Hourglass (DateTime, TimezoneOffset)
import qualified Data.Set as S
import Numeric.Natural (Natural)
import Safe (toEnumMay)

{-# ANN module ("HLint: ignore Use import/export shortcut" :: String) #-}

_Boolean :: Prism' ASN1 Bool
_Boolean = prism Boolean f where
  f (Boolean b) = Right b
  f z = Left z

_Integer :: Prism' ASN1 Integer
_Integer = prism IntVal f where
  f (IntVal n) = Right n
  f z = Left z

_Enumerated :: Prism' ASN1 Integer
_Enumerated = prism Enumerated f where
  f (Enumerated n) = Right n
  f z = Left z

_String :: Prism' ASN1 ASN1CharacterString
_String = prism ASN1String f where
  f (ASN1String s) = Right s
  f z = Left z

_BitString :: Prism' ASN1 BitArray
_BitString = prism BitString f where
  f (BitString bits) = Right bits
  f z = Left z

_OctetString :: Prism' ASN1 B.ByteString
_OctetString = prism OctetString f where
  f (OctetString bs) = Right bs
  f z = Left z

_OID :: Prism' ASN1 OID
_OID = prism OID f where
  f (OID a) = Right a
  f z = Left z

data GeneralizedTime = GeneralizedTime DateTime (Maybe TimezoneOffset)

_GeneralizedTime :: Prism' ASN1 GeneralizedTime
_GeneralizedTime = prism g f where
  g (GeneralizedTime t z) = ASN1Time TimeGeneralized t z
  f (ASN1Time TimeGeneralized t z) = Right (GeneralizedTime t z)
  f z = Left z

boolean :: Cons s s ASN1 ASN1 => Grammar s Bool
boolean = _Boolean <<$>> _Cons

integer :: Cons s s ASN1 ASN1 => Grammar s Integer
integer = _Integer <<$>> _Cons

octetString :: Cons s s ASN1 ASN1 => Grammar s B.ByteString
octetString = _OctetString <<$>> _Cons

oid :: Cons s s ASN1 ASN1 => Grammar s OID
oid = _OID <<$>> _Cons

generalizedTime :: Cons s s ASN1 ASN1 => Grammar s GeneralizedTime
generalizedTime = _GeneralizedTime <<$>> _Cons

enumerated :: (Cons s s ASN1 ASN1, Bounded a, Enum a) => Grammar s a
enumerated = _Enumerated . boundedIntegral . prism' fromEnum toEnumMay <<$>> _Cons

-- | Build a constraint prism given a predicate
--
constrain :: Prism' a a -> (a -> Bool) -> Prism' a a
constrain p f = withPrism p $ \as sesa ->
  prism as (sesa >=> (\a -> if f a then Right a else Left a))

-- | Constrain to natural numbers
--
natural :: Integral a => Prism' a Natural
natural = prism fromIntegral f where
  f n
    | n >= 0 = Right (fromIntegral n)
    | otherwise = Left n

-- | Constrain to bounds of target type
--
boundedIntegral :: forall a b. (Integral a, Integral b, Bounded b) => Prism' a b
boundedIntegral = prism fromIntegral f where
  f n =
    if n >= fromIntegral (minBound :: b) && n <= fromIntegral (maxBound :: b)
    then Right (fromIntegral n)
    else Left n

sequence :: Cons s s ASN1 ASN1 => Grammar s a -> Grammar s a
sequence = between (literal (Start Sequence)) (literal (End Sequence))

inseq :: Cons s s ASN1 ASN1 => Grammar s a -> Grammar s a
inseq = between (literal (Start Sequence)) (literal (End Sequence))

inset :: Cons s s ASN1 ASN1 => Grammar s a -> Grammar s a
inset = between (literal (Start Set)) (literal (End Set))

sequenceOf :: Cons s s ASN1 ASN1 => Grammar s a -> Grammar s [a]
sequenceOf g = inseq (many g)

sequenceOf1 :: Cons s s ASN1 ASN1 => Grammar s a -> Grammar s (NonEmpty a)
sequenceOf1 g = inseq (many1 g)

setOf :: (Cons s s ASN1 ASN1, Ord a) => Grammar s a -> Grammar s (S.Set a)
setOf g = inset (iso S.fromList S.toList <<$>> many g)

tagOfClass
  :: Cons s s ASN1 ASN1
  => ASN1Class -> Int -> Grammar s a -> Grammar s a
tagOfClass cls n g =
  let tag' = Container cls n
  in between (literal (Start tag')) (literal (End tag')) g

tag, application :: Cons s s ASN1 ASN1 => Int -> Grammar s a -> Grammar s a
tag = tagOfClass Data.ASN1.Types.Context
application = tagOfClass Application

string :: Cons s s ASN1 ASN1 => ASN1StringEncoding -> Grammar s B.ByteString
string enc = prism f g <<$>> _Cons where
  f a = ASN1String (ASN1CharacterString enc a)
  g (ASN1String (ASN1CharacterString enc' a)) | enc == enc' = Right a
  g s = Left s


encode
  :: (Cons [ASN1] [ASN1] ASN1 ASN1, ASN1Encoding e)
  => e -> Grammar [ASN1] a -> a -> L.ByteString
encode e g a = encodeASN1 e (Data.Fresnel.print g a)

decode
  :: (Cons [ASN1] [ASN1] ASN1 ASN1, ASN1Decoding e)
  => e -> Grammar [ASN1] a -> L.ByteString -> Maybe a
decode e g s = either (const Nothing) Just (decodeASN1 e s) >>= parse g
