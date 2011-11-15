{-# LANGUAGE CPP #-}
module Language.Haskell.TH.Extras where

import Control.Monad
import Data.Generics
import Data.Maybe
import Language.Haskell.TH

intIs64 :: Bool
intIs64 = toInteger (maxBound :: Int) > 2^32

replace :: (a -> Maybe a) -> (a -> a)
replace = ap fromMaybe

namesBoundInPat :: Pat -> [Name]
namesBoundInPat (VarP name)             = [name]
namesBoundInPat (TupP pats)             = pats >>= namesBoundInPat
namesBoundInPat (ConP _ pats)           = pats >>= namesBoundInPat
namesBoundInPat (InfixP p1 _ p2)        = namesBoundInPat p1 ++ namesBoundInPat p2
namesBoundInPat (TildeP pat)            = namesBoundInPat pat
namesBoundInPat (AsP name pat)          = name : namesBoundInPat pat
namesBoundInPat (RecP _ fieldPats)      = map snd fieldPats >>= namesBoundInPat
namesBoundInPat (ListP pats)            = pats >>= namesBoundInPat
namesBoundInPat (SigP pat _)            = namesBoundInPat pat

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 612
namesBoundInPat (BangP pat)             = namesBoundInPat pat
#endif

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 700
namesBoundInPat (ViewP _ pat)           = namesBoundInPat pat
#endif

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
namesBoundInPat (UnboxedTupP pats)      = pats >>= namesBoundInPat
#endif

namesBoundInPat _                       = []


namesBoundInDec :: Dec -> [Name]
namesBoundInDec (FunD name _)                       = [name]
namesBoundInDec (ValD pat _ _)                      = namesBoundInPat pat
namesBoundInDec (DataD _ name _ _ _)                = [name]
namesBoundInDec (NewtypeD _ name _ _ _)             = [name]
namesBoundInDec (TySynD name _ _)                   = [name]
namesBoundInDec (ClassD _ name _ _ _)               = [name]
namesBoundInDec (ForeignD (ImportF _ _ _ name _))   = [name]

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 612
namesBoundInDec (FamilyD _ name _ _)                = [name]
#endif

namesBoundInDec _                                   = []

genericalizeName :: Name -> Name
genericalizeName = mkName . nameBase

-- Genericalize all names defined at the top level, to fix the lunacy introduced in GHC 7.2.
-- Why they should be fresh is beyond me; it really seems absurd because there is no way whatsoever
-- to refer to names known to be bound in [d||] quotes other than to scrounge around inside the
-- generated 'Dec's.
genericalizeDecs :: [Dec] -> [Dec]
genericalizeDecs decs = everywhere (mkT fixName) decs
    where
        -- get all names bound in the decs and make them generic
        -- at every occurence in decs.
        names = decs >>= namesBoundInDec
        genericalizedNames = [ (n, genericalizeName n) | n <- names]
        fixName = replace (`lookup` genericalizedNames)

