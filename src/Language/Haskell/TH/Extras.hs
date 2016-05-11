{-# LANGUAGE CPP, TemplateHaskell #-}
module Language.Haskell.TH.Extras where

import Control.Monad
import Data.Generics
import Data.Maybe
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

intIs64 :: Bool
intIs64 = toInteger (maxBound :: Int) > 2^32

replace :: (a -> Maybe a) -> (a -> a)
replace = ap fromMaybe

composeExprs :: [ExpQ] -> ExpQ
composeExprs [] = [| id |]
composeExprs [f] = f
composeExprs (f:fs) = [| $f . $(composeExprs fs) |]

nameOfCon :: Con -> Name
nameOfCon (NormalC  name _) = name
nameOfCon (RecC     name _) = name
nameOfCon (InfixC _ name _) = name
nameOfCon (ForallC _ _ con) = nameOfCon con
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
nameOfCon (GadtC [name] _ _)    = name
nameOfCon (RecGadtC [name] _ _) = name
#endif

-- |WARNING: discards binders in GADTs and existentially-quantified constructors
argTypesOfCon :: Con -> [Type]
argTypesOfCon (NormalC  _ args) = map snd args
argTypesOfCon (RecC     _ args) = [t | (_,_,t) <- args]
argTypesOfCon (InfixC x _ y)    = map snd [x,y]
argTypesOfCon (ForallC _ _ con) = argTypesOfCon con
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
argTypesOfCon (GadtC _ args _)    = map snd args
argTypesOfCon (RecGadtC _ args _) = [t | (_,_,t) <- args]
#endif

nameOfBinder :: TyVarBndr -> Name
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 700
nameOfBinder (PlainTV n)    = n
nameOfBinder (KindedTV n _) = n
#else
nameOfBinder = id
type TyVarBndr = Name
#endif

varsBoundInCon :: Con -> [TyVarBndr]
varsBoundInCon (ForallC bndrs _ con) = bndrs ++ varsBoundInCon con
varsBoundInCon _ = []

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

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
namesBoundInDec (DataD _ name _ _ _ _)              = [name]
namesBoundInDec (NewtypeD _ name _ _ _ _)           = [name]
#else
namesBoundInDec (DataD _ name _ _ _)                = [name]
namesBoundInDec (NewtypeD _ name _ _ _)             = [name]
#endif

namesBoundInDec (TySynD name _ _)                   = [name]
namesBoundInDec (ClassD _ name _ _ _)               = [name]
namesBoundInDec (ForeignD (ImportF _ _ _ name _))   = [name]

#if defined(__GLASGOW_HASKELL__)
#if __GLASGOW_HASKELL__ >= 800
namesBoundInDec (OpenTypeFamilyD (TypeFamilyHead name _ _ _))     = [name]
namesBoundInDec (ClosedTypeFamilyD (TypeFamilyHead name _ _ _) _) = [name]
#elif __GLASGOW_HASKELL__ >= 612
namesBoundInDec (FamilyD _ name _ _)                = [name]
#endif
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

headOfType :: Type -> Name
headOfType (ForallT _ _ ty) = headOfType ty
headOfType (VarT name) = name
headOfType (ConT name) = name
headOfType (TupleT n) = tupleTypeName n
headOfType ArrowT = ''(->)
headOfType ListT = ''[]
headOfType (AppT t _) = headOfType t

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 612
headOfType (SigT t _) = headOfType t
#endif

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
headOfType (UnboxedTupleT n) = unboxedTupleTypeName n
#endif

occursInType :: Name -> Type -> Bool
occursInType var ty = case ty of
        ForallT bndrs _ ty
            | any (var ==) (map nameOfBinder bndrs)
                -> False
            | otherwise
                -> occursInType var ty
        VarT name
            | name == var -> True
            | otherwise   -> False
        AppT ty1 ty2 -> occursInType var ty1 || occursInType var ty2
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 612
        SigT ty _ -> occursInType var ty
#endif
        _ -> False

