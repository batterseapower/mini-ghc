{-# LANGUAGE ViewPatterns, TupleSections, Rank2Types #-}
module Core.Renaming where

import Core.FreeVars
import Core.Syntax

import Renaming
import Utilities

import qualified Data.Set as S


type In a = (Renaming, a)
type Out a = a


renameFreeVars :: Renaming -> FreeVars -> FreeVars
renameFreeVars rn = S.map (rename rn)


renameIn :: (Renaming -> a -> a) -> In a -> a
renameIn f (rn, x) = f rn x

renameInRenaming :: Renaming -> In a -> In a
renameInRenaming rn_by (rn, x) = (renameRenaming rn_by rn, x)

renameBounds :: (Var -> Var -> v) -> IdSupply -> Renaming -> [(Var, a)] -> (IdSupply, Renaming, [(v, In a)])
renameBounds f ids rn (unzip -> (xs, es)) = (ids', rn', zipWith f xs xs' `zip` map (rn',) es)
  where (ids', rn', xs') = renameBinders ids rn xs


(renameTerm,                renameAlts,                renameValue,                renameValue')                = mkRename (\f rn (I e) -> I (f rn e))
(renameFVedTerm,            renameFVedAlts,            renameFVedValue,            renameFVedValue')            = mkRename (\f rn (FVed fvs e) -> FVed (renameFreeVars rn fvs) (f rn e))
(renameTaggedTerm,          renameTaggedAlts,          renameTaggedValue,          renameTaggedValue')          = mkRename (\f rn (Tagged tg e) -> Tagged tg (f rn e))
(renameTaggedSizedFVedTerm, renameTaggedSizedFVedAlts, renameTaggedSizedFVedValue, renameTaggedSizedFVedValue') = mkRename (\f rn (Comp (Tagged tg (Comp (Sized sz (FVed fvs e))))) -> Comp (Tagged tg (Comp (Sized sz (FVed (renameFreeVars rn fvs) (f rn e))))))

{-# INLINE mkRename #-}
mkRename :: (forall a. (Renaming -> a -> a) -> Renaming -> ann a -> ann a)
         -> (IdSupply -> Renaming -> ann (TermF ann)  -> ann (TermF ann),
             IdSupply -> Renaming -> [AltF ann]       -> [AltF ann],
             IdSupply -> Renaming -> ann (ValueF ann) -> ann (ValueF ann),
             IdSupply -> Renaming -> ValueF ann       -> ValueF ann)
mkRename rec = (term, alternatives, value, value')
  where
    term ids rn = rec (term' ids) rn
    term' ids rn e = case e of
      Var x -> Var (rename rn x)
      Value v -> Value (value' ids rn v)
      App e1 x2 -> App (term ids rn e1) (rename rn x2)
      PrimOp pop es -> PrimOp pop (map (term ids rn) es)
      Case e alts -> Case (term ids rn e) (alternatives ids rn alts)
      LetRec xes e -> LetRec (map (second (renameIn (term ids'))) xes') (term ids' rn' e)
        where (ids', rn', xes') = renameBounds (\_ x' -> x') ids rn xes
    
    value ids rn = rec (value' ids) rn
    value' ids rn v = case v of
      Indirect x -> Indirect (rename rn x)
      Lambda x e -> Lambda x' (term ids' rn' e)
        where (ids', rn', x') = renameBinder ids rn x
      Data dc xs -> Data dc (map (rename rn) xs)
      Literal l -> Literal l
    
    alternatives ids rn = map (alternative ids rn)
    
    alternative ids rn (alt_con, alt_e) = (alt_con', term ids' rn' alt_e)
        where (ids', rn', alt_con') = renameAltCon ids rn alt_con

renameAltCon :: IdSupply -> Renaming -> AltCon -> (IdSupply, Renaming, AltCon)
renameAltCon ids rn_alt alt_con = case alt_con of
    DataAlt alt_dc alt_xs -> third3 (DataAlt alt_dc) $ renameBinders ids rn_alt alt_xs
    LiteralAlt _          -> (ids, rn_alt, alt_con)
    DefaultAlt alt_mb_x   -> maybe (ids, rn_alt, alt_con) (third3 (DefaultAlt . Just) . renameBinder ids rn_alt) alt_mb_x
