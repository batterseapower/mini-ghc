module Core.Data where

import Core.Type

import Name
import Utilities


type Arity = Int
type DataCon = String

dataTypes :: [(TyCon, [TyVar], [(DataCon, [Type])])]
dataTypes = [
    ("()"       , [],
     [("()"     , [])]),
    ("(,)"      , [name "a", name "b"],
     [("(,)"    , [TyVar (name "a"), TyVar (name "b")])]),
    ("(,,)"     , [name "a", name "b", name "c"],
     [("(,,)"   , [TyVar (name "a"), TyVar (name "b"), TyVar (name "c")])]),
    ("(,,,)"    , [name "a", name "b", name "c", name "d"],
     [("(,,,)"  , [TyVar (name "a"), TyVar (name "b"), TyVar (name "c"), TyVar (name "d")])]),
    ("[]"       , [name "a"],
     [("[]"     , []),
      ("(:)"    , [TyVar (name "a"), TyTyCon "[]" `TyApp` TyVar (name "a")])]),
    ("Either"   , [name "a", name "b"],
     [("Left"   , [TyVar (name "a")]),
      ("Right"  , [TyVar (name "b")])]),
    ("Bool"     , [],
     [("True"   , []),
      ("False"  , [])]),
    ("Maybe"    , [name "a"],
     [("Just"   , [TyVar (name "a")]),
      ("Nothing", [])])
  ]

dataConFriendlyName :: DataCon -> Maybe String
dataConFriendlyName dc = case dc of
    "()"    -> Just "Tup0"
    "(,)"   -> Just "Tup2"
    "(,,)"  -> Just "Tup3"
    "(,,,)" -> Just "Tup4"
    "[]"    -> Just "Nil"
    "(:)"   -> Just "Cons"
    _       -> Nothing

dataConFields :: DataCon -> (TyCon, [TyVar], [Type])
dataConFields have_dc = case [(tc, tvs, tys) | (tc, tvs, dt) <- dataTypes, (dc, tys) <- dt, dc == have_dc] of
  [res] -> res
  _     -> panic "dataConFields" (text have_dc)

dataConArity :: DataCon -> Arity
dataConArity = length . thd3 . dataConFields

dataConSiblings :: DataCon -> [(DataCon, Arity)]
dataConSiblings have_dc = case [[(dc, length tys) | (dc, tys) <- dt] | (_tc, _tvs, dt) <- dataTypes, Just _ <- [lookup have_dc dt]] of
  [dt] -> dt
  _    -> panic "dataConSiblings" (text have_dc)
