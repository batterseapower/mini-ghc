module Core.Type where

import Name
import Utilities


type TyCon = String
type TyVar = Name

data Type = TyVar TyVar
          | TyTyCon TyCon
          | TyApp Type Type
          | TyForAll TyVar Type

instance Pretty Type where
    pPrintPrec level prec ty = case ty of
        TyVar x       -> pPrintPrec level prec x
        TyTyCon tc    -> text tc
        TyApp ty1 ty2 -> prettyParen (prec >= appPrec) $ pPrintPrec level opPrec ty1 <+> pPrintPrec level appPrec ty2
        TyForAll x ty -> prettyParen (prec > noPrec) $ text "forall" <+> pPrintPrec level appPrec x <> text "." <+> pPrintPrec level noPrec ty

tyApps :: Type -> [Type] -> Type
tyApps = foldl TyApp

tyForAlls :: [TyVar] -> Type -> Type
tyForAlls tvs ty = foldr TyForAll ty tvs

collectTyForAlls :: Type -> ([TyVar], Type)
collectTyForAlls (TyForAll tv ty) = first (tv :) $ collectTyForAlls ty
collectTyForAlls ty               = ([], ty)

infixr 6 `funTy`

funTy :: Type -> Type -> Type
funTy ty1 ty2 = TyTyCon "(->)" `tyApps` [ty1, ty2]

anyTy, boolTy, intTy, charTy :: Type
anyTy = TyTyCon "Any"
boolTy = TyTyCon "Bool"
intTy = TyTyCon "Int"
charTy = TyTyCon "Char"
