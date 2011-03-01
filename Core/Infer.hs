module Core.Infer (infer) where

import Core.Data
import Core.FreeVars
import Core.Syntax
import Core.Type

import IdSupply
import Name
import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.Graph.Wrapper as G

import Control.Monad

import qualified Data.Map as M
import qualified Data.Set as S


infer :: [(Var, Term)] -> Either String [(Var, Type)]
infer xes = fmap (\(s, xes) -> map (second (zonk (setToMap anyTy (freeTyVars (M.elems s))) . zonk s)) xes) $ runTcM (inferLetRec xes)


-- Guaranteed not to occur in input term (in particular within foralls)
type MetaTyVar = TyVar
--data TypeScheme = TS [TyVar] Type

data TcEnv = TcEnv {
    inScope :: M.Map Var Type
  }

data TcState = TcState {
    idSupply :: IdSupply,
    substitution :: M.Map MetaTyVar Type -- Invariant: Types in range do not contain the domain's MetaTyVars as free type variables (so zonking can be done in one pass)
  }

newtype TcM a = TcM { unTcM :: TcEnv -> TcState -> Either String (TcState, a) }

instance Functor TcM where
    fmap = liftM

instance Monad TcM where
    return x = TcM $ \_e s -> Right (s, x)
    mx >>= fxmy = TcM $ \e s -> case unTcM mx e s of Left err -> Left err
                                                     Right (s, x) -> unTcM (fxmy x) e s
    fail s = TcM $ \_ _ -> Left s


class Zonkable a where
    zonk :: M.Map MetaTyVar Type -> a -> a
    freeTyVars :: a -> S.Set TyVar

instance Zonkable a => Zonkable [a] where
    zonk env tys = map (zonk env) tys
    freeTyVars = S.unions . map freeTyVars

instance (Zonkable a, Zonkable b) => Zonkable (a, b) where
    zonk env (ty1, ty2) = (zonk env ty1, zonk env ty2)
    freeTyVars (ty1, ty2) = freeTyVars ty1 `S.union` freeTyVars ty2

-- instance Zonkable TypeScheme where
--     zonk env (TS tvs ty) = TS tvs (zonk (M.filterWithKey (\x' _ -> not (x' `elem` tvs)) env) ty)
--     freeTyVars (TS tvs ty) = M.filterWithKey (\x' _ -> not (x' `elem` tvs)) (freeTyVars ty)

instance Zonkable Type where
    zonk env ty = case ty of
        TyVar x -> M.findWithDefault {- (error $ "Out of scope TyVar: " ++ show x) -} (TyVar x) x env -- NB: TyVar may be out of scope if it is is Meta.... could cleanup (FIXME)
        TyTyCon tc -> TyTyCon tc
        TyApp t1 t2 -> TyApp (zonk env t1) (zonk env t2)
        TyForAll x t -> TyForAll x (zonk (M.insert x (TyVar x) env) t)
    freeTyVars ty = case ty of
        TyVar x -> S.singleton x
        TyTyCon _ -> S.empty
        TyApp t1 t2 -> freeTyVars t1 `S.union` freeTyVars t2
        TyForAll x t -> S.delete x (freeTyVars t)

-- instance Zonkable Term where
--     zonk _env e = e -- FIXME
--     freeTyVars _e = S.empty -- FIXME

runTcM :: TcM a -> Either String (M.Map MetaTyVar Type, a)
runTcM mx = case unTcM mx (TcEnv { inScope = M.empty }) (TcState { idSupply = inferIdSupply, substitution = M.empty }) of
    Left err     -> Left err
    Right (s, x) -> Right (substitution s, x)


freshMetaTyVar :: TcM MetaTyVar
freshMetaTyVar = TcM $ \_ s -> case freshName (idSupply s) "meta" of (ids, tyv) -> Right (s { idSupply = ids }, tyv)

withinScopeOf :: [(Var, Type)] -> TcM a -> TcM a
withinScopeOf what mx = TcM $ \e s -> unTcM mx (e { inScope = M.fromList what `M.union` inScope e }) s

lookupType :: Var -> TcM Type
lookupType x = TcM $ \e s -> Right (s, M.findWithDefault (error $ "Out of scope Var: " ++ show x) x (inScope e))

zonkM :: Zonkable a => a -> TcM a
zonkM ty = TcM $ \_ s -> Right (s, zonk (substitution s) ty)

generalise :: Type -> TcM Type
generalise ty = TcM $ \e s -> let ty' = zonk (substitution s) ty
                                  free_tvs = freeTyVars ty'
                                  captured_tvs = freeTyVars (zonk (substitution s) (M.elems (inScope e)))
                              in -- traceRender ("generalise", ty', free_tvs, captured_tvs) $
                                 Right (s, tyForAlls (S.toList (free_tvs S.\\ captured_tvs)) ty')


-- TODO: unify these two functions somewhat?
lambdaBind :: Var -> (MetaTyVar -> TcM a) -> TcM a
lambdaBind x body = do
    arg_tyv <- freshMetaTyVar
    withinScopeOf [(x, TyVar arg_tyv)] $ body arg_tyv

letBind :: [Var] -> ([MetaTyVar] -> TcM a) -> TcM ([Type], a)
letBind xs body = do
    arg_tyvs <- mapM (\_ -> freshMetaTyVar) xs
    res <- withinScopeOf (xs `zip` map TyVar arg_tyvs) $ body arg_tyvs
    arg_gen_tys <- mapM (generalise . TyVar) arg_tyvs
    return (arg_gen_tys, res)


inferVar :: Var -> TcM Type
inferVar x = lookupType x >>= (instantiate . collectTyForAlls)

instantiate :: Zonkable a => ([TyVar], a) -> TcM a
instantiate (tvs, ty) = do
    inst_tvs <- mapM (\_ -> fmap TyVar freshMetaTyVar) tvs
    return (zonk (M.fromList (tvs `zip` inst_tvs)) ty)


unify :: Type -> Type -> TcM ()
unify ty1 ty2 = go [] ty1 ty2 -- NB: unifying unzonked types
  where
    go skolems (TyVar x1)        (TyVar x2)        | (x1, x2) `elem` skolems = return ()
    go skolems (TyVar x1)        ty2               | all ((/= x1) . fst) skolems = substitute skolems x1 ty2
    go skolems ty1               (TyVar x2)        | all ((/= x2) . snd) skolems = substitute skolems x2 ty1
    go skolems (TyTyCon tc1)     (TyTyCon tc2)     | tc1 == tc2 = return ()
    go skolems (TyApp ty1a ty1b) (TyApp ty2a ty2b) = go skolems ty1a ty2a >> go skolems ty1b ty2b
    go skolems (TyForAll x1 ty1) (TyForAll x2 ty2) = go ((x1, x2) : skolems) ty1 ty2
    go skolems ty1 ty2 = fail $ show $ text "Cannot unify:" $$ nest 2 (pPrint ty1) $$ text "and:" $$ nest 2 (pPrint ty2)
    
    -- Precondition: the substitution must not contain a binding for x already
    --substitute :: MetaTyVar -> Type -> TcM ()
    substitute skolems x ty = TcM $ \e s -> case M.lookup x (substitution s) of
        Nothing | x `S.member` freeTyVars ty' -> Left $ show $ text "Occurs check failed in:" $$ pPrint ty' -- By substitution invariant, domain of s cannot be free in ty'
                | otherwise                   -> Right (s { substitution = M.insert x ty' (M.map (zonk (M.singleton x ty')) (substitution s)) }, ())
          where ty' = zonk (substitution s) ty
        Just got_ty -> unTcM (go skolems got_ty ty) e s


inferTerm :: Term -> TcM Type
inferTerm = inferTerm' . unI

inferTerm' (Var x) = inferVar x
inferTerm' (Value v) = case v of
    Indirect x -> lookupType x
    Lambda x e -> lambdaBind x $ \arg_tyv -> do
        body_ty <- inferTerm e
        return (TyVar arg_tyv `funTy` body_ty)
    Data dc xs -> do
        (res_ty, arg_tys) <- instantiate (tvs, (TyTyCon tc `tyApps` map TyVar tvs, tys))
        zipWithEqualM_ (\x arg_ty -> inferVar x >>= unify arg_ty) xs arg_tys
        return res_ty
      where (tc, tvs, tys) = dataConFields dc
    Literal l -> return $ literalType l
inferTerm' (App e x) = do
    fun_ty <- inferTerm e
    arg_ty <- lookupType x
    res_ty <- freshMetaTyVar
    unify fun_ty (arg_ty `funTy` TyVar res_ty)
    return (TyVar res_ty)
inferTerm' (PrimOp pop es) = case pop of
    Add           -> intIntInt
    Subtract      -> intIntInt
    Multiply      -> intIntInt
    Divide        -> intIntInt
    Modulo        -> intIntInt
    Equal         -> intIntBool
    LessThan      -> intIntBool
    LessThanEqual -> intIntBool
  where
    intIntInt  = intIntX intTy
    intIntBool = intIntX boolTy
    intIntX res_ty = do
      [ty1, ty2] <- mapM inferTerm es
      mapM_ (unify intTy) [ty1, ty2]
      return (ty1 `funTy` ty2 `funTy` res_ty)
inferTerm' (Case e alts) = do
    scrut_ty <- inferTerm e
    res_ty <- freshMetaTyVar
    forM_ alts $ \(alt_con, e) -> do
        bv_tys <- case alt_con of
            DefaultAlt mb_x -> return $ maybe [] (\x -> [(x, scrut_ty)]) mb_x
            LiteralAlt l    -> unify (literalType l) scrut_ty >> return []
            DataAlt dc xs   -> do
                -- TODO: commonality with Data introducer?
                let (tc, tvs, tys) = dataConFields dc
                (res_ty, arg_tys) <- instantiate (tvs, (TyTyCon tc `tyApps` map TyVar tvs, tys))
                unify res_ty scrut_ty
                zipWithEqualM (\x arg_ty -> return (x, arg_ty)) xs arg_tys
        branch_ty <- withinScopeOf bv_tys $ inferTerm e
        unify (TyVar res_ty) branch_ty
    return (TyVar res_ty)
inferTerm' (LetRec xes e) = do
    bound_tys <- inferLetRec xes
    withinScopeOf bound_tys $ inferTerm e

-- Since this inference procedure is used even to typecheck top-level bindings, it is essential to do the dependency analysis here
inferLetRec :: [(Var, Term)] -> TcM [(Var, Type)]
inferLetRec xes = go $ map Foldable.toList (G.stronglyConnectedComponents graph)
  where
    graph = G.fromList [(x, e, S.toList (termFreeVars e)) | (x, e) <- xes]
    
    go [] = return []
    go (xs:sccs) = do
        let es = map (G.vertex graph) xs
        (bound_schemes, ()) <- letBind xs $ \bound_tyvs -> zipWithEqualM_ (\bound_tyv e -> inferTerm e >>= unify (TyVar bound_tyv)) bound_tyvs es
        let xtys = xs `zip` bound_schemes -- TODO: a bit ugly here and in (LetRec xes e) clause above
        fmap (xtys ++) $ withinScopeOf xtys $ go sccs

literalType :: Literal -> Type
literalType l = case l of
    Int _ -> intTy
    Char _ -> charTy
