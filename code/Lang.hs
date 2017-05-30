{-# LANGUAGE TemplateHaskell #-}
import SimpleBound

type TC = Either String
type Ctx a = a -> TC (Type a)

data Term a = Var a
            | TyDef
            | App (Term a) (Term a) (Scope Type a)
            | Bool
            | False
            | If (Scope Type a) (Term a) (Term a) (Term a)
            | Lam (Type a) (Scope Term a)
            | Pi (Type a) (Scope Type a)
            | True
type Type = Term

deriveEq1 ''Term
deriveShow1 ''Term
instance Eq a => Eq (Term a) where (==) = eq1
instance Show a => Show (Term a) where showsPrec = showsPrec1

instance Functor Term where
        fmap = fmapDefault
instance Foldable Term where
        foldMap = foldMapDefault

deriveTraversable ''Term

instance Monad Term where
        Var v1 >>= f = f v1
        App v1 v2 v3 >>= f = App (v1 >>= f) (v2 >>= f) (v3 >>>= f)
        Bool >>= f = Bool
        False >>= f = False
        If v1 v2 v3 v4 >>= f
          = If (v1 >>>= f) (v2 >>= f) (v3 >>= f) (v4 >>= f)
        Lam v1 v2 >>= f = Lam (v1 >>= f) (v2 >>>= f)
        Pi v1 v2 >>= f = Pi (v1 >>= f) (v2 >>>= f)
        True >>= f = True
        TyDef >>= f = TyDef

checkT :: (Show a, Eq a) => Ctx a -> Type a -> Term a -> TC ()
checkT ctx want t
  = do have <- infer ctx t
       when (nf have /= nf want) $
         Left $
           "type mismatch, have: " ++ (show have) ++ " want: " ++ (show want)

checkEq :: (Show a, Eq a) => Term a -> Term a -> TC ()
checkEq want have
  = do when (nf have /= nf want) $
         Left $
           "Terms are unequal, left: " ++
             (show have) ++ " right: " ++ (show want)

report :: String -> TC (Type a)
report nm = throwError $ "Can't have " ++ nm ++ " : " ++ nm

emptyCtx :: (Show a, Eq a) => Ctx a
emptyCtx x = Left $ "Variable not in scope: " ++ show x

consCtx :: (Show a, Eq a) => Type a -> Ctx a -> Ctx (Var a)
consCtx ty ctx B = pure (F <$> ty)
consCtx ty ctx (F a) = (F <$>) <$> ctx a

infer :: (Show a, Eq a) => Ctx a -> Term a -> TC (Type a)
infer ctx (Var v1) = ctx v1
infer ctx TyDef = report "TyDef"
infer ctx al@(App v1 v2 v3)
  = do v4 <- infer ctx v2
       v5 <- pure (nf v4)
       v6 <- infer ctx v1
       checkEq (Pi v5 (toScope (fromScope v3))) v6
       checkT ctx TyDef v5
       checkT (consCtx v5 ctx) TyDef (fromScope v3)
       infer ctx v1
       infer ctx v2
       pure (instantiate v2 (toScope (fromScope v3)))
infer ctx al@Bool = pure TyDef
infer ctx al@False = pure Bool
infer ctx al@(If v1 v2 v3 v4)
  = do v5 <- infer ctx v2
       checkEq Bool v5
       v6 <- infer ctx v4
       checkEq (instantiate False (toScope (fromScope v1))) v6
       v7 <- infer ctx v3
       checkEq (instantiate True (toScope (fromScope v1))) v7
       checkT ctx TyDef Bool
       checkT (consCtx Bool ctx) TyDef (fromScope v1)
       infer ctx v2
       infer ctx v3
       infer ctx v4
       pure (instantiate v2 (toScope (fromScope v1)))
infer ctx al@(Lam v1 v2)
  = do checkT ctx TyDef v1
       v3 <- infer (consCtx v1 ctx) (fromScope v2)
       v4 <- pure (nf v3)
       pure (Pi v1 (toScope v4))
infer ctx al@(Pi v1 v2)
  = do checkT ctx TyDef v1
       checkT (consCtx v1 ctx) TyDef (fromScope v2)
       pure TyDef
infer ctx al@True = pure Bool

nf :: (Show a, Eq a) => Term a -> Term a
nf (Var v1) = Var v1
nf TyDef = TyDef
nf (App v1 v2 v3) = nf' (U Bot) (App (nf v1) (nf v2) (nf1 v3))
nf Bool = Bool
nf False = False
nf (If v1 v2 v3 v4)
  = nf' (U (U Bot)) (If (nf1 v1) (nf v2) (nf v3) (nf v4))
nf (Lam v1 v2) = Lam (nf v1) (nf1 v2)
nf (Pi v1 v2) = Pi (nf v1) (nf1 v2)
nf True = True

nf' :: (Show a, Eq a) => Cnt -> Term a -> Term a
nf' (U _) al@(App (Lam v1 (Scope v2)) v3 (Scope v4))
  = case
      do v5 <- pure v1
         v6 <- pure v4
         v7 <- pure v3
         v8 <- pure v2
         pure (instantiate v7 (toScope v8))
      of
        Left _ -> nf' Bot al
        Right x -> nf x
nf' (U (U _)) al@(If (Scope v1) True v2 v3)
  = case
      do v4 <- pure v1
         v5 <- pure v2
         v6 <- pure v3
         pure v5
      of
        Left _ -> nf' (U Bot) al
        Right x -> nf x
nf' (U _) al@(If (Scope v1) False v2 v3)
  = case
      do v4 <- pure v1
         v5 <- pure v2
         v6 <- pure v3
         pure v6
      of
        Left _ -> nf' Bot al
        Right x -> nf x
nf' _ x = x

rt f x = runIdentity (traverse f x)
nf1 x = (toScope $ nf $ fromScope x)

data Cnt = Bot | U (Cnt)
         deriving (Eq, Show)
