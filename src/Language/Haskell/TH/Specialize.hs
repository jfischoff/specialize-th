{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, FlexibleInstances, GeneralizedNewtypeDeriving,
 TemplateHaskell #-}
module Language.Haskell.TH.Specialize 
(
-- ** Main Interface
expand_and_specialize,
 expand_and_specialize',
-- *** Helper Types
 ConstructorName (..),
 TypeName (..),
-- *** Renamer Interface
 DecRenamer,
 ConstrRenamer,
-- *** Stock Renamers
 mk_new_dec_name,
 id_constr_renamer,

  -- ** Utils ... Pretend these are not here
 sub_dec_and_rename,
 create_dec_from_type,
 find_con,

 get_con_vars,
 get_ty_vars,
 concat_type_names,
 rename_dec,
 run_state',
 Result
 ) where
    
import Language.Haskell.TH
import Language.Haskell.TH.Universe
import Language.Haskell.TH.TypeSub
import Control.Monad.Error
import Control.Monad.State
import Data.Generics.Uniplate.Data
import Data.List
import Control.Applicative
import Data.List.Utils
import Control.Applicative
import Control.Newtype
import Control.Newtype.TH
import Language.Haskell.TH.ExpandSyns
import Data.Composition
import Data.List




-- | Expand all the type syn's and create specialize types for any polymorphic types.
--   All of the new specialized declarations are returned, along with the original dec 
--   with subbed types and a new name. 
--   The first Name is the name of the Dec to create specialize instances for.
--   The second Name, is the new name for the Dec.
--   use mk_new_dec_name for the Dec renaming and id_constr_renamer for the constructor renaming.
expand_and_specialize :: Name -> Name -> Q [Dec]
expand_and_specialize = expand_and_specialize' mk_new_dec_name id_constr_renamer

-- | Expand all the type syn's and create specialize types for any polymorphic types.
--   All of the new specialized declarations are returned, along with the original dec 
--   with subbed types and a new name. 
--   The first Name is the name of the Dec to create specialize instances for.
--   The second Name, is the new name for the Dec.
--   The DecRenamer and ConstrRenamer are used to rename Dec's and Con's respectively.
expand_and_specialize' :: DecRenamer -> ConstrRenamer -> Name -> Name -> Q [Dec]
expand_and_specialize' dr cr name new_name = do
    universe <- map snd <$> get_universe name
    decs <- expand_type_syn_decs universe
    
    (new_dec, new_decs) <- run_state' (create_decs_from_name dr cr (TypeName name)) decs
    
    let result = case new_dec of
                Right x -> (from_right $ set_dec_name (pack new_name) x):new_decs
                Left  _ -> new_decs
    
    return $ (nub result) \\ decs
    
expand_type_syn_decs :: [Dec] -> Q [Dec]
expand_type_syn_decs decs = mapM expand_type_syn_dec decs

expand_type_syn_dec :: Dec -> Q Dec
expand_type_syn_dec dec = (from_right . (flip set_cons) dec) <$> (mapM expand_type_syn_con $ get_cons dec)

expand_type_syn_con :: Con -> Q Con
expand_type_syn_con con = set_con_types' con <$> (mapM expand_type_syn_type $ 
                                    get_con_types con)
                                    
expand_type_syn_type :: Type -> Q Type
expand_type_syn_type = expandSyns

find_dec :: [Dec] -> TypeName -> Result Dec
find_dec decs name = maybe_to_either "could not find dec" $ find (is_dec_name name) decs

is_dec_name name dec = result where
    dec_name_result = get_dec_name dec
    result = case dec_name_result of 
                Right x -> x == name
                Left _  -> False

find_dec_from_constr :: (Monad m, Functor m, MonadError String m) => [Dec] -> ConstructorName -> m Dec
find_dec_from_constr decs name = throw_maybe "could not find dec" $ 
        find (has_constr name) decs

has_constr :: ConstructorName -> Dec -> Bool
has_constr name dec = result where
    found = find (\x -> name == get_con_name x) $ get_cons dec
    result = case found of 
                Just _ -> True
                Nothing  -> False

create_decs_from_name :: (Functor m, Monad m, MonadState [Dec] m, MonadError String m) => 
    DecRenamer -> ConstrRenamer -> TypeName -> m Dec
create_decs_from_name dr cr name = do
    decs <- get
    dec <- throw_either $ find_dec decs name
    create_decs_from_dec dr cr dec

create_decs_from_dec :: (Functor m, Monad m, MonadState [Dec] m, MonadError String m) => 
    DecRenamer -> ConstrRenamer -> Dec -> m Dec 
create_decs_from_dec dr cr dec = (from_right . (flip set_cons) dec) <$> 
    (mapM (create_decs_from_con dr cr) $ get_cons dec)
            
create_decs_from_con :: (Functor m, Monad m, MonadState [Dec] m, MonadError String m) => 
    DecRenamer -> ConstrRenamer -> Con -> m Con 
create_decs_from_con dr cr con = set_con_types' con <$> (mapM (create_dec_from_type dr cr) $ 
                                    get_con_types con)
    
create_dec_from_type :: (Functor m, Monad m, MonadState [Dec] m, MonadError String m) => 
    DecRenamer -> ConstrRenamer -> Type -> m Type
create_dec_from_type dr cr typ@(AppT _ _) = do 
    let x:args = collect_type_args typ
    create_dec_from_type' dr cr x =<< (mapM (create_dec_from_type dr cr) args)
create_dec_from_type dr cr typ = return typ

type DecRenamer    = ([Type] -> TypeName -> Result TypeName)
type ConstrRenamer = ([Type] -> Con -> Con)

has_dec :: (Monad m, MonadState [Dec] m) => TypeName -> m Bool
has_dec name = gets (any (is_dec_name name))

add_dec dec = modify (dec:) 

-- | Default Con renamer
id_constr_renamer :: [Type] -> Con -> Con
id_constr_renamer x y = y

newtype ConstructorName = ConstructorName { runConstructorName :: Name }
    deriving(Show, Eq)
newtype TypeName = TypeName { runTypeName :: Name }
    deriving(Show, Eq)

create_dec_from_type' :: (Monad m, MonadState [Dec] m, Functor m,
                          MonadError String m) => 
                          DecRenamer -> ConstrRenamer -> Type -> [Type] -> m Type
create_dec_from_type' dr cr (ConT name) args = do
        decs          <- get     
        dec           <- throw_either $ find_dec decs $ TypeName name
        dec_name      <- throw_either $ get_dec_name dec 
        new_dec_name  <- throw_either $ dr args dec_name
        has_dec'      <- has_dec new_dec_name
        when (not has_dec') $ do 
            new_dec <- sub_dec_and_rename cr dec args
            add_dec new_dec 

        return $ ConT $ runTypeName new_dec_name
create_dec_from_type' dr cr ListT args                 = 
    create_dec_from_type' dr cr (ConT $ mkName "GHC.Types.[]") args 
create_dec_from_type' dr cr (TupleT count) args        = 
    create_dec_from_type' dr cr (ConT $ mkName ("GHC.Types.(" ++ 
        (concat $ take count (cycle [","])) ++ ")")) args
create_dec_from_type' dr cr t@(AppT _ _) args            = do
    typ <- (create_dec_from_type dr cr t)
    create_dec_from_type' dr cr typ args
create_dec_from_type' dr cr (SigT t _) args              = do
    typ <- (create_dec_from_type dr cr t)
    create_dec_from_type' dr cr typ args
create_dec_from_type' dr cr (ForallT _ _ t) args         = do
    typ <- (create_dec_from_type dr cr t)
    create_dec_from_type' dr cr typ args
create_dec_from_type' dr cr t args = 
    --just return what was passed in if we can't do anything
    return $ foldl' AppT t args 

rename_cons :: (Con -> Con) -> Dec -> Result Dec
rename_cons cr dec = result where
    new_cons = map cr $ get_cons dec
    result = set_cons new_cons dec
    
set_cons :: [Con] -> Dec -> Result Dec
set_cons (con:[]) (NewtypeD x y z _ w)     = Right $ NewtypeD x y z con w
set_cons cons (NewtypeD _ _ _ _ _)         = Left $ show cons ++ " is not a appropiate arg for setting the NewtypeD's constructor arg"
set_cons cons (DataD x y z _ w)            = Right $ DataD x y z cons w
set_cons cons (DataInstD x y z _ w)        = Right $ DataInstD x y z cons w
set_cons (con:[]) (NewtypeInstD x y z _ w) = Right $ NewtypeInstD x y z con w
set_cons cons (NewtypeInstD x y z _ w)     = Left $ show cons ++ " is not a appropiate arg for setting the NewtypeInstD's constructor arg"
set_cons _ x                               = Left $ "Can't set the constructors for " ++ show x

get_ty_vars :: Dec -> [TyVarBndr]
get_ty_vars (NewtypeD _ _ ty_vars _ _) = ty_vars
get_ty_vars (DataD    _ _ ty_vars _ _) = ty_vars
get_ty_vars (TySynD _ ty_vars _)       = ty_vars
get_ty_vars (ClassD _ _ ty_vars _ _)   = ty_vars
get_ty_vars (FamilyD _ _ ty_vars _ )   = ty_vars
get_ty_vars _                          = []

ty_var_name :: TyVarBndr -> Name
ty_var_name (KindedTV name _ ) = name
ty_var_name (PlainTV name) = name

sub_dec_by_con :: (Monad m, MonadError String m) => 
    ConstrRenamer -> Dec -> [Type] -> m Dec
sub_dec_by_con cr dec args = do
    --get the names of the ty vars
    let tv_vars = get_ty_vars dec
    --subsistute the types into the dec
    throw_either $ rename_cons (cr args) $ foldl' sub_type_dec' dec $ zip args $ 
        map (VarT . ty_var_name) tv_vars
    
sub_dec_and_rename :: (Monad m, Functor m, MonadError String m) => 
    ConstrRenamer -> Dec -> [Type] -> m Dec   
sub_dec_and_rename cr dec types = rename_dec types =<< sub_dec_by_con cr dec types

concat_type_names :: [Type] -> String
concat_type_names types = concat $ intersperse "_" $ map (replace " " "_" . show) types 

-- | Default Dec renamer
mk_new_dec_name :: [Type] -> TypeName -> Result TypeName
mk_new_dec_name types dec_name = do
    let suffix   = concat_type_names types
    let dec_name_string = show $ unpack dec_name
    let name_string = if isSuffixOf "[]" dec_name_string
                        then suffix ++ "_List"
                        else dec_name_string ++ "_" ++ suffix
 
    return $ pack $ mkName $ name_string
    

rename_dec :: (Monad m, MonadError String m) => [Type] -> Dec -> m Dec
rename_dec types dec = do
    new_name <- (throw_either . mk_new_dec_name types) =<< (throw_either $ get_dec_name dec)
    set_dec_name new_name dec

sub_type_dec' dec (new, old) = sub_type_dec new old dec

find_con :: (Monad m, MonadError String m) => ConstructorName -> Dec -> m Con
find_con name dec = throw_maybe err_msg $ find (\x -> name == get_con_name x) $ get_cons dec where
    err_msg = "constructor " ++ show name ++ "not found"
    
throw_maybe :: (Monad m, MonadError String m) => String -> Maybe a -> m a
throw_maybe _ (Just x)   = return x
throw_maybe err Nothing  = throwError err

maybe_to_either :: String -> Maybe a -> Result a
maybe_to_either msg (Just a) = Right a
maybe_to_either msg Nothing = Left msg

throw_either :: (Monad m, MonadError String m) => Result a -> m a
throw_either (Right x) = return x
throw_either (Left x)  = throwError x

is_vart (VarT _) = True
is_vart _        = False

get_con_name :: Con -> ConstructorName
get_con_name (NormalC n _)     = pack n
get_con_name (RecC n _)        = pack n
get_con_name (InfixC _ n _)    = pack n
get_con_name (ForallC _ _ con) = get_con_name con

get_con_vars :: Con -> [Type]
get_con_vars =  filter is_vart . concatMap universe . get_con_types 

collect_type_args :: Type -> [Type]
collect_type_args (AppT x y) = x:(collect_type_args y)
collect_type_args x          = [x]

run_state' x xs = runStateT (runErrorT (runErrorStateT x)) xs

type ErrorStateType m e s a = ErrorT e (StateT s m) a

newtype ErrorStateT e s m a = ErrorStateT { runErrorStateT :: ErrorStateType m e s a }
    deriving (Monad, MonadState s, MonadError e, Functor, MonadPlus)
    
instance MonadTrans (ErrorStateT String [Dec]) where
    lift = ErrorStateT . lift . lift

collect_constr :: [Dec] -> [(TypeName, [Con])]
collect_constr decs = right_only $ map get_cons_pair decs

is_right :: Either a b -> Bool
is_right (Right _) = True
is_right (Left _)  = False

from_right :: Either a b -> b
from_right (Right x) = x
from_right (Left _)  = error "from_right"

right_only :: [Either a b] -> [b]
right_only = map from_right . filter is_right

--get_cons_pair :: (Monad m, MonadError String m) => Dec -> m (Name, [Con])
get_cons_pair :: Dec -> Result (TypeName, [Con])
get_cons_pair dec = do
    name <- get_dec_name dec
    let cons = get_cons dec
    return (name, cons)

--get_dec_name :: (Monad m, MonadError String m) => Dec -> m Name
get_dec_name :: Dec -> Result TypeName
get_dec_name (FunD name _)             = Right $ pack name
get_dec_name (ValD _ _ _)              = Left "ValD does not have a name"
get_dec_name (DataD _ name _ _ _)      = Right $ pack name
get_dec_name (NewtypeD _ name _ _ _)   = Right $ pack name
get_dec_name (TySynD name _ _)         = Right $ pack name
get_dec_name (ClassD _ name _ _ _)     = Right $ pack name
get_dec_name (InstanceD _ _ _)         = Left "InstanceD does not have a name"
get_dec_name (SigD name _)             = Right $ pack name
get_dec_name (ForeignD _)              = Left "ForeignD does not have a name"
get_dec_name (PragmaD _ )              = Left "PragmaD does not have a name"
get_dec_name (FamilyD _ name _ _)      = Right $ pack name
get_dec_name (DataInstD _ name _ _ _ ) = Right $ pack name

set_dec_name :: (Monad m, MonadError String m) => TypeName -> Dec -> m Dec
set_dec_name name (FunD _ x)                = return $ FunD (unpack name) x
set_dec_name name (ValD _ _ _)              = throwError "ValD does not have a name"
set_dec_name name (DataD x _ y z w)         = return $ DataD x (unpack name) y z w
set_dec_name name (NewtypeD x _ y z w)      = return $ NewtypeD x (unpack name) y z w
set_dec_name name (TySynD _ x y)            = return $ TySynD (unpack name) x y
set_dec_name name (ClassD x _ y z w)        = return $ ClassD x (unpack name) y z w
set_dec_name name (InstanceD _ _ _)         = throwError "InstanceD does not have a name"
set_dec_name name (SigD _ x)                = return $ SigD (unpack name) x
set_dec_name name (ForeignD _)              = throwError "ForeignD does not have a name"
set_dec_name name (PragmaD _ )              = throwError "PragmaD does not have a name"
set_dec_name name (FamilyD x _ y z)         = return $ FamilyD x (unpack name) y z
set_dec_name name (DataInstD x _ y z w )    = return $ DataInstD x (unpack name) y z w

set_con_types' :: Con -> [Type] -> Con
set_con_types' (NormalC n st)    types = NormalC n $ zipWith (\(x, _) t -> (x, t)) st types
set_con_types' (RecC n st)       types = RecC n $ zipWith (\(x, y, _) t -> (x,y,t)) st types
set_con_types' (InfixC (x, _) n (y, _))  [a, b] = InfixC (x, a) n (y, b)
set_con_types' (ForallC x y con) types = ForallC x y $ set_con_types' con types

$(mkNewTypes [''ConstructorName, ''TypeName])













