{-# LANGUAGE FlexibleContexts #-}
module Language.Haskell.TH.Specialize where
    
import Language.Haskell.TH
import Language.Haskell.TH.TypeSub
import Control.Monad.Error
import Control.Monad.State
import Data.Generics.Uniplate.Data
import Data.List
import Control.Applicative
import Data.List.Utils

--type Result a = Either String a

-- | Collect all of the constructors for a type
--
collect_constr :: [Dec] -> [(Name, [Con])]
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
get_cons_pair :: Dec -> Result (Name, [Con])
get_cons_pair dec = do
    name <- get_dec_name dec
    let cons = get_cons dec
    return (name, cons)

--get_dec_name :: (Monad m, MonadError String m) => Dec -> m Name
get_dec_name :: Dec -> Result Name
get_dec_name (FunD name _)             = Right name
get_dec_name (ValD _ _ _)              = Left "ValD does not have a name"
get_dec_name (DataD _ name _ _ _)      = Right name
get_dec_name (NewtypeD _ name _ _ _)   = Right name
get_dec_name (TySynD name _ _)         = Right name
get_dec_name (ClassD _ name _ _ _)     = Right name
get_dec_name (InstanceD _ _ _)         = Left "InstanceD does not have a name"
get_dec_name (SigD name _)             = Right name
get_dec_name (ForeignD _)              = Left "ForeignD does not have a name"
get_dec_name (PragmaD _ )              = Left "PragmaD does not have a name"
get_dec_name (FamilyD _ name _ _)      = Right name
get_dec_name (DataInstD _ name _ _ _ ) = Right name

set_dec_name :: (Monad m, MonadError String m) => Name -> Dec -> m Dec
set_dec_name name (FunD _ x)                = return $ FunD name x
set_dec_name name (ValD _ _ _)              = throwError "ValD does not have a name"
set_dec_name name (DataD x _ y z w)         = return $ DataD x name y z w
set_dec_name name (NewtypeD x _ y z w)      = return $ NewtypeD x name y z w
set_dec_name name (TySynD _ x y)            = return $ TySynD name x y
set_dec_name name (ClassD x _ y z w)        = return $ ClassD x name y z w
set_dec_name name (InstanceD _ _ _)         = throwError "InstanceD does not have a name"
set_dec_name name (SigD _ x)                = return $ SigD name x
set_dec_name name (ForeignD _)              = throwError "ForeignD does not have a name"
set_dec_name name (PragmaD _ )              = throwError "PragmaD does not have a name"
set_dec_name name (FamilyD x _ y z)         = return $ FamilyD x name y z
set_dec_name name (DataInstD x _ y z w )    = return $ DataInstD x name y z w

-- | I need to expand all the constructors 
-- for all the ConT in a type, replace them with the expanded version
--expand_type :: [Dec] -> Type -> Result Type
--expand_type decs t@(ConT name) = result where
--    current_dec <- 
--    result = case current_dec of
--                TySynD _ _ expanded_typ -> expanded_typ
--                _                       -> t
--expand_type _ typ = typ
--this part doesn't do the subsitution

find_dec :: (Monad m, Functor m, MonadError String m) => [Dec] -> Name -> m Dec
find_dec decs name = throw_maybe "could not find dec" $ find (is_dec_name name) decs

is_dec_name name dec = result where
    dec_name_result = get_dec_name dec
    result = case dec_name_result of 
                Right x -> x == name
                Left _  -> False

find_dec_from_constr :: (Monad m, Functor m, MonadError String m) => [Dec] -> Name -> m Dec
find_dec_from_constr decs name = throw_maybe "could not find dec" $ 
        find (has_constr name) decs

has_constr :: Name -> Dec -> Bool
has_constr name dec = result where
    found = find (\x -> name == get_con_name x) $ get_cons dec
    result = case found of 
                Just _ -> True
                Nothing  -> False


--I need to create a declarations for a given type
--if the type is 
--this is tricker. I need to recursively do this
--for all of the args first
create_dec_from_type :: (Functor m, Monad m, MonadState [Dec] m, MonadError String m) => 
    DecRenamer -> ConstrRenamer -> Type -> m Type
create_dec_from_type dr cr typ@(AppT x _) = do 
    let args = collect_type_args typ
    create_dec_from_type' dr cr x =<< (mapM (create_dec_from_type dr cr) args)
create_dec_from_type dr cr typ = return typ

type DecRenamer    = ([Type] -> Name -> Result Name)
type ConstrRenamer = ([Type] -> Con -> Con)



has_dec :: (Monad m, MonadState [Dec] m) => Name -> m Bool
has_dec name = undefined

add_dec = undefined

id_constr_renamer x y = y

create_dec_from_type' :: (Monad m, MonadState [Dec] m, Functor m,
                          MonadError String m) => 
                          DecRenamer -> ConstrRenamer -> Type -> [Type] -> m Type
create_dec_from_type' dr cr (ConT name) args = do
        decs          <- get
        dec           <- find_dec decs name
        dec_name      <- throw_either $ get_dec_name dec 
        new_dec_name  <- throw_either $ dr args dec_name
        has_dec'      <- has_dec new_dec_name
        when (not has_dec') $ do 
            new_dec <- sub_dec_and_rename cr dec name args
            add_dec new_dec 

        return $ ConT new_dec_name
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


sub_dec_by_con :: (Monad m, MonadError String m) => 
    ConstrRenamer -> Dec -> Name -> [Type] -> m Dec
sub_dec_by_con cr dec name args = do
    --find the constructor with the given name
    con <- find_con name dec
    --get the names of the ty vars
    let tv_vars = get_con_vars con
    --subsistute the types into the dec
    throw_either $ rename_cons (cr args) $ foldl' sub_type_dec' dec $ zip args tv_vars
    
sub_dec_and_rename :: (Monad m, Functor m, MonadError String m) => 
    ConstrRenamer -> Dec -> Name -> [Type] -> m Dec   
sub_dec_and_rename cr dec name types = rename_dec types =<< sub_dec_by_con cr dec name types

concat_type_names :: [Type] -> String
concat_type_names types = concat $ intersperse "_" $ map (replace " " "_" . show) types 

mk_new_dec_name :: (Monad m, MonadError String m) => [Type] -> Name -> m Name
mk_new_dec_name types dec_name = do
    let suffix   = concat_type_names types 
    return $ mkName $ show dec_name ++ "_" ++ suffix
    

rename_dec :: (Monad m, MonadError String m) => [Type] -> Dec -> m Dec
rename_dec types dec = do
    new_name <- mk_new_dec_name types =<< (throw_either $ get_dec_name dec)
    set_dec_name new_name dec

sub_type_dec' dec (new, old) = sub_type_dec new old dec

find_con :: (Monad m, MonadError String m) => Name -> Dec -> m Con
find_con name dec = throw_maybe err_msg $ find (\x -> name == get_con_name x) $ get_cons dec where
    err_msg = "constructor " ++ show name ++ "not found"
    
throw_maybe :: (Monad m, MonadError String m) => String -> Maybe a -> m a
throw_maybe _ (Just x)   = return x
throw_maybe err Nothing  = throwError err

throw_either :: (Monad m, MonadError String m) => Result a -> m a
throw_either (Right x) = return x
throw_either (Left x)  = throwError x

is_vart (VarT _) = True
is_vart _        = False

get_con_name :: Con -> Name
get_con_name (NormalC n _)     = n
get_con_name (RecC n _)        = n
get_con_name (InfixC _ n _)    = n
get_con_name (ForallC _ _ con) = get_con_name con

get_con_vars :: Con -> [Type]
get_con_vars =  filter is_vart . concatMap universe . get_con_types 

collect_type_args :: Type -> [Type]
collect_type_args (AppT x y) = x:(collect_type_args y)
collect_type_args x          = [x]
























