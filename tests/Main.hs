{-# LANGUAGE TupleSections, GeneralizedNewtypeDeriving,
    FlexibleInstances, NoMonomorphismRestriction, TemplateHaskell #-}
module Main where
import Language.Haskell.TH.Specialize
import Language.Haskell.TH
import Language.Haskell.TH.Syntax 
import Test.Framework (defaultMain, testGroup, defaultMainWithArgs)
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck
import Test.HUnit
import Debug.Trace.Helpers
import Debug.Trace

import Test.QuickCheck.Checkers
import Data.List
import Data.Generics.Uniplate.Data
import Control.Applicative ((<$>))

import TestType
import Control.Monad.Identity
-- import Language.Haskell.TH.LiftInstances

main = defaultMainWithArgs tests ["-a 100", "-o 5"]

tests = [
            testGroup "sub_dec_by_con" [
                testCase "test_find_con_0" test_find_con_0,
                testCase "test_get_con_vars_0" test_get_con_vars_0, 
                testCase "sub_dec_and_rename_0" sub_dec_and_rename_0  
            ],
            testGroup "concat_type_names" [
                testCase "test_concat_type_names_0" test_concat_type_names_0 
            ],
            testGroup "rename_dec" [
                testCase "test_rename_dec_0" test_rename_dec_0 
            ],
            testGroup "create_dec_from_type" [
                testCase "test_create_dec_from_type_0" test_create_dec_from_type_0
            ],
            testGroup "expand_and_specialize" [
                testCase "test_expand_and_specialize_0" test_expand_and_specialize_0,
                testCase "test_expand_and_specialize_1" test_expand_and_specialize_1,
                testCase "test_expand_and_specialize_2" test_expand_and_specialize_2
            ]]

ty_vars_empty dec | (length . get_ty_vars) dec == 0 = True
ty_vars_empty dec | otherwise = False

filter_poly = filter ty_vars_empty

test_expand_and_specialize_2 = show actual @?= show expected where
    actual = $(lift =<< expand_and_specialize ''ListLike ''ListLike) :: [Dec]
    expected = [DataD [] 
        (mkName "TestType.ListLike") [] 
        [RecC (mkName "TestType.ListLike")
            [((mkName "TestType.values"), NotStrict,
                ConT $ mkName "ConT_GHC_Types_Int_List")]] [],
            DataD [] 
                (mkName "ConT_GHC_Types_Int_List") [] 
                [NormalC (mkName "GHC.Types.[]") [],
                 InfixC (NotStrict,ConT $ mkName "GHC.Types.Int") (mkName "GHC.Types.:")
                        (NotStrict, ConT $ mkName "ConT_GHC_Types_Int_List")] []]

test_expand_and_specialize_1 = show actual @?= show expected where
    actual   =  $(lift =<< expand_and_specialize ''TestTypeInt ''TestTypeInt) :: [Dec]
    expected =  [DataD [] (mkName "TestType.TestTypeInt") [] 
                                [NormalC (mkName "TestType.TestTypeInt") 
                                [(NotStrict,ConT $ mkName "TestType_PolyType_ConT_GHC_Types_Int")]] [],
                 DataD [] (mkName "TestType_PolyType_ConT_GHC_Types_Int") [] 
                    [NormalC (mkName "TestType.PolyType") [(NotStrict,ConT (mkName "GHC.Types.Int"))]] []]


test_expand_and_specialize_0 = show actual @?= show expected where
    actual   = sort $(lift =<< expand_and_specialize ''TestType ''TestType) :: [Dec]
    expected = [$(lift =<< (\(TyConI x) -> return x) =<< reify ''TestType)] :: [Dec]
 

test_create_dec_from_type_0 = actual @?= (Right expected_typ, expected_decs) where
    actual        = runIdentity $ run_state' (create_dec_from_type mk_new_dec_name id_constr_renamer initial) 
                         (built_in_decs, sub_dec_and_rename)
    expected_decs = [DataD [] (mkName "ConT_Int_List") [] [NormalC (mkName "GHC.Types.[]") [],
        InfixC (NotStrict,ConT $ mkName "Int") (mkName "GHC.Types.:") 
            (NotStrict, ConT $ mkName "ConT_Int_List")] []]
    expected_typ  = ConT $ mkName "ConT_Int_List"
    initial       = AppT ListT (ConT $ mkName "Int")
    built_in_decs = [DataD [] (mkName "GHC.Types.[]") [PlainTV $ mkName "a"] 
        [NormalC (mkName "GHC.Types.[]") [], InfixC (NotStrict,VarT $ mkName "a") 
        (mkName "GHC.Types.:") (NotStrict,AppT ListT (VarT $ mkName "a"))] []]

test_find_con_0 = actual @?= expected where
    actual           = find_con (ConstructorName initial_con_name) initial
    expected         = Right initial_con
    initial          = DataD [] (mkName "Dec_Name") [] [initial_con] []
    initial_con      = NormalC initial_con_name []
    initial_con_name = mkName "Test"
    
test_get_con_vars_0 = actual @?= expected where
    actual      = get_con_vars initial
    expected    = [VarT $ mkName "a", VarT $ mkName "b"]
    initial     = NormalC (mkName "Test") $ map (NotStrict,) $ [ConT $ mkName "Test"] ++ expected
         
sub_dec_and_rename_0 = actual @?= Right expected where
    actual              = sub_dec_and_rename id_constr_renamer 
                            initial_dec types
    expected            = DataD [] expected_name []
                            [expected_con_0, expected_con_1] []
    expected_name       = mkName $ initial_name_string ++ "_" ++ concat_type_names types
    expected_con_0      = NormalC (mkName "Test_0") $ map (NotStrict,) $ [ConT $ mkName "Test_0"] 
                                ++ [ConT $ mkName "thing", ConT $ mkName "hello"]
    expected_con_1      = NormalC (mkName "Test_1") $ map (NotStrict,) $ [ConT $ mkName "Test_1"] 
                            ++ [ConT $ mkName "test", ConT $ mkName "test"]
    types               = [ConT $ mkName "test", ConT $ mkName "thing", ConT $ mkName "hello"]
    initial_name_string = "Dec_name"
    initial_name        = mkName initial_name_string
    initial_dec         = DataD [] initial_name (map (PlainTV . mkName) ["a", "b", "c"]) 
                            [initial_con_0, initial_con_1] []
    initial_con_0       = NormalC (mkName "Test_0") $ map (NotStrict,) $ 
                            [ConT $ mkName "Test_0", VarT $ mkName "b", VarT $ mkName "c"]
    initial_con_1       = NormalC (mkName "Test_1") $ map (NotStrict,) $ 
                             [ConT $ mkName "Test_1", VarT $ mkName "a", VarT $ mkName "a"]

    

test_concat_type_names_0 = actual @?= expected where
    actual   = concat_type_names [ConT $ mkName "test", ConT $ mkName "thing"]
    expected = "ConT_test_ConT_thing" 
    
test_rename_dec_0 = actual @?= Right expected where
    actual              = rename_dec types initial_dec 
    expected            = DataD [] expected_name [] [] []
    expected_name       = mkName $ initial_name_string ++ "_" ++ concat_type_names types
    types               = [ConT $ mkName "test", ConT $ mkName "thing"]
    initial_name_string = "Dec_name"
    initial_name        = mkName initial_name_string
    initial_dec         = DataD [] initial_name [] [] []
    
    
    
    
    
    
    
    
    
    
    