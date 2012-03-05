{-# LANGUAGE TupleSections, NoMonomorphismRestriction, TemplateHaskell #-}
module Main where
import Language.Haskell.TH
import Test.Framework (defaultMain, testGroup, defaultMainWithArgs)
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck
import Test.HUnit
import Debug.Trace.Helpers
import Debug.Trace
import Language.Haskell.TH.Instances
import Test.QuickCheck.Checkers
import Data.List
import Data.Generics.Uniplate.Data
import Control.Applicative ((<$>))
import Language.Haskell.TH.Specialize

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
            ]]

test_find_con_0 = actual @?= expected where
    actual           = find_con initial_con_name initial
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
                            initial_dec initial_con_name types
    expected            = DataD [] expected_name (map (PlainTV . mkName) ["a"])
                            [expected_con, initial_con_1] []
    expected_name       = mkName $ initial_name_string ++ "_" ++ concat_type_names types
    expected_con        = NormalC (mkName "Test") $ map (NotStrict,) $ [ConT $ mkName "Test"] 
                                ++ types
    types               = [ConT $ mkName "test", ConT $ mkName "thing"]
    initial_name_string = "Dec_name"
    initial_name        = mkName initial_name_string
    initial_dec         = DataD [] initial_name (map (PlainTV . mkName) ["a", "b", "c"]) 
                            [initial_con_0, initial_con_1] []
    initial_con_0       = NormalC initial_con_name $ map (NotStrict,) $ 
                            [ConT $ mkName "Test", VarT $ mkName "b", VarT $ mkName "c"]
    initial_con_1       = NormalC initial_con_name $ map (NotStrict,) $ 
                             [ConT $ mkName "Test", VarT $ mkName "a", VarT $ mkName "a"]

    initial_con_name    = mkName "Test"
    

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
    
    
    
    
    
    
    
    
    
    
    