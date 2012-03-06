module TestType where
    
data TestType = TestType Int

data PolyType a = PolyType a

data TestTypeInt = TestTypeInt (PolyType Int)