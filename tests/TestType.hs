module TestType where
    
data TestType = TestType Int

data PolyType a = PolyType a

data TestTypeInt = TestTypeInt (PolyType Int)

type IntList = [Int]

data ListLike = ListLike
    {
        values :: IntList
    }
    deriving(Show, Eq)