record Person where
  constructor MkPerson
  name : String
  age : Int

data Field : String -> Type -> Type -> Type where
  F : (label : String) -> (s -> a) -> Field label s a

data R : Type -> Type -> Type where
  (:*:) : f1 -> f2 -> R f1 f2

infixr 10 :*:

nameE : Field "name" Person String
nameE = F "name" Person.name

ageE : Field "age" Person Int
ageE = F "age" Person.age

personR : R (Field "name" Person String) (Field "age" Person Int)
personR = nameE :*: ageE

gatherFields : {a : Type} -> {b : Type} -> R (Field lbl a b) rest -> List String
gatherFields (F lbl f :*: rest) = [lbl, lbl] -- lbl :: gatherFields rest

phil : Person
phil = MkPerson "asd" 55

main : IO ()
main = do
  print $ gatherFields personR
