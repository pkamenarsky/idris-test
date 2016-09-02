record Person where
  constructor MkPerson
  name : String
  age : Int

data Field : String -> Type -> Type -> Type where
  F : (label : String) -> (s -> a) -> Field label s a

data U = UI

data R : Type where
  NR : R
  (:*:) : {lbl : String} -> (Field lbl a b) -> R -> R

infixr 10 :*:

nameE : Field "name" Person String
nameE = F "name" Person.name

ageE : Field "age" Person Int
ageE = F "age" Person.age

personR : R
personR = nameE :*: (ageE :*: NR)

total
gatherFields : R -> List String
gatherFields NR = []
gatherFields (F lbl f :*: rest) = lbl :: gatherFields rest
gatherFields (F lbl f :*: NR)   = [lbl]

-- checkPerms : ["name", "age"] = gatherFields personR
-- checkPerms = Refl

phil : Person
phil = MkPerson "asd" 55

main : IO ()
main = do
  case ["name", "age"] == gatherFields personR of
    True  => print "Yes"
    False => print "No"
