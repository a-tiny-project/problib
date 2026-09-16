import Lean

namespace Trust

open Lean

structure Policy where
  allowed : Array Name

def trustCeiling : Array Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

def formatNames (names : Array Name) : String :=
  String.intercalate ", " (names.map toString).toList

def sortedNames (names : Array Name) : Array Name :=
  names.qsort Name.lt

def duplicateNames (names : Array Name) : Array Name := Id.run do
  let mut previous : Option Name := none
  let mut duplicates := #[]
  for name in sortedNames names do
    if previous == some name then
      if duplicates.back? != some name then
        duplicates := duplicates.push name
    previous := some name
  return duplicates

def Policy.permits (policy : Policy) (name : Name) : Bool :=
  policy.allowed.contains name

def Policy.create (allowed : Array Name) : Except String Policy := do
  let duplicates := duplicateNames allowed
  unless duplicates.isEmpty do
    throw s!"duplicate allowed axioms [{formatNames duplicates}]"
  let outside := sortedNames <| allowed.filter fun name =>
    !trustCeiling.contains name
  unless outside.isEmpty do
    throw s!"allowed axioms exceed trust ceiling [{formatNames outside}]"
  return { allowed := sortedNames allowed }

end Trust
