import Mathlib.Data.Nat.Basic
import Mathlib.CategoryTheory.Category.Basic
/-
In Lean:

Sort 0 = Prop
Sort 1 = Type 0 = Type
Sort 2 = Type 1 -- The type of types
-/

#check 0 = 1
#check Prop
#check ℕ
#check Type
#check Type 1

#check Quiver
#check Quiver.{0} -- Homs are props
#check Quiver.{0} ℕ -- Homs are props, objects are natural numbers
#check Quiver.{1} ℕ -- Homs are types, objects are natural numbers

#check Quiver.{0} Type -- Homs are props
#check Quiver.{1} Type -- Homs are types

#check Quiver.{0} ℕ
