import Mathlib.Data.Nat.Basic

variable (A : ℕ → Type)

example (m n : ℕ) (h : m = n) : A m = A n := by subst h; rfl -- or `rw [h]`

example (A : ℕ → Type) : A (2 + 2) = A 4 := rfl

example (m n : ℕ) : A (m + n) = A (n + m) := by rw [add_comm]  -- `rfl` fails

def f (m n : ℕ) (h : m = n) : A m → A n := fun a ↦ by rw [← h]; exact a  -- `a` fails since it has the wrong type. Therefore this function is not identity.

#check f (A : ℕ → Type) 2 2 rfl

example : f (A : ℕ → Type) (2 + 2) 4 rfl = @id (A 4) := rfl

example : f (A : ℕ → Type) (2 + 2) 4 rfl = @id (A 4) := by ext x; rfl

example : f (A : ℕ → Type) 2 2 rfl = @id (A 2) := rfl

example (m n : ℕ) : f (A : ℕ → Type) (m + n) (n + m) (add_comm m n) = @id (A (m + n)) := sorry -- m + n = n + m is a propostitional equality and therefore the types `A (m + n)` and `A (n + m)` are not definitionally equal.
