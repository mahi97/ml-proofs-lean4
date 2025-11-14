import Mathlib

#eval 1 + 1

theorem add_comm_example (a b : ℕ) : a + b = b + a := by
  simp [Nat.add_comm]
