/- Copyright (c) 2024 Theodora Brick.

Authors: Thea Brick
-/

/- Some additional utilities that are commonly used. -/

def String.leftpad (s : String) (n : Nat) (padding : Char) : String :=
  ⟨.replicate (n - s.data.length) padding ++ s.data⟩

def String.leftpad0 (s : String) (n : Nat) := String.leftpad s n '0'

theorem Nat.zero_eq_add (n m : Nat) : 0 = n + m ↔ n = 0 ∧ m = 0 := by
  apply Iff.intro <;> intro h
  . cases n with
    | zero => simp at *; exact h.symm
    | succ n =>
      cases m with
      | zero => contradiction
      | succ m => contradiction
  . rw [h.left, h.right]
