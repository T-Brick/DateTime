/- Copyright (c) 2024 Theodora Brick.

Authors: Thea Brick
-/

/- Some additional utilities that are commonly used. -/

def String.leftpad (s : String) (n : Nat) (padding : Char) : String :=
  ⟨.replicate (n - s.data.length) padding ++ s.data⟩

def String.leftpad0 (s : String) (n : Nat) := String.leftpad s n '0'
