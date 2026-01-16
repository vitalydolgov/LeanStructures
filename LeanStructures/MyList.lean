/- # MyList

An implementation of polymorphic lists with verified operations.
All proofs are written in term-style for educational purposes.
-/

/-- A polymorphic list with nil and cons constructors. -/
inductive MyList (α : Type u) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

namespace MyList

infixr:67 " :: " => cons

/-- Returns the number of elements in a list. -/
def length : MyList α → Nat
  | nil => 0
  | _ :: xs => 1 + length xs

-- Length properties

theorem length_nil : length (nil : MyList α) = 0 := rfl

/-- Concatenates two lists. -/
def append : MyList α → MyList α → MyList α
  | nil, ys => ys
  | x :: xs, ys => x :: append xs ys

infixr:65 " ++ " => append

-- Append properties

-- Monoid laws: (MyList α, ++, nil) forms a monoid

/-- Left identity. -/
theorem nil_append (xs : MyList α) : nil ++ xs = xs := rfl

/-- Right identity. -/
theorem append_nil (xs : MyList α) : xs ++ nil = xs :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := append_nil xs
    congrArg (cons x ·) ih

/-- Associativity. -/
theorem append_assoc (xs ys zs : MyList α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := append_assoc xs ys zs
    congrArg (cons x ·) ih

-- Homomorphism property

/-- Length is a monoid homomorphism. -/
theorem length_append (xs ys : MyList α) :
    length (xs ++ ys) = length xs + length ys :=
  match xs with
  | nil => (Nat.zero_add _).symm
  | x :: xs =>
    have ih := length_append xs ys
    calc length ((x :: xs) ++ ys)
      _ = 1 + (length xs + length ys) := congrArg (1 + ·) ih
      _ = (1 + length xs) + length ys := (Nat.add_assoc _ _ _).symm

end MyList
