/- # MyList

An implementation of polymorphic lists with verified operations.
All proofs are written in term-style for educational purposes.
-/

/-- A polymorphic list with nil and cons constructors. -/
inductive MyList (α : Type u) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

namespace MyList

/-- Converts a standard List to MyList. -/
def mk : List α → MyList α
  | [] => nil
  | x :: xs => cons x (mk xs)

infixr:67 " :: " => cons

/-! ## Length -/

/-- Returns the number of elements in a list. -/
def length : MyList α → Nat
  | nil => 0
  | _ :: xs => 1 + length xs

theorem length_nil : length (nil : MyList α) = 0 := rfl

/-! ## Append -/

/-- Concatenates two lists. -/
def append : MyList α → MyList α → MyList α
  | nil, ys => ys
  | x :: xs, ys => x :: append xs ys

infixr:65 " ++ " => append

/-- Left identity for append. -/
theorem nil_append (xs : MyList α) : nil ++ xs = xs := rfl

/-- Right identity for append. -/
theorem append_nil (xs : MyList α) : xs ++ nil = xs :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := append_nil xs
    congrArg (cons x ·) ih

/-- Associativity of append. -/
theorem append_assoc (xs ys zs : MyList α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := append_assoc xs ys zs
    congrArg (cons x ·) ih

/-- Length is a monoid homomorphism from (MyList, ++, nil) to (Nat, +, 0). -/
theorem length_append (xs ys : MyList α) :
    length (xs ++ ys) = length xs + length ys :=
  match xs with
  | nil => (Nat.zero_add _).symm
  | x :: xs =>
    have ih := length_append xs ys
    calc length ((x :: xs) ++ ys)
      _ = 1 + length (xs ++ ys) := rfl
      _ = 1 + (length xs + length ys) := by rw [ih]
      _ = (1 + length xs) + length ys := by ac_rfl

/-! ## Reverse -/

/-- Reverses a list. -/
def reverse : MyList α → MyList α
  | nil => nil
  | x :: xs => reverse xs ++ x :: nil

/-- Reverse of empty list is empty. -/
theorem reverse_nil :
    reverse (nil : MyList α) = nil := rfl

/-- Singleton lists are fixed points of reverse. -/
theorem reverse_singleton (x : α) :
    reverse (x :: nil) = x :: nil := rfl

/-- Reverse is an anti-homomorphism: it reverses the order of concatenation. -/
theorem reverse_append (xs ys : MyList α) :
    reverse (xs ++ ys) = reverse ys ++ reverse xs :=
  match xs with
  | nil => by symm; apply append_nil
  | x :: xs =>
    have ih := reverse_append xs ys
    calc reverse (x :: xs ++ ys) = reverse (xs ++ ys) ++ x :: nil := rfl
      _ = (reverse ys ++ reverse xs) ++ x :: nil := by rw [ih]
      _ = reverse ys ++ reverse xs ++ x :: nil := by apply append_assoc

/-- Reverse is an involution: applying it twice yields identity. -/
theorem reverse_reverse (xs : MyList α) :
    reverse (reverse xs) = xs :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := reverse_reverse xs
    calc reverse (reverse (x :: xs)) = reverse (reverse xs ++ x :: nil) := rfl
      _ = reverse (x :: nil) ++ reverse (reverse xs) := by apply reverse_append
      _ = reverse (x :: nil) ++ xs := by rw [ih]

/-- Length is invariant under reverse. -/
theorem length_reverse (xs : MyList α) :
    length (reverse xs) = length xs :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := length_reverse xs
    calc length (reverse (x :: xs)) = length (reverse xs ++ x :: nil) := rfl
      _ = length (reverse xs) + length (x :: nil) := by apply length_append
      _ = length xs + length (x :: nil) := by rw [ih]
      _ = 1 + length xs := by ac_rfl

/-- Reverse is injective (one-to-one). -/
theorem reverse_injective (xs ys : MyList α) :
    reverse xs = reverse ys → xs = ys := fun h =>
  calc xs
    _ = reverse (reverse xs) := by symm; apply reverse_reverse
    _ = reverse (reverse ys) := by rw [h]
    _ = ys := by apply reverse_reverse

/-- Characterization of reverse equality. -/
theorem reverse_eq_iff (xs ys : MyList α) :
    reverse xs = ys ↔ xs = reverse ys :=
  Iff.intro
    (fun h =>
      calc xs
        _ = reverse (reverse xs) := by symm; apply reverse_reverse
        _ = reverse ys := by rw [h]
    )
    (fun h =>
      calc reverse xs
        _ = reverse (reverse ys) := by rw [h]
        _ = ys := by apply reverse_reverse
    )

end MyList
