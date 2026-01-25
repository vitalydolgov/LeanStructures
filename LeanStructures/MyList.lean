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

/-! ## Membership -/

def Mem (a : α) : MyList α → Prop
  | nil => False
  | x :: xs => a = x ∨ Mem a xs

instance : Membership α (MyList α) where
  mem := flip Mem

theorem mem_nil : a ∈ nil ↔ False := Iff.rfl

theorem mem_cons : a ∈ (cons x xs) ↔ a = x ∨ a ∈ xs := Iff.rfl

/-! ## Length -/

/-- Returns the number of elements in a list. -/
def length : MyList α → Nat
  | nil => 0
  | _ :: xs => 1 + length xs

/-- Length of empty list is zero. -/
theorem length_nil : length (nil : MyList α) = 0 := rfl

/-! ## Append -/

/-- Concatenates two lists. -/
def append : MyList α → MyList α → MyList α
  | nil, ys => ys
  | x :: xs, ys => x :: append xs ys

infixr:65 " ++ " => append

/-! ### Characterization

    An element belongs to the concatenation of two lists
    if and only if it belongs to at least one of them. -/

theorem mem_append :
    a ∈ (xs ++ ys) ↔ a ∈ xs ∨ a ∈ ys :=
  match xs with
  | nil =>
    Iff.intro
      (fun h => Or.inr h)
      (fun h =>
        match h with
        | Or.inl hfalse => False.elim hfalse
        | Or.inr hmem => hmem)
  | _ :: xs =>
    have ih := mem_append (xs := xs) (ys := ys) (a := a)
    Iff.intro
      (fun h =>
        match h with
        | Or.inl heq => Or.inl (Or.inl heq)
        | Or.inr hmem =>
          match ih.mp hmem with
          | Or.inl hmem_tl => Or.inl (Or.inr hmem_tl)
          | Or.inr hmem_ys => Or.inr hmem_ys
        )
      (fun h =>
        match h with
        | Or.inl hmem_cons =>
          match hmem_cons with
          | Or.inl heq_hd => Or.inl heq_hd
          | Or.inr hmem_tl => Or.inr (ih.mpr (Or.inl hmem_tl))
        | Or.inr hmem_ys => Or.inr (ih.mpr (Or.inr hmem_ys)))

/-! ### Monoid Laws

    `(MyList α, ++, nil)` forms a monoid with identity and associativity. -/

theorem append_nil (xs : MyList α) : xs ++ nil = xs :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := append_nil xs
    congrArg (cons x ·) ih

theorem append_assoc (xs ys zs : MyList α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := append_assoc xs ys zs
    congrArg (cons x ·) ih

/-! ### Monoid Homomorphism

    `length` is a monoid homomorphism from `(MyList α, ++, nil)` to `(Nat, +, 0)`.
    Note: `length_nil` serves double duty as the unit law. -/

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
  | nil => (append_nil (reverse ys)).symm
  | x :: xs =>
    have ih := reverse_append xs ys
    calc reverse (x :: xs ++ ys) = reverse (xs ++ ys) ++ x :: nil := rfl
      _ = (reverse ys ++ reverse xs) ++ x :: nil := by rw [ih]
      _ = reverse ys ++ reverse xs ++ x :: nil := by rw [append_assoc]

/-- Reverse is an involution: applying it twice yields identity. -/
theorem reverse_reverse (xs : MyList α) :
    reverse (reverse xs) = xs :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := reverse_reverse xs
    calc reverse (reverse (x :: xs)) = reverse (reverse xs ++ x :: nil) := rfl
      _ = reverse (x :: nil) ++ reverse (reverse xs) := by rw [reverse_append]
      _ = reverse (x :: nil) ++ xs := by rw [ih]

/-- Length is invariant under reverse. -/
theorem length_reverse (xs : MyList α) :
    length (reverse xs) = length xs :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := length_reverse xs
    calc length (reverse (x :: xs)) = length (reverse xs ++ x :: nil) := rfl
      _ = length (reverse xs) + length (x :: nil) := by rw [length_append]
      _ = length xs + length (x :: nil) := by rw [ih]
      _ = 1 + length xs := by ac_rfl

/-- Reverse is injective (one-to-one). -/
theorem reverse_injective (xs ys : MyList α) :
    reverse xs = reverse ys → xs = ys := fun h =>
  calc xs
    _ = reverse (reverse xs) := by symm; rw [reverse_reverse]
    _ = reverse (reverse ys) := by rw [h]
    _ = ys := by rw [reverse_reverse]

/-- Characterization of reverse equality. -/
theorem reverse_eq_iff (xs ys : MyList α) :
    reverse xs = ys ↔ xs = reverse ys :=
  Iff.intro
    (fun h =>
      calc xs
        _ = reverse (reverse xs) := by symm; rw [reverse_reverse]
        _ = reverse ys := by rw [h]
    )
    (fun h =>
      calc reverse xs
        _ = reverse (reverse ys) := by rw [h]
        _ = ys := by rw [reverse_reverse]
    )

/-! ## Map -/

/-- Applies a function to every element of a list. -/
def map : (α → β) → MyList α → MyList β
  | _, nil => nil
  | f, x :: xs => f x :: map f xs

/-! ### Characterization

    An element belongs to the image if and only if it has a preimage. -/

theorem mem_map :
    y ∈ map f xs ↔ ∃ x, x ∈ xs ∧ f x = y :=
  match xs with
  | nil =>
    Iff.intro
      (fun h => False.elim h)
      (fun ⟨_, hmem, _⟩ => False.elim hmem)
  | x :: xs =>
    have ih := mem_map (xs := xs) (f := f) (y := y)
    Iff.intro
      (fun h =>
        match h with
        | Or.inl heq => ⟨x, Or.inl rfl, heq.symm⟩
        | Or.inr hmem_map =>
          have ⟨wit, hmem_wit_tl, heq_fwit⟩ := ih.mp hmem_map
          ⟨wit, Or.inr hmem_wit_tl, heq_fwit⟩)
      (fun h =>
        have ⟨wit, hmem_wit_cons, heq_fwit⟩ := h
        match hmem_wit_cons with
        | Or.inl heq_wit_hd =>
          Or.inl (heq_fwit ▸ heq_wit_hd ▸ rfl)
        | Or.inr hmem_wit_tl =>
          Or.inr (ih.mpr ⟨wit, hmem_wit_tl, heq_fwit⟩))

/-! ### Computation Rules

    One equation per constructor of `MyList`. -/

theorem map_nil :
    map f nil = nil := rfl

theorem map_cons (f : α → β) (xs : MyList α) :
    map f (x :: xs) = f x :: map f xs := rfl

/-! ### Functor Laws

    `(MyList, map)` forms a functor with identity and composition laws. -/

theorem map_id (xs : MyList α) :
    map id xs = xs :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := map_id xs
    congrArg (cons x ·) ih

theorem map_map (f : α → β) (g : β → γ) (xs : MyList α) :
    map g (map f xs) = map (g ∘ f) xs :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := map_map f g xs
    calc map g (map f (x :: xs))
      _ = (g ∘ f) x :: map g (map f xs) := rfl
      _ = (g ∘ f) x :: map (g ∘ f) xs := by rw [ih]

/-! ### Monoid Homomorphism

    `(MyList α, ++, nil)` is a monoid. `map f` is a monoid homomorphism.
    Note: map_nil serves double duty as the unit law. -/

theorem map_append (f : α → β) (xs ys : MyList α) :
    map f (xs ++ ys) = map f xs ++ map f ys :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := map_append f xs ys
    calc map f ((x :: xs) ++ ys)
      _ = f x :: map f (xs ++ ys) := rfl
      _ = f x :: (map f xs ++ map f ys) := by rw [ih]

/-! ### Naturality

    `length` is invariant under `map`.
    `reverse` commutes with `map`. -/

theorem length_map (f : α → β) (xs : MyList α) :
    length (map f xs) = length xs :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := length_map f xs
    calc length (map f (x :: xs))
      _ = 1 + length (map f xs) := rfl
      _ = 1 + length xs := by rw [ih]

theorem map_reverse (f : α → β) (xs : MyList α) :
    map f (reverse xs) = reverse (map f xs) :=
  match xs with
  | nil => rfl
  | x :: xs =>
    have ih := map_reverse f xs
    calc map f (reverse (x :: xs))
      _ = map f (reverse xs ++ x :: nil) := rfl
      _ = map f (reverse xs) ++ map f (x :: nil) := by rw [map_append]
      _ = reverse (map f xs) ++ map f (x :: nil) := by rw [ih]

/-! ### Injectivity -/

theorem map_injective
  (f : α → β) (hinj : Function.Injective f) (xs ys : MyList α) :
    map f xs = map f ys → xs = ys :=
  fun heq =>
    match xs, ys with
    | nil, nil => rfl
    | x :: xs, y :: ys =>
      have heq_decomp := MyList.cons.inj heq
      have hh : x = y := hinj heq_decomp.1
      have heq' : map f xs = map f ys := heq_decomp.2
      have ht : xs = ys := map_injective f hinj xs ys heq'
      calc x :: xs
        _ = y :: xs := congrArg (cons · xs) hh
        _ = y :: ys := congrArg (cons y ·) ht

end MyList
