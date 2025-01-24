Axiom ℕ : Type.
Axiom zero : ℕ.
Axiom succ : ℕ -> ℕ.
Definition ten := 10.
Axiom + : ℕ -> ℕ -> ℕ.
Axiom × : ℕ -> ℕ -> ℕ.
Axiom Prop : Type.
Axiom = : ℕ -> ℕ -> Prop.
Axiom Prf : Prop -> Type.
Axiom =-refl : forall x, Prf (x = x).
Axiom =-succ : forall x y, (Prf (x = y)) -> Prf (succ x = succ y).
Axiom ind_ℕ : forall (p : ℕ -> Prop) (case-zero : Prf (p zero)) (case-succ : forall x : ℕ, (Prf (p x)) -> Prf (p (succ x))) (n : ℕ), Prf (p n).
Axiom Set : Type.
Axiom τ : Set -> Type.
Axiom nat : Set.
Axiom ≃ : forall {a}, (τ a) -> (τ a) -> Prop.
Axiom ≃-refl : forall {a} (x : τ a), Prf (x ≃ x).
Axiom ≃-ind : forall {a} {x y : τ a}, (Prf (x ≃ y)) -> forall p, (Prf (p y)) -> Prf (p x).
Axiom ⊕ : Nat -> Nat -> Nat.