module typeclass where

open import Data.Bool
open import Data.Nat hiding (_<_; _>_; _≤_; _≥_)

record Eq (A : Set) : Set where
  field
    _==_ : A → A → Bool

  _/=_ : A → A → Bool
  x /= y = not (x == y)

  infixr 3 _==_ _/=_

open Eq ⦃...⦄ public

instance
  Eqℕ : Eq ℕ
  _==_ {{Eqℕ}} = Agda.Builtin.Nat._==_ where open import Agda.Builtin.Nat

instance
  EqBool : Eq Bool
  _==_ {{EqBool}} false t = not t
  _==_ {{EqBool}} true t  = t

open import Data.List

instance
  EqList : {A : Set} ⦃ _ : Eq A ⦄ → Eq (List A)
  _==_ ⦃ EqList ⦄ [] [] = true
  _==_ ⦃ EqList ⦄ [] (_ ∷ _) = false
  _==_ ⦃ EqList ⦄ (_ ∷ _) [] = false
  _==_ ⦃ EqList ⦄ (x ∷ xs) (y ∷ ys) = (x == y) ∧ (xs == ys)

record Ord (A : Set) : Set where
  field
    _<_ : A → A → Bool
    overlap ⦃ eqA ⦄ : Eq A
    
  _≤_ : A → A → Bool
  x ≤ y = (x < y) ∨ (x == y)
  _>_ : A → A → Bool
  x > y = not (x ≤ y)
  _≥_ : A → A → Bool
  x ≥ y = (x > y) ∨ (x == y)

open Ord ⦃...⦄ hiding (eqA)

instance
  Ordℕ : Ord ℕ
  _<_ ⦃ Ordℕ ⦄ = Agda.Builtin.Nat._<_ where open import Agda.Builtin.Nat

  OrdBool : Ord Bool
  _<_ {{OrdBool}} false t = t
  _<_ {{OrdBool}} true _ = false


record Num (A : Set) : Set where
  field
    fromℕ : ℕ → A
    overlap ⦃ eqA ⦄ : Eq A
open Num ⦃...⦄ hiding (eqA)

instance
  Numℕ : Num ℕ
  fromℕ ⦃ Numℕ ⦄ n = n

_≤3 : {A : Set} ⦃ _ : Ord A ⦄ ⦃ _ : Num A ⦄ → A → Bool
x ≤3 = x ≤ fromℕ 3
