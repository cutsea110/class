module typeclass where

open import Data.Bool
open import Data.Nat hiding (_<_; _>_)

record Eq (A : Set) : Set where
  field _==_ : A → A → Bool
  _/=_ : A → A → Bool
  _/=_ = _==_

  infixr 3 _==_ _/=_

open Eq ⦃...⦄ public

instance
  Eqℕ : Eq ℕ
  _==_ {{Eqℕ}} zero zero       = true
  _==_ {{Eqℕ}} zero (suc _)    = false
  _==_ {{Eqℕ}} (suc _) zero    = false
  _==_ {{Eqℕ}} (suc x) (suc y) = x == y

instance
  EqBool : Eq Bool
  _==_ {{EqBool}} false t = not t
  _==_ {{EqBool}} true t  = t

open import Data.List

instance
  EqList : {A : Set} ⦃ _ : Eq A ⦄ → Eq (List A)
  _==_ {{EqList}} [] [] = true
  _==_ {{EqList}} [] (_ ∷ _) = false
  _==_ {{EqList}} (_ ∷ _) [] = false
  _==_ {{EqList}} (x ∷ xs) (y ∷ ys) = (x == y) ∧ (xs == ys)

record Ord (A : Set) : Set where
  field _<_ : A → A → Bool
        _>_ : A → A → Bool
        _<=_ : A → A → Bool
        _>=_ : A → A → Bool
        overlap ⦃ eqA ⦄ : Eq A

open Ord ⦃...⦄ hiding (eqA)
