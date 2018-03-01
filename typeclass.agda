module typeclass where

open import Data.Bool
open import Data.Nat hiding (_<_; _>_; _≤_; _≥_) renaming (_∸_ to _-_)

record Eq (A : Set) : Set where
  field
    _==_ : A → A → Bool

  _/=_ : A → A → Bool
  x /= y = not (x == y)

  infixr 3 _==_ _/=_
open Eq {{...}} public

instance
  Eqℕ : Eq ℕ
  _==_ {{Eqℕ}} = Agda.Builtin.Nat._==_ where open import Agda.Builtin.Nat

instance
  EqBool : Eq Bool
  _==_ {{EqBool}} false t = not t
  _==_ {{EqBool}} true t  = t

open import Data.List

instance
  EqList : {A : Set} {{_ : Eq A}} → Eq (List A)
  _==_ {{EqList}} [] [] = true
  _==_ {{EqList}} [] (_ ∷ _) = false
  _==_ {{EqList}} (_ ∷ _) [] = false
  _==_ {{EqList}} (x ∷ xs) (y ∷ ys) = (x == y) ∧ (xs == ys)

record Ord (A : Set) : Set where
  field
    _<_ : A → A → Bool
    overlap {{eqA}} : Eq A
    
  _≤_ : A → A → Bool
  x ≤ y = (x < y) ∨ (x == y)
  _>_ : A → A → Bool
  x > y = not (x ≤ y)
  _≥_ : A → A → Bool
  x ≥ y = (x > y) ∨ (x == y)
open Ord {{...}} hiding (eqA)

instance
  Ordℕ : Ord ℕ
  _<_ {{Ordℕ}} = Agda.Builtin.Nat._<_ where open import Agda.Builtin.Nat

  OrdBool : Ord Bool
  _<_ {{OrdBool}} false t = t
  _<_ {{OrdBool}} true _ = false


record Num (A : Set) : Set where
  field
    fromℕ : ℕ → A
    overlap {{eqA}} : Eq A
open Num {{...}} hiding (eqA)

instance
  Numℕ : Num ℕ
  fromℕ {{Numℕ}} n = n

_≤3 : {A : Set} {{_ : Ord A}} {{_ : Num A}} → A → Bool
x ≤3 = x ≤ fromℕ 3


data _≡_ {A : Set} (x : A) : A → Set where
  instance refl : x ≡ x

infixr 3 _≡_

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  succ : {n : ℕ} → Fin n → Fin (suc n)

mkFin : {n : ℕ} (m : ℕ) {{_ : suc m - n ≡ 0}} → Fin n
mkFin {zero} m {{}} -- absurd
mkFin {suc n} zero = zero
mkFin {suc n} (suc m) = succ (mkFin m)

five : Fin 6
five = mkFin 5

-- see above mkFin
mkFin' : {n : ℕ} (m : ℕ) {p : suc m - n ≡ 0} → Fin n
mkFin' {zero} m {} -- absurd
mkFin' {suc n} zero {p} = zero
mkFin' {suc n} (suc m) {p} = succ (mkFin' {n} m {p})

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  instance
    zero : ∀ {xs} →  x ∈ x ∷ xs
    succ : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x

ex₁ : 1 + 2 ∈ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
ex₁ = it -- succ (succ zero)

ex₂ : {A : Set} (x y : A) (xs : List A) → x ∈ y ∷ y ∷ x ∷ xs
ex₂ x y xs = it -- succ (succ zero)

ex₃ : {A : Set} (x y : A) (xs : List A) {{i : x ∈ xs}} → x ∈ y ∷ y ∷ xs
ex₃ x y xs {{i}} = it -- succ (succ i)
