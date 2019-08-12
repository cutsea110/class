module class where

open import Data.Bool hiding (_<_)
open import Data.Nat hiding (_<_; _>_)

record Eq (t : Set) : Set where
  field _==_ : t → t → Bool
  _/=_ : t → t → Bool
  x /= y = not (x == y)

open Eq ⦃ ... ⦄

instance
  eqN : Eq ℕ
  eqN = record { _==_ = eq' }
    where
      eq' : ℕ → ℕ → Bool
      eq' zero zero = true
      eq' zero (suc m) = false
      eq' (suc n) zero = false
      eq' (suc n) (suc m) = eq' n m
  eqB : Eq Bool
  eqB = record { _==_ = eq' }
    where
      eq' : Bool → Bool → Bool
      eq' false false = true
      eq' false true = false
      eq' true false = false
      eq' true true = true

test₀ : Bool
test₀ = true == false ∨ 4 /= 5

record Ord (t : Set) : Set where
  field
    eqT : Eq t
    _<_ : t → t → Bool
  _<=_ : t → t → Bool
  x <= y = x < y ∨ x === y where open Eq eqT renaming (_==_ to _===_)
  _>_ : t → t → Bool
  x > y = not (x <= y)
  _>=_ : t → t → Bool
  x >= y = y <= x

open Ord ⦃ ... ⦄

instance
  ordN : Ord ℕ
  ordN = record { eqT = eqN; _<_ = lt' }
    where
      lt' : ℕ → ℕ → Bool
      lt' zero zero = false
      lt' zero (suc y) = true
      lt' (suc x) zero = false
      lt' (suc x) (suc y) = lt' x y

  ordB : Ord Bool
  ordB = record { eqT = eqB; _<_ = lt' }
    where
      lt' : Bool → Bool → Bool
      lt' false false = false
      lt' false true = false
      lt' true false = true
      lt' true true = false

test₁ : Bool
test₁ = 5 < 3 ∧ false < true
test₂ : Bool
test₂ = 5 <= 3 ∨ false <= true
test₃ : Bool
test₃ = 5 > 3 ∧ false > true
test₄ : Bool
test₄ = 5 >= 3 ∨ false >= true

open import Data.List

instance
  listEq : {t : Set} → ⦃ eqT : Eq t ⦄ → Eq (List t)
  listEq {t} ⦃ eqT ⦄ = record { _==_ = eq' }
    where
      eq' : List t → List t → Bool
      eq' [] [] = true
      eq' [] (x ∷ y) = false
      eq' (x ∷ x₁) [] = false
      eq' (x ∷ xs) (y ∷ ys) = x == y ∧ eq' xs ys

test₅ : Bool
test₅ = (1 ∷ []) == (2 ∷ 3 ∷ []) ∧ (true ∷ []) /= (false ∷ true ∷ [])

instance
  listOrd : {t : Set} → ⦃ ordT : Ord t ⦄ → Ord (List t)
  listOrd {t} ⦃ ordT ⦄ = record { eqT = listEq {t} ⦃ eqT ⦄ ; _<_ = lt' }
    where
      lt' : List t → List t → Bool
      lt' [] [] = false
      lt' [] (x ∷ y) = true
      lt' (x ∷ xs) [] = false
      lt' (x ∷ xs) (y ∷ ys) = x < y ∧ lt' xs ys

test₆ : Bool
test₆ = (1 ∷ []) < (2 ∷ 3 ∷ []) ∧ (true ∷ []) < (false ∷ true ∷ [])

test₇ : Bool
test₇ = (1 ∷ []) <= (2 ∷ 3 ∷ []) ∧ (true ∷ []) <= (false ∷ true ∷ [])

test₈ : Bool
test₈ = (1 ∷ []) > (2 ∷ 3 ∷ []) ∧ (true ∷ []) > (false ∷ true ∷ [])

test₉ : Bool
test₉ = (1 ∷ []) >= (2 ∷ 3 ∷ []) ∧ (true ∷ []) >= (false ∷ true ∷ [])
