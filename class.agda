module class where

open import Data.Bool
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

record Ord {t : Set} (eqT : Eq t) : Set where
  field _<_ : t → t → Bool
  _<=_ : t → t → Bool
  x <= y = x < y ∨ x === y where open Eq eqT renaming (_==_ to _===_)
  _>_ : t → t → Bool
  x > y = not (x <= y)
  _>=_ : t → t → Bool
  x >= y = y <= x

instance
  ltN : Ord eqN
  ltN = record { _<_ = lt' }
    where
      lt' : ℕ → ℕ → Bool
      lt' zero zero = false
      lt' zero (suc m) = true
      lt' (suc n) zero = false
      lt' (suc n) (suc m) = lt' n m
  ltB : Ord eqB
  ltB = record { _<_ = lt' }
    where
      lt' : Bool → Bool → Bool
      lt' false false = false
      lt' false true = false
      lt' true false = true
      lt' true true = false

open Ord ⦃ ... ⦄ using (_<_)

test₁ : Bool
test₁ = 5 < 3 ∨ false < true
test₂ : Bool
test₂ = false < true ∧ 5 < 3

open import Data.List


listEq : {t : Set} → ⦃ eqT : Eq t ⦄ → Eq (List t)
listEq {t} ⦃ eqT ⦄ = record { _==_ = eq' }
  where
    eq' : List t → List t → Bool
    eq' [] [] = true
    eq' [] (y ∷ ys) = false
    eq' (x ∷ xs) [] = false
    eq' (x ∷ xs) (y ∷ ys) = x == y ∧ eq' xs ys
{--
test₃ = Eq._==_ listEq (1 ∷ []) (1 ∷ 2 ∷ [])
test₄ = (1 ∷ []) == (1 ∷ 2 ∷ [])
  where listEqN = listEq ⦃ eqN ⦄ -- need this!

test₅ = (true ∷ false ∷ []) == (true ∷ false ∷ [])
  where listEqB = listEq ⦃ eqB ⦄ -- need this!
--}
