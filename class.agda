module class where

open import Data.Bool
open import Data.Nat hiding (_<_; _>_)

record Eq (t : Set) : Set where
  field _==_ : t → t → Bool
  _/=_ : t → t → Bool
  x /= y = not (x == y)

eqN : Eq ℕ
eqN = record { _==_ = eq' }
  where
    eq' : ℕ → ℕ → Bool
    eq' zero zero = true
    eq' zero (suc n) = false
    eq' (suc m) zero = true
    eq' (suc m) (suc n) = eq' m n

eqB : Eq Bool
eqB = record { _==_ = eq' }
  where
    eq' : Bool → Bool → Bool
    eq' true true = true
    eq' true false = false
    eq' false true = false
    eq' false false = true

{--
_==_ : {t : Set} → ⦃ eqT : Eq t ⦄ → t → t → Bool
_==_ ⦃ eqT ⦄ = Eq._==_ eqT
_/=_ : {t : Set} → ⦃ eqT : Eq t ⦄ → t → t → Bool
_/=_ ⦃ eqT ⦄ = Eq._/=_ eqT
--}

-- module EqInst {t} ⦃ eqT : Eq t ⦄ = Eq eqT
open Eq ⦃ ... ⦄ using (_==_; _/=_)

test : Bool
test = true == false ∨ 4 /= 5

record Ord {t : Set} (eqT : Eq t) : Set where
  field _<_ : t → t → Bool
  _<=_ : t → t → Bool
  x <= y = x < y ∨ x == y
  _>_ : t → t → Bool
  x > y = not (x <= y)
  _>=_ : t → t → Bool
  x >= y = x > y ∨ x == y

ltN : Ord {ℕ} eqN
ltN = record { _<_ = lt' }
  where
    lt' : ℕ → ℕ → Bool
    lt' zero zero = false
    lt' zero (suc m) = true
    lt' (suc n) zero = false
    lt' (suc n) (suc m) = lt' n m

ltB : Ord {Bool} eqB
ltB = record { _<_ = lt' }
  where
    lt' : Bool → Bool → Bool
    lt' true true = false
    lt' true false = false
    lt' false true = true
    lt' false false = false

open Ord ⦃ ... ⦄ using (_<_)

test₁ = 5 < 3
test₂ = false < true

open import Data.List


listEq : {t : Set} → ⦃ eqT : Eq t ⦄ → Eq (List t)
listEq {t} ⦃ eqT ⦄ = record { _==_ = eq' }
  where
    eq' : List t → List t → Bool
    eq' [] [] = true
    eq' [] (y ∷ ys) = false
    eq' (x ∷ xs) [] = false
    eq' (x ∷ xs) (y ∷ ys) = x == y ∧ eq' xs ys

test₃ = Eq._==_ listEq (1 ∷ []) (1 ∷ 2 ∷ [])
test₄ = (1 ∷ []) == (1 ∷ 2 ∷ [])
  where listEqN = listEq ⦃ eqN ⦄ -- need this!

test₅ = (true ∷ false ∷ []) == (true ∷ false ∷ [])
  where listEqB = listEq ⦃ eqB ⦄ -- need this!
