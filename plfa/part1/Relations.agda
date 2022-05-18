module plfa.part1.Relations where 

import Relation.Binary.PropositionalEquality as Eq 
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

data _≤_ : ℕ → ℕ → Set where 
  z≤n : ∀ {n : ℕ}
       -------------
       → zero ≤ n 
   
  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

infix 4 _≤_