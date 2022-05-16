module plfa.part1.Naturals where

import Relation.Binary.PropositionalEquality as Eq 

open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_ ; _∎)

data ℕ : Set where 
  zero : ℕ
  suc  : ℕ -> ℕ 

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ

zero + n = n 
(suc m) + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ

0 * n = 0
1 * n = 1
(suc m) * n = m + (m * n)

_∸_ : ℕ → ℕ → ℕ

m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ = 
  begin 
    3 ∸ 2 
  ≡⟨⟩
    (2 ∸ 1)
  ≡⟨⟩
    (1 ∸ 0)
  ≡⟨⟩ 
    1
  ∎
_ : 2 + 3 ≡ 5

_ = 
    begin 
    2 + 3
    ≡⟨⟩
    suc (1 + 3)
    ≡⟨⟩
    suc (suc (0 + 3))   
    ≡⟨⟩
    suc (suc 3)
    ≡⟨⟩
    5
  
    ∎


_ = 
    begin 
    5 ∸ 3 
  ≡⟨⟩
    4 ∸  2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0 
  ≡⟨⟩
    2 
  ∎ 

_ : 2 ∸ 3 ≡ 0 

_ = refl
_ = 
  begin 
  3 ∸ 5 
  ≡⟨⟩ 
  2 ∸ 4 
  ≡⟨⟩
  1 ∸ 3 
  ≡⟨⟩ 
  0 ∸ 2 
  ≡⟨⟩ 
  0 
  ∎

data Bin : Set where 
  ⟨⟩ : Bin 
  _O : Bin → Bin 
  _I : Bin → Bin 

inc : Bin → Bin 

inc ⟨⟩ = ⟨⟩ I
inc (b O) =  b I
inc (b I) =  (inc b) O


_ : inc ⟨⟩ ≡ ⟨⟩ I 

_ = refl


_ : inc (⟨⟩ I) ≡ ⟨⟩ I O 

_ = refl


_ : inc (⟨⟩ I O ) ≡ ⟨⟩ I I 

_ = refl



_ : inc (⟨⟩ I I ) ≡ ⟨⟩ I O O  

_ = refl


_ : inc (⟨⟩ I O O  ) ≡ ⟨⟩ I O I 

_ = refl


to : ℕ → Bin 

to zero = ⟨⟩
to (suc n) = inc (to n)

from : Bin → ℕ 

from ⟨⟩ = 0
from (b O) = 2 * (from b)
from (b I) = suc (2 * (from b))

