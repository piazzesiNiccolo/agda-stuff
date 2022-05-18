module plfa.part1.Induction where 

import Relation.Binary.PropositionalEquality as Eq 
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import plfa.part1.Binary using (Bin; from; to; inc)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

+-assoc zero n p = refl
+-assoc (suc m) n p =  
    begin 
    (suc m + n) + p 
    ≡⟨⟩
    suc (m + n) + p
    ≡⟨⟩
    suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
    ≡⟨⟩
    suc m + ( n + p) 
    ∎ 

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m 

+-identityʳ zero = refl
+-identityʳ (suc m) = begin 
    suc m + zero 
    ≡⟨⟩
    suc (m + zero)
    ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m 
    ∎

+-suc : ∀ ( m n : ℕ) → m + suc n ≡ suc ( m + n)

+-suc zero n = refl 
+-suc (suc m) n = begin 
    suc m + suc n 
    ≡⟨⟩
    suc (m + suc n)
    ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
    ≡⟨⟩ 
    suc (suc m + n)
    ∎

+-comm : ∀ ( m n : ℕ) → m + n ≡ n + m  

+-comm m zero =
    begin 
    m + zero 
    ≡⟨ +-identityʳ m ⟩
    m
    ≡⟨⟩
    zero + m 
    ∎
+-comm m (suc n) = m + suc n 
    ≡⟨ +-suc m n ⟩ 
    suc ( m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
    suc n + m 
    ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


+-swap : ∀ ( m n p : ℕ) → m + (n + p) ≡ n + ( m + p)

+-swap m n p = begin 
        m + (n + p)
    ≡⟨ sym (+-assoc m n p) ⟩ 
        m + n + p 
    ≡⟨ cong (_+ p) (+-comm m n) ⟩ 
        n + m + p 
    ≡⟨ +-assoc n m p ⟩
        n + (m + p)
    ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q

+-rearrange m n p q = begin 
    (m + n) + (p + q)
    ≡⟨ +-assoc  m n (p + q) ⟩
    m + (n + (p + q))
    ≡⟨ cong ( m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q) 
    ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
    ∎
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p 

*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p  rewrite *-distrib-+  m n p | sym (+-assoc p (m * p) (n * p)) = refl
 
*-assoc : ∀ ( m n p : ℕ) → (m * n) * p ≡ m * (n * p)

*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl


*-identity⁰ : ∀ (m : ℕ) → m * zero ≡ zero

*-identity⁰ zero = refl
*-identity⁰ (suc m) rewrite *-identity⁰ m = refl


*-identity¹ : ∀ (m : ℕ) → m * suc zero ≡ m 

*-identity¹ zero = refl
*-identity¹ (suc m) rewrite *-identity¹ m = refl

*-suc : ∀ ( m n : ℕ) → m * suc n ≡ m + m * n

*-suc zero n = refl
*-suc (suc m) n  rewrite *-suc m n |  +-swap n m (m * n)= refl

*-comm : ∀ ( m n : ℕ) →  m * n ≡ n * m 

*-comm m zero = *-identity⁰ m

*-comm m (suc n) rewrite *-suc m n | *-comm  m n = refl

monus : ∀ (n : ℕ) → zero ∸ n ≡ zero 

monus zero = refl
monus (suc n) rewrite monus n = refl   


∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p rewrite monus p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl


--- Bin ---



inc-suc : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
inc-suc Bin.nil = refl
inc-suc (Bin.x0 x) = refl
inc-suc (Bin.x1 x) rewrite inc-suc x | +-suc (suc (from x)) (from x + 0) = refl

-- to (from x) ≡ x is false:
--  to ( from (x0 x0 nil)) ≡ x0 nil != x0 x0 nil

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n) rewrite inc-suc (to n) | from-to n = refl