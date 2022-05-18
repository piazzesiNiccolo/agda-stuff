module plfa.part1.Binary where  

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
import Relation.Binary.PropositionalEquality as Eq 
open Eq using (_≡_; refl; cong; sym)


data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

infixl 20 x0_

infixl 20 x1_
inc : Bin → Bin
inc nil = x1 nil
inc (x0 m) = x1 m
inc (x1 m) = x0 inc m

to : ℕ → Bin
to zero = x0 nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil = 0
from (x0 n) = 2 * from n
from (x1 n) = 1 + 2 * from n