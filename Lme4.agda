module Lme4 where

open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Data.String hiding (_++_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Fin using (Fin; lower₁)
open import Level renaming (suc to lsuc)
open import Data.Bool
open import Data.Vec.Properties
open import Data.Vec.Relation.Unary.Any using (index ; here ; there ; satisfied)
open import Data.Vec.Relation.Unary.Any.Properties
open import Data.Vec.Relation.Binary.Equality.Propositional
open import Data.Vec.Membership.Propositional
open import Data.Vec.Membership.Propositional.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Nullary
open import Relation.Nullary.Product using (_×-dec_)
open import Function using (_∋_; typeOf; _∘_)
open import Data.Empty
open import Data.Unit
open import Data.Float

Schema : ∀ {l} {n} → Set (lsuc l)
Schema {l} {n} = Vec (String × Set l) n

Row : ∀ {l} {n} → Set (lsuc l)
Row {l} {n} = Vec (String × ∃ λ (A : Set l) → A) n

rowBind : ∀ {l n m a b} -> Row {l} n a -> Row {l} m b -> Row {l} (n + m) (a Data.Vec.++ b)
rowBind [] rs = rs
rowBind (x ∷ xs) rs = x ∷ rowBind xs rs
Values : ∀ {l} {n} → Set (lsuc l)
Values {l} {n} = Vec (∃ λ (A : Set l) → A) n

DataFrame : ∀ {l} {m : ℕ} (n : ℕ) -> Vec (String × Set l) m -> Set (Level.suc l)
DataFrame {l} {m} n TS = Vec (Row m TS) n
Coding : ∀ {l} {n} → Set (lsuc l)
Coding {l} {n} = Vec (String × ∃ λ (m : ℕ) → ∃ λ (A : Set l) → A → Vec Float m) n

the : ∀ (t : Set) -> t -> t
the t x = x
projectSchema : ∀ {l} {n} → Row {l} {n} → Schema {l} {n}
projectSchema row = map (λ x → proj₁ x , (proj₁ ∘ proj₂) x) row

test : Row _ _
test = ("hi" , the (Vec _ _) (1 ∷ [])) ∷ ("there" , 2) ∷ []
RowTransformer : ∀ {l} {r} {n} → Set (lsuc (l ⊔ r))
RowTransformer {l} {r} {n} = Vec (String × ∃ λ (A : Set l) → (∃ λ (B : Set r) → A → B)) n

testFrame : DataFrame _ _
testFrame = test ∷ test ∷ []







