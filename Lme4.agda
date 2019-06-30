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


data Row {l} : ∀ (n : ℕ) → Vec (String × Set l) n -> Set (Level.suc l) where
  []  : Row 0 []
  _∷_ : ∀ {n : ℕ} {T : Set l} {TS} → (p : String × T) → Row n TS → Row (ℕ.suc n) (((proj₁ p) , T) ∷ TS)

rowBind : ∀ {l n m a b} -> Row {l} n a -> Row {l} m b -> Row {l} (n + m) (a Data.Vec.++ b)
rowBind [] rs = rs
rowBind (x ∷ xs) rs = x ∷ rowBind xs rs

DataFrame : ∀ {l} {m : ℕ} (n : ℕ) -> Vec (String × Set l) m -> Set (Level.suc l)
DataFrame {l} {m} n TS = Vec (Row m TS) n

the : ∀ (t : Set) -> t -> t
the t x = x

test : Row _ _
test = ("hi" , the (Vec _ _) (1 ∷ [])) ∷ ("there" , 2) ∷ []

testFrame : DataFrame _ _
testFrame = test ∷ test ∷ []

data CodedRow : ∀ (n : ℕ) → Vec (String × ℕ) n -> Set where
 [] : CodedRow 0 []
 _∷_ : ∀ {n : ℕ} {len} {NS} → (p : String × (Vec Float len)) → CodedRow n NS → CodedRow (ℕ.suc n) (((proj₁ p) , len) ∷ NS)

data FactorCoding {l} : (n : ℕ) → Vec (String × Set l × ℕ) n -> Set (Level.suc l) where
 [] : FactorCoding 0 []
 _∷_ : ∀ {n} {p} {FCS} {A : Set l} ->
       (i : (String × (A -> Vec Float p))) -> FactorCoding n FCS -> FactorCoding (ℕ.suc n) (((proj₁ i) , A , p) ∷ FCS)

projectRow : ∀ {l} {n} {ts} -> FactorCoding {l} n ts -> Set (Level.suc l)
projectRow {_} {n} {ts} rs = Row n (Data.Vec.map (\ { (s , T , _)  -> (s , T) } ) ts)

projectCodedRow : ∀ {l} {n} {ts} -> FactorCoding {l} n ts -> Set
projectCodedRow {_} {n} {ts} rs = CodedRow n (Data.Vec.map (\ { (s , _ , p)  -> (s , p) } ) ts)

codeFactor : ∀ {l n CS} -> (FC : FactorCoding {l} n CS) -> projectRow FC -> projectCodedRow FC
codeFactor [] [] = []
codeFactor ((s , f) ∷ cs) ((_ , fac) ∷ facs) = (s , (f fac)) ∷ codeFactor cs facs


