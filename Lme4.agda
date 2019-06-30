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

Values : ∀ {l} {n} → Set (lsuc l)
Values {l} {n} = Vec (∃ λ (A : Set l) → A) n

Coding : ∀ {l} {n} → Set (lsuc l)
Coding {l} {n} = Vec (String × ∃ λ (m : ℕ) → ∃ λ (A : Set l) → A → Vec Float m) n

projectSchema : ∀ {l} {n} → Row {l} {n} → Schema {l} {n}
projectSchema row = map (λ x → proj₁ x , (proj₁ ∘ proj₂) x) row

RowTransformer : ∀ {l} {r} {n} → Set (lsuc (l ⊔ r))
RowTransformer {l} {r} {n} = Vec (String × ∃ λ (A : Set l) → (∃ λ (B : Set r) → A → B)) n

compat? : ∀ {n} {l} {r} → Row {l} {n} → RowTransformer {l} {r} {n} → Set (lsuc l)
compat? {l = l} [] [] = Lift (lsuc l) ⊤
compat? (x ∷ row) (y ∷ rowt) = (proj₁ x , (proj₁ ∘ proj₂) x) ≡ (proj₁ y , (proj₁ ∘ proj₂) y) × compat? row rowt

transformRow : ∀ {l} {r} {n} {row : Row {l} {n} } {rowt : RowTransformer {l} {r} {n} } → compat? row rowt → Row {r} {n}
transformRow {row = []} {[]} compatRowRowt = []
transformRow {row = (lab , A , v) ∷ row} {(labt , A' , B , f ) ∷ rowt} compatRowRowt with proj₁ compatRowRowt
... | _≡_.refl = (lab , B , f v) ∷ (transformRow {row = row} {rowt = rowt} (proj₂ compatRowRowt))

_⊆_ : ∀ {l} {n} {m} {A} (XS : Vec A m) (YS : Vec A n) → Set l
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

⊆-nested : ∀ {l} {n} {m} {A} {a : A} {as : Vec {l} A n} {bs : Vec A m} → (a ∷ as) ⊆ bs → as ⊆ bs
⊆-nested {a = a} prf e = prf (∈-++⁺ʳ (a ∷ []) e)

schemaLookup : ∀ {l} {n} {src : Row {l} {n}} → (i : Fin n) → (λ x → proj₁ x , (proj₁ ∘ proj₂) x) (lookup src i) ≡ lookup (projectSchema src) i
schemaLookup {src = src} i with (λ x → proj₁ x , (proj₁ ∘ proj₂) x) (lookup src i) | lookup (projectSchema src) i | lookup-map i (λ x → proj₁ x , (proj₁ ∘ proj₂) x) src
schemaLookup {src = src} i | q | .q | refl = refl

rowCast-schema : ∀ {l} {n} {m} {tgt : Row {l} {n}} →
  (src : Row {l} {m}) →
  (projectSchema tgt) ⊆ (projectSchema src) →
  Σ (Row {l} {n}) (λ row → projectSchema row ≡ projectSchema tgt)
rowCast-schema {tgt = []} xs prf = [] , refl
rowCast-schema {l} {tgt = t ∷ tgt} src prf with here refl
... | p with prf p
...   | q with lookup-index q | lookup src (index q) | schemaLookup {src = src} (index q) |  rowCast-schema src (⊆-nested prf)
...      | lui≡ | lu | slu≡ | prow , pprf with trans lui≡ (sym slu≡)
...         | refl = lu ∷ prow , (≋⇒≡ (refl ∷ ≡⇒≋ pprf))
  
rowCast : ∀ {l} {n} {m} {tgt : Row {l} {n}} →
  (src : Row {l} {m}) →
  (projectSchema tgt) ⊆ (projectSchema src) →
  Row {l} {n}
rowCast src prf = proj₁ (rowCast-schema src prf)

data Intercept : Set where
  Unset : Intercept
  No    : Intercept
  Yes   : Intercept

_∧ᵢ_ : Intercept -> Intercept -> Intercept
Unset ∧ᵢ y = y
No ∧ᵢ Unset = No
No ∧ᵢ No = No
No ∧ᵢ Yes = Yes
Yes ∧ᵢ y = Yes

data Modelable : Set -> Set where
  FloatT : Modelable Float
  FactT  : Modelable String

data Term : ∀ {n : ℕ} {empty : Bool} {intercept : Intercept} ->  (vars : Vec (String × Set) n) -> Set₁ where
  Var   : ∀ {MT : Set} -> (p : String × Modelable MT) -> Term {_} {false} {Unset} ((proj₁ p , MT)  ∷ [])
  Plus  : ∀ {b1 b2 i1 i2 n m VA VB} -> Term {n} {b1} {i1} VA -> Term {m} {b2} {i2} VB -> Term {_} {b1 ∧ b2} {i1 ∧ᵢ i2} (VA ++ VB)
  Mul   : ∀ {b1 b2 i1 i2 n m VA VB} -> Term {n} {b1} {i1} VA -> Term {m} {b2} {i2} VB -> Term {_} {b1 ∧ b2} {i1 ∧ᵢ i2} (VA ++ VB)
  Colon : ∀ {b1 b2 i1 i2 n m VA VB} -> Term {n} {b1} {i1} VA -> Term {m} {b2} {i2} VB -> Term {_} {b1 ∧ b2} {i1 ∧ᵢ i2} (VA ++ VB)
  Div   : ∀ {b1 b2 i1 i2 n m VA VB} -> Term {n} {b1} {i1} VA -> Term {m} {b2} {i2} VB -> Term {_} {b1 ∧ b2} {i1 ∧ᵢ i2} (VA ++ VB)
  +0    : Term {_} {true} {No} []
  +1    : Term {_} {false} {Yes} []

data BarTerm : ∀ {n : ℕ} {intercept : Intercept} ->  (vars : Vec (String × Set) n) -> Set₁ where
  Bar : ∀ {n VA i} -> Term {n} {false} {i} VA -> (V : (String × Modelable String)) -> BarTerm {ℕ.suc n} {i} ((proj₁ V , String) ∷ VA)

either : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}  -> (A -> C) -> (B -> C) -> A ⊎ B -> C
either f _ (inj₁ x) = f x
either _ g (inj₂ x) = g x

isEmpty : ∀ {b m nv i} -> Term {m} {b} {i} nv ⊎ BarTerm {m} {i} nv -> Bool
isEmpty {b} {m} {nv} = either (λ _ -> b) (λ _ -> false)

joinIntercepts : ∀ {i n b nv} -> Intercept ->  Term {n} {b} {i} nv ⊎ BarTerm {n} {i} nv -> Intercept
joinIntercepts {i} li (inj₁ _) = li ∧ᵢ i
joinIntercepts li _ = li

data Model : ∀ {n : ℕ} {empty : Bool} {intercept : Intercept} ->  (Vec (String × Set) n) -> Set₁ where
  Var   : ∀ {MT : Set} -> (p : String × Modelable MT) -> Model {_} {false} {Unset} ((proj₁ p , MT)  ∷ [])
  Add   : ∀ {b1 b2 i1 i2 n m ov nv} -> Model {n} {b1} {i1} ov -> (T : Term {m} {b2} {i2} nv ⊎ BarTerm {m} {i2} nv) -> Model {n + m} {b1 ∧ isEmpty T} {joinIntercepts i1 T} (ov ++ nv)
  Plus  : ∀ {b1 b2 i1 i2 n m ov nv} -> Model {n} {b1} {i1} ov -> (T : Term {m} {b2} {i2} nv ⊎ BarTerm {m} {i2} nv) -> Model {n + m} {b1 ∧ isEmpty T} {joinIntercepts i1 T} (ov ++ nv)
  Mul   : ∀ {b1 b2 i1 i2 n m ov nv} -> Model {n} {b1} {i1} ov -> (T : Term {m} {b2} {i2} nv ⊎ BarTerm {m} {i2} nv) -> Model {n + m} {b1 ∧ isEmpty T} {joinIntercepts i1 T} (ov ++ nv)
  Colon : ∀ {b1 b2 i1 i2 n m ov nv} -> Model {n} {b1} {i1} ov -> (T : Term {m} {b2} {i2} nv ⊎ BarTerm {m} {i2} nv) -> Model {n + m} {b1 ∧ isEmpty T} {joinIntercepts i1 T} (ov ++ nv)
  Div   : ∀ {b1 b2 i1 i2 n m ov nv} -> Model {n} {b1} {i1} ov -> (T : Term {m} {b2} {i2} nv ⊎ BarTerm {m} {i2} nv) -> Model {n + m} {b1 ∧ isEmpty T} {joinIntercepts i1 T} (ov ++ nv)
  +0    : Model {_} {true} {No} []
  +1    : Model {_} {false} {Yes} []

data lFormula : ∀ {n : ℕ} ->  (vars : Vec (String × Set) n) -> Set₁ where
  Tilde : ∀ {b1 b2 i1 i2 n m lv rv} -> Term {n} {b1} {i1} lv -> Model {m} {b2} {i2} rv -> lFormula (lv ++ rv)

-- generateModelMatrix : ∀ {n m x} ->
--   {coding : Vec (String × Set × ℕ) m} ->
--   lFormula {m} (Data.Vec.map (λ{ (s , T , _) -> (s , T)}) coding) ->
--   DataFrame n x ->
--   FactorCoding m coding ->
--   Vec (Vec Float (sum (Data.Vec.map (λ { (_ , _ , c) -> c }) coding))) n
-- generateModelMatrix = {!!}

-- generateModelMatrix :
--   ∀ {m n codes vars} ->
--   {vars ≡ Data.Vec.map (λ a b _ -> (a , b)) codes} ->
--   {vars ⊆ things} ->
--   {somenumber ≡ Data.Vec.foldr (+) (Data.Vec.map (λ _ _ p -> p) codes)} ->
--   lFormula vars -> FactorCoding m codes -> DataFrame n things -> Vec (Vec Float somenumber) n 
-- generateModelMatrix = ?
