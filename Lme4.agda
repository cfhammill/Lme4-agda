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


