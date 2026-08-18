import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Small abelian subcategories closed under injective presentations

This file supplies the omitted set-theoretic construction used in Sets,
Lemma `abelian-injectives`.  Starting from a small family of objects in a
large abelian category, we repeatedly adjoin zero, binary products, kernels,
cokernels, and chosen injective presentations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace Formalization.CategoryTheory.SmallAbelianClosure

variable {A : Type (u + 1)} [LargeCategory A] [Abelian A] [EnoughInjectives A]

/-- A family of objects indexed in the small universe. -/
structure Family where
  ι : Type u
  obj : ι → A

/-- The operations adjoined in one closure step. -/
inductive StepIndex (F : Family (A := A)) : Type u
  | old (i : F.ι)
  | zero
  | product (i j : F.ι)
  | kernel (i j : F.ι) (f : F.obj i ⟶ F.obj j)
  | cokernel (i j : F.ι) (f : F.obj i ⟶ F.obj j)
  | injective (i : F.ι)

/-- Interpret one step of formal closure inside the ambient category. -/
def step (F : Family (A := A)) : Family (A := A) where
  ι := StepIndex F
  obj
    | .old i => F.obj i
    | .zero => 0
    | .product i j => F.obj i ⨯ F.obj j
    | .kernel _ _ f => kernel f
    | .cokernel _ _ f => cokernel f
    | .injective i => Injective.under (F.obj i)

/-- The inclusion of a family into its next closure step. -/
def toStep (F : Family (A := A)) : F.ι → (step F).ι := StepIndex.old

@[simp]
lemma step_obj_toStep (F : Family (A := A)) (i : F.ι) :
    (step F).obj (toStep F i) = F.obj i := rfl

/-- The family after `n` closure steps. -/
def stages (S : Type u) (A₀ : S → A) : ℕ → Family (A := A)
  | 0 => ⟨S, A₀⟩
  | n + 1 => step (stages S A₀ n)

/-- Move an index forward by a specified number of closure steps. -/
def liftIndex (S : Type u) (A₀ : S → A) (n : ℕ) :
    ∀ k : ℕ, (stages S A₀ n).ι → (stages S A₀ (n + k)).ι
  | 0, i => i
  | k + 1, i => toStep _ (liftIndex S A₀ n k i)

@[simp]
lemma obj_liftIndex (S : Type u) (A₀ : S → A) (n k : ℕ)
    (i : (stages S A₀ n).ι) :
    (stages S A₀ (n + k)).obj (liftIndex S A₀ n k i) =
      (stages S A₀ n).obj i := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- All object codes appearing at a finite stage of the construction. -/
def Code (S : Type u) (A₀ : S → A) :=
  Σ n : ℕ, (stages S A₀ n).ι

/-- The ambient object represented by a closure code. -/
def realize (S : Type u) (A₀ : S → A) : Code S A₀ → A
  | ⟨n, i⟩ => (stages S A₀ n).obj i

/-- Regard a code from stage `n` as a code from stage `n + k`. -/
def liftCode (S : Type u) (A₀ : S → A) {n : ℕ}
    (i : (stages S A₀ n).ι) (k : ℕ) : Code S A₀ :=
  ⟨n + k, liftIndex S A₀ n k i⟩

@[simp]
lemma realize_liftCode (S : Type u) (A₀ : S → A) {n : ℕ}
    (i : (stages S A₀ n).ι) (k : ℕ) :
    realize S A₀ (liftCode S A₀ i k) = (stages S A₀ n).obj i :=
  obj_liftIndex S A₀ n k i

/-- Transport a stage index along an equality of stage numbers. -/
def castIndex (S : Type u) (A₀ : S → A) {n m : ℕ} (h : n = m) :
    (stages S A₀ n).ι → (stages S A₀ m).ι := by
  subst h
  exact id

@[simp]
lemma obj_castIndex (S : Type u) (A₀ : S → A) {n m : ℕ} (h : n = m)
    (i : (stages S A₀ n).ι) :
    (stages S A₀ m).obj (castIndex S A₀ h i) = (stages S A₀ n).obj i := by
  subst h
  rfl

/-- Move two stage indices to the common stage `n + m`. -/
def commonLeft (S : Type u) (A₀ : S → A) {n m : ℕ}
    (i : (stages S A₀ n).ι) : (stages S A₀ (n + m)).ι :=
  liftIndex S A₀ n m i

/-- Move the right input to the common stage `n + m`. -/
def commonRight (S : Type u) (A₀ : S → A) {n m : ℕ}
    (j : (stages S A₀ m).ι) : (stages S A₀ (n + m)).ι :=
  castIndex S A₀ (Nat.add_comm m n) (liftIndex S A₀ m n j)

@[simp]
lemma obj_commonLeft (S : Type u) (A₀ : S → A) {n m : ℕ}
    (i : (stages S A₀ n).ι) :
    (stages S A₀ (n + m)).obj (commonLeft S A₀ i) =
      (stages S A₀ n).obj i :=
  obj_liftIndex S A₀ n m i

@[simp]
lemma obj_commonRight (S : Type u) (A₀ : S → A) {n m : ℕ}
    (j : (stages S A₀ m).ι) :
    (stages S A₀ (n + m)).obj (commonRight S A₀ j) =
      (stages S A₀ m).obj j := by
  simp [commonRight]

/-- A zero-object code. -/
def zeroCode (S : Type u) (A₀ : S → A) : Code S A₀ :=
  ⟨1, StepIndex.zero⟩

@[simp]
lemma realize_zeroCode (S : Type u) (A₀ : S → A) :
    realize S A₀ (zeroCode S A₀) = 0 := rfl

/-- A code for the product of two represented objects. -/
def productCode (S : Type u) (A₀ : S → A) : Code S A₀ → Code S A₀ → Code S A₀
  | ⟨n, i⟩, ⟨m, j⟩ =>
      ⟨n + m + 1, StepIndex.product (commonLeft S A₀ i) (commonRight S A₀ j)⟩

@[simp]
lemma realize_productCode (S : Type u) (A₀ : S → A) (i j : Code S A₀) :
    realize S A₀ (productCode S A₀ i j) =
      (realize S A₀ i ⨯ realize S A₀ j) := by
  rcases i with ⟨n, i⟩
  rcases j with ⟨m, j⟩
  simp [productCode, realize, stages, step]

/-- The two endpoints, promoted to a common stage. -/
def commonHom (S : Type u) (A₀ : S → A) {n m : ℕ}
    {i : (stages S A₀ n).ι} {j : (stages S A₀ m).ι}
    (f : (stages S A₀ n).obj i ⟶ (stages S A₀ m).obj j) :
    (stages S A₀ (n + m)).obj (commonLeft S A₀ i) ⟶
      (stages S A₀ (n + m)).obj (commonRight S A₀ j) :=
  eqToHom (obj_commonLeft S A₀ i) ≫ f ≫ eqToHom (obj_commonRight S A₀ j).symm

/-- A code for the kernel of an ambient morphism between represented objects. -/
def kernelCode (S : Type u) (A₀ : S → A) :
    {i j : Code S A₀} → (realize S A₀ i ⟶ realize S A₀ j) → Code S A₀
  | ⟨n, i⟩, ⟨m, j⟩, f =>
      ⟨n + m + 1, StepIndex.kernel _ _ (commonHom S A₀ f)⟩

/-- A code for the cokernel of an ambient morphism between represented objects. -/
def cokernelCode (S : Type u) (A₀ : S → A) :
    {i j : Code S A₀} → (realize S A₀ i ⟶ realize S A₀ j) → Code S A₀
  | ⟨n, i⟩, ⟨m, j⟩, f =>
      ⟨n + m + 1, StepIndex.cokernel _ _ (commonHom S A₀ f)⟩

/-- A code for a chosen ambient injective object under a represented object. -/
def injectiveCode (S : Type u) (A₀ : S → A) : Code S A₀ → Code S A₀
  | ⟨n, i⟩ => ⟨n + 1, StepIndex.injective i⟩

@[simp]
lemma realize_injectiveCode (S : Type u) (A₀ : S → A) (i : Code S A₀) :
    realize S A₀ (injectiveCode S A₀ i) = Injective.under (realize S A₀ i) := by
  rcases i with ⟨n, i⟩
  rfl

/-- The small induced category on all generated object codes. -/
abbrev Closure (S : Type u) (A₀ : S → A) :=
  InducedCategory A (realize S A₀)

/-- The fully faithful inclusion of the generated category. -/
abbrev inclusion (S : Type u) (A₀ : S → A) : Closure S A₀ ⥤ A :=
  inducedFunctor (realize S A₀)

/-- The original family embeds at stage zero. -/
def baseCode (S : Type u) (A₀ : S → A) (s : S) : Closure S A₀ := ⟨0, s⟩

@[simp]
lemma inclusion_baseCode (S : Type u) (A₀ : S → A) (s : S) :
    (inclusion S A₀).obj (baseCode S A₀ s) = A₀ s := rfl

section CategoryStructure

variable (S : Type u) (A₀ : S → A)

instance closureHasZeroObject : HasZeroObject (Closure S A₀) := by
  let Z : Closure S A₀ := zeroCode S A₀
  have hZ : IsZero ((inclusion S A₀).obj Z) := by
    change IsZero (realize S A₀ (zeroCode S A₀))
    rw [realize_zeroCode]
    exact isZero_zero A
  exact ⟨Z, IsZero.of_full_of_faithful_of_isZero (inclusion S A₀) Z hZ⟩

/-- The selected binary-product cone. -/
def productFan (X Y : Closure S A₀) : BinaryFan X Y :=
  BinaryFan.mk
    (InducedCategory.homMk
      (eqToHom (realize_productCode S A₀ X Y) ≫ Limits.prod.fst))
    (InducedCategory.homMk
      (eqToHom (realize_productCode S A₀ X Y) ≫ Limits.prod.snd))

/-- The selected binary-product cone is limiting. -/
def productFanIsLimit (X Y : Closure S A₀) : IsLimit (productFan S A₀ X Y) := by
  apply isLimitOfReflects (inclusion S A₀)
  let b : BinaryFan ((inclusion S A₀).obj X) ((inclusion S A₀).obj Y) := BinaryFan.mk
    (eqToHom (realize_productCode S A₀ X Y) ≫ Limits.prod.fst)
    (eqToHom (realize_productCode S A₀ X Y) ≫ Limits.prod.snd)
  have hb : IsLimit b := BinaryFan.IsLimit.mk _
    (fun f g ↦ Limits.prod.lift f g ≫ eqToHom (realize_productCode S A₀ X Y).symm)
    (by intros; simpa [b] using Limits.prod.lift_fst _ _) (by
      intros; simpa [b] using Limits.prod.lift_snd _ _) (by
      intro T f g m hm₁ hm₂
      rw [← cancel_mono (eqToHom (realize_productCode S A₀ X Y))]
      apply Limits.prod.hom_ext
      · calc
          _ = f := by simpa [b, Category.assoc] using hm₁
          _ = _ := (Limits.prod.lift_fst f g).symm
          _ = _ := by simp
      · calc
          _ = g := by simpa [b, Category.assoc] using hm₂
          _ = _ := (Limits.prod.lift_snd f g).symm
          _ = _ := by simp)
  let b' := (Cone.postcompose (pairComp X Y (inclusion S A₀)).inv).obj b
  have hb' : IsLimit b' :=
    (IsLimit.postcomposeInvEquiv (pairComp X Y (inclusion S A₀)) b).invFun hb
  apply IsLimit.ofIsoLimit hb'
  exact Cone.ext (Iso.refl _) (by
    rintro ⟨j⟩
    rcases j with _ | _
    · dsimp [b', b, pairComp, diagramIsoPair, mapPairIso, NatIso.ofComponents,
        productFan, inclusion, inducedFunctor]
      simp only [Category.comp_id, Category.id_comp]
      change (eqToHom (realize_productCode S A₀ X Y) ≫ Limits.prod.fst) =
        (InducedCategory.homMk
          (eqToHom (realize_productCode S A₀ X Y) ≫ Limits.prod.fst)).hom
      rfl
    · dsimp [b', b, pairComp, diagramIsoPair, mapPairIso, NatIso.ofComponents,
        productFan, inclusion, inducedFunctor]
      simp only [Category.comp_id, Category.id_comp]
      change (eqToHom (realize_productCode S A₀ X Y) ≫ Limits.prod.snd) =
        (InducedCategory.homMk
          (eqToHom (realize_productCode S A₀ X Y) ≫ Limits.prod.snd)).hom
      rfl)

instance closureHasLimitPair (X Y : Closure S A₀) : HasLimit (pair X Y) :=
  ⟨productFan S A₀ X Y, productFanIsLimit S A₀ X Y⟩

instance closureHasBinaryProducts : HasBinaryProducts (Closure S A₀) :=
  hasBinaryProducts_of_hasLimit_pair (C := Closure S A₀)

instance closureHasFiniteProducts : HasFiniteProducts (Closure S A₀) :=
  hasFiniteProducts_of_has_binary_and_terminal

end CategoryStructure

end Formalization.CategoryTheory.SmallAbelianClosure
