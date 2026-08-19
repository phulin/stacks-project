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
abbrev Code (S : Type u) (A₀ : S → A) :=
  Σ n : ℕ, (stages S A₀ n).ι

/-- The ambient object represented by a closure code. -/
abbrev realize (S : Type u) (A₀ : S → A) (i : Code S A₀) : A :=
  (stages S A₀ i.1).obj i.2

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

lemma toCommon_comp_commonHom (S : Type u) (A₀ : S → A)
    {X Y : Code S A₀} (f : realize S A₀ X ⟶ realize S A₀ Y)
    {W : A} (g : W ⟶ realize S A₀ X) (hg : g ≫ f = 0) :
    (g ≫ eqToHom (obj_commonLeft S A₀ X.2).symm) ≫ commonHom S A₀ f = 0 := by
  rcases X with ⟨n, i⟩
  rcases Y with ⟨m, j⟩
  simpa [commonHom, Category.assoc, zero_comp] using
    (reassoc_of% hg) (eqToHom (obj_commonRight S A₀ j).symm)

lemma commonHom_comp_fromCommon (S : Type u) (A₀ : S → A)
    {X Y : Code S A₀} (f : realize S A₀ X ⟶ realize S A₀ Y)
    {W : A} (g : realize S A₀ Y ⟶ W) (hg : f ≫ g = 0) :
    commonHom S A₀ f ≫ (eqToHom (obj_commonRight S A₀ Y.2) ≫ g) = 0 := by
  rcases X with ⟨n, i⟩
  rcases Y with ⟨m, j⟩
  simpa [commonHom, Category.assoc, comp_zero] using
    congrArg (fun q ↦ eqToHom (obj_commonLeft (m := m) S A₀ i) ≫ q) hg

/-- A code for the kernel of an ambient morphism between represented objects. -/
abbrev kernelCode (S : Type u) (A₀ : S → A) :
    {i j : Code S A₀} → (realize S A₀ i ⟶ realize S A₀ j) → Code S A₀
  | ⟨n, i⟩, ⟨m, j⟩, f =>
      ⟨n + m + 1, StepIndex.kernel _ _ (commonHom S A₀ f)⟩

/-- A code for the cokernel of an ambient morphism between represented objects. -/
abbrev cokernelCode (S : Type u) (A₀ : S → A) :
    {i j : Code S A₀} → (realize S A₀ i ⟶ realize S A₀ j) → Code S A₀
  | ⟨n, i⟩, ⟨m, j⟩, f =>
      ⟨n + m + 1, StepIndex.cokernel _ _ (commonHom S A₀ f)⟩

@[simp]
lemma realize_kernelCode (S : Type u) (A₀ : S → A) {i j : Code S A₀}
    (f : realize S A₀ i ⟶ realize S A₀ j) :
    realize S A₀ (kernelCode S A₀ f) = kernel (commonHom S A₀ f) := by
  rcases i with ⟨n, i⟩
  rcases j with ⟨m, j⟩
  rfl

@[simp]
lemma realize_cokernelCode (S : Type u) (A₀ : S → A) {i j : Code S A₀}
    (f : realize S A₀ i ⟶ realize S A₀ j) :
    realize S A₀ (cokernelCode S A₀ f) = cokernel (commonHom S A₀ f) := by
  rcases i with ⟨n, i⟩
  rcases j with ⟨m, j⟩
  rfl

/-- The represented kernel object identified with the ambient kernel. -/
def kernelIso (S : Type u) (A₀ : S → A) {i j : Code S A₀}
    (f : realize S A₀ i ⟶ realize S A₀ j) :
    realize S A₀ (kernelCode S A₀ f) ≅ kernel (commonHom S A₀ f) :=
  eqToIso (realize_kernelCode S A₀ f)

/-- The represented cokernel object identified with the ambient cokernel. -/
def cokernelIso (S : Type u) (A₀ : S → A) {i j : Code S A₀}
    (f : realize S A₀ i ⟶ realize S A₀ j) :
    realize S A₀ (cokernelCode S A₀ f) ≅ cokernel (commonHom S A₀ f) :=
  eqToIso (realize_cokernelCode S A₀ f)

/-- The canonical kernel arrow from a generated kernel to the original source. -/
abbrev kernelArrow (S : Type u) (A₀ : S → A) :
    {i j : Code S A₀} → (f : realize S A₀ i ⟶ realize S A₀ j) →
      realize S A₀ (kernelCode S A₀ f) ⟶ realize S A₀ i
  | ⟨n, i⟩, ⟨m, j⟩, f =>
      (kernelIso S A₀ f).hom ≫ kernel.ι (commonHom S A₀ f) ≫
        eqToHom (obj_commonLeft S A₀ i)

lemma kernelArrow_condition (S : Type u) (A₀ : S → A)
    {i j : Code S A₀} (f : realize S A₀ i ⟶ realize S A₀ j) :
    kernelArrow S A₀ f ≫ f = 0 := by
  rcases i with ⟨n, i⟩
  rcases j with ⟨m, j⟩
  change ((kernelIso S A₀ f).hom ≫ kernel.ι (commonHom S A₀ f) ≫
    eqToHom (obj_commonLeft S A₀ i)) ≫ f = 0
  rw [← cancel_mono (eqToHom (obj_commonRight S A₀ j).symm)]
  have h := congrArg (fun q ↦ (kernelIso S A₀ f).hom ≫ q)
    (kernel.condition (commonHom S A₀ f))
  rw [comp_zero] at h
  simpa only [commonHom, Category.assoc, zero_comp, comp_zero] using h

/-- The canonical cokernel arrow from the original target to a generated cokernel. -/
abbrev cokernelArrow (S : Type u) (A₀ : S → A) :
    {i j : Code S A₀} → (f : realize S A₀ i ⟶ realize S A₀ j) →
      realize S A₀ j ⟶ realize S A₀ (cokernelCode S A₀ f)
  | ⟨n, i⟩, ⟨m, j⟩, f =>
      eqToHom (obj_commonRight S A₀ j).symm ≫ cokernel.π (commonHom S A₀ f) ≫
        (cokernelIso S A₀ f).inv

lemma cokernelArrow_condition (S : Type u) (A₀ : S → A)
    {i j : Code S A₀} (f : realize S A₀ i ⟶ realize S A₀ j) :
    f ≫ cokernelArrow S A₀ f = 0 := by
  rcases i with ⟨n, i⟩
  rcases j with ⟨m, j⟩
  change f ≫ (eqToHom (obj_commonRight S A₀ j).symm ≫
    cokernel.π (commonHom S A₀ f) ≫ (cokernelIso S A₀ f).inv) = 0
  rw [← cancel_epi (eqToHom (obj_commonLeft S A₀ i))]
  have h := congrArg (fun q ↦ q ≫ (cokernelIso S A₀ f).inv)
    (cokernel.condition (commonHom S A₀ f))
  rw [zero_comp] at h
  simpa only [commonHom, Category.assoc, zero_comp, comp_zero] using h

/-- A code for a chosen ambient injective object under a represented object. -/
abbrev injectiveCode (S : Type u) (A₀ : S → A) : Code S A₀ → Code S A₀
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

/-- The selected kernel fork of a morphism in the closure. -/
abbrev closureKernelFork {X Y : Closure S A₀} (f : X ⟶ Y) : KernelFork f :=
  KernelFork.ofι (InducedCategory.homMk (kernelArrow S A₀ f.hom)) (by
    apply InducedCategory.hom_ext
    exact kernelArrow_condition S A₀ f.hom)

/-- The selected kernel fork is limiting. -/
def closureKernelForkIsLimit {X Y : Closure S A₀} (f : X ⟶ Y) :
    IsLimit (closureKernelFork S A₀ f) := by
  rcases X with ⟨n, i⟩
  rcases Y with ⟨m, j⟩
  have sourceCondition (s : KernelFork f) : s.ι.hom ≫ f.hom = 0 := by
    have hs : (inclusion S A₀).map (s.ι ≫ f) =
        (inclusion S A₀).map 0 :=
      congrArg (fun q ↦ (inclusion S A₀).map q) s.condition
    rw [Functor.map_comp, Functor.map_zero] at hs
    change s.ι.hom ≫ f.hom = 0 at hs
    exact hs
  let liftObj (s : KernelFork f) :
      realize S A₀ s.pt ⟶ realize S A₀ (kernelCode S A₀ f.hom) :=
    kernel.lift (commonHom S A₀ f.hom)
      (s.ι.hom ≫ eqToHom (obj_commonLeft S A₀ i).symm)
      (toCommon_comp_commonHom S A₀ f.hom s.ι.hom (sourceCondition s)) ≫
        (kernelIso S A₀ f.hom).inv
  have liftFac (s : KernelFork f) : liftObj s ≫ kernelArrow S A₀ f.hom = s.ι.hom := by
    dsimp [liftObj, kernelArrow]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hl := kernel.lift_ι (commonHom S A₀ f.hom)
      ((Fork.ι s).hom ≫ eqToHom (obj_commonLeft S A₀ i).symm)
      (toCommon_comp_commonHom S A₀ f.hom (Fork.ι s).hom (sourceCondition s))
    rw [← Category.assoc, hl]
    simp
  refine isLimitAux _ (fun s ↦ InducedCategory.homMk (liftObj s)) (fun s ↦ ?_)
      (fun s m hm ↦ ?_)
  · apply InducedCategory.hom_ext
    exact liftFac s
  ·
    apply InducedCategory.hom_ext
    rw [← cancel_mono (kernelIso S A₀ f.hom).hom]
    apply Fork.IsLimit.hom_ext (kernelIsKernel (commonHom S A₀ f.hom))
    have hm' : m.hom ≫ kernelArrow S A₀ f.hom = s.ι.hom := by
      have h := congrArg (fun q ↦ (inclusion S A₀).map q) hm
      change m.hom ≫ kernelArrow S A₀ f.hom = s.ι.hom at h
      exact h
    rw [← cancel_mono (eqToHom (obj_commonLeft S A₀ i))]
    simpa [kernelArrow, liftObj, Category.assoc]
      using hm'.trans (liftFac s).symm

instance closureHasKernel {X Y : Closure S A₀} (f : X ⟶ Y) : HasKernel f :=
  ⟨closureKernelFork S A₀ f, closureKernelForkIsLimit S A₀ f⟩

instance closureHasKernels : HasKernels (Closure S A₀) :=
  ⟨fun f ↦ closureHasKernel S A₀ f⟩

/-- The selected cokernel cofork of a morphism in the closure. -/
abbrev closureCokernelCofork {X Y : Closure S A₀} (f : X ⟶ Y) : CokernelCofork f :=
  CokernelCofork.ofπ (InducedCategory.homMk (cokernelArrow S A₀ f.hom)) (by
    apply InducedCategory.hom_ext
    exact cokernelArrow_condition S A₀ f.hom)

/-- The selected cokernel cofork is colimiting. -/
def closureCokernelCoforkIsColimit {X Y : Closure S A₀} (f : X ⟶ Y) :
    IsColimit (closureCokernelCofork S A₀ f) := by
  rcases X with ⟨n, i⟩
  rcases Y with ⟨m, j⟩
  have targetCondition (s : CokernelCofork f) : f.hom ≫ s.π.hom = 0 := by
    have hs : (inclusion S A₀).map (f ≫ s.π) =
        (inclusion S A₀).map 0 :=
      congrArg (fun q ↦ (inclusion S A₀).map q) s.condition
    rw [Functor.map_comp, Functor.map_zero] at hs
    change f.hom ≫ s.π.hom = 0 at hs
    exact hs
  let descObj (s : CokernelCofork f) :
      realize S A₀ (cokernelCode S A₀ f.hom) ⟶ realize S A₀ s.pt :=
    (cokernelIso S A₀ f.hom).hom ≫ cokernel.desc (commonHom S A₀ f.hom)
      (eqToHom (obj_commonRight S A₀ j) ≫ s.π.hom)
      (commonHom_comp_fromCommon S A₀ f.hom s.π.hom (targetCondition s))
  have descFac (s : CokernelCofork f) :
      cokernelArrow S A₀ f.hom ≫ descObj s = s.π.hom := by
    dsimp [descObj, cokernelArrow]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hd := cokernel.π_desc (commonHom S A₀ f.hom)
      (eqToHom (obj_commonRight S A₀ j) ≫ (Cofork.π s).hom)
      (commonHom_comp_fromCommon S A₀ f.hom (Cofork.π s).hom (targetCondition s))
    rw [hd]
    simp
  refine isColimitAux _ (fun s ↦ InducedCategory.homMk (descObj s)) (fun s ↦ ?_)
      (fun s m hm ↦ ?_)
  · apply InducedCategory.hom_ext
    exact descFac s
  ·
    apply InducedCategory.hom_ext
    rw [← cancel_epi (cokernelIso S A₀ f.hom).inv]
    apply Cofork.IsColimit.hom_ext (cokernelIsCokernel (commonHom S A₀ f.hom))
    have hm' : cokernelArrow S A₀ f.hom ≫ m.hom = s.π.hom := by
      have h := congrArg (fun q ↦ (inclusion S A₀).map q) hm
      change cokernelArrow S A₀ f.hom ≫ m.hom = s.π.hom at h
      exact h
    rw [← cancel_epi (eqToHom (obj_commonRight S A₀ j).symm)]
    simpa [cokernelArrow, descObj, Category.assoc]
      using hm'.trans (descFac s).symm

instance closureHasCokernel {X Y : Closure S A₀} (f : X ⟶ Y) : HasCokernel f :=
  ⟨closureCokernelCofork S A₀ f, closureCokernelCoforkIsColimit S A₀ f⟩

instance closureHasCokernels : HasCokernels (Closure S A₀) :=
  ⟨fun f ↦ closureHasCokernel S A₀ f⟩

end CategoryStructure

end Formalization.CategoryTheory.SmallAbelianClosure
