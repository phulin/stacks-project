import Formalization.Books.Algebra.Unit56
import Formalization.Books.Algebra.Unit87
import Formalization.Books.Algebra.Unit96
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 98: Taking limits of modules

The inverse systems in the source are indexed by the positive natural numbers.
The declarations below use the inverse-system and graded-module interfaces from
Chapters 56 and 87, and the canonical adic completion from Chapter 96.
-/

namespace Formalization.Books.Algebra.Unit98

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21
open Formalization.Books.Algebra.Unit56
open Formalization.Books.Algebra.Unit87
open Formalization.Books.Algebra.Unit96
open scoped TensorProduct

universe u w

noncomputable section

/-! ## Adic limits of modules -/

/-- An inverse system is annihilated by the indicated power of `I` at every stage. -/
def IsPowerAnnihilated {A : Type u} [CommRing A] (I : Ideal A)
    (F : NaturalInverseSystem.{u, w} A) : Prop :=
  ∀ n : ℕ+,
    Module.IsTorsionBySet A (F.obj (Opposite.op n))
      ((I ^ (n : ℕ) : Ideal A) : Set A)

/-- The quotient module occurring in the `n`th step of an `I`-adic system. -/
abbrev quotientModule {A : Type u} [CommRing A] (I : Ideal A)
    (M : ModuleCat.{w} A) (n : ℕ) : ModuleCat.{w} A :=
  ModuleCat.of A (M ⧸ (I ^ n • (⊤ : Submodule A M)))

/-- A source-faithful presentation of the transition map as a quotient map. -/
structure QuotientStep {A : Type u} [CommRing A] (I : Ideal A)
    (F : NaturalInverseSystem.{u, w} A) (n : ℕ+) where
  equivalence : quotientModule I (F.obj (Opposite.op (n + 1))) (n : ℕ) ≅
    F.obj (Opposite.op n)
  transition_eq :
    ModuleCat.ofHom
        (equivalence.hom.hom.comp
          (Submodule.mkQ (I ^ (n : ℕ) •
            (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))))) =
      transitionMap F (i := n + 1) (j := n)
        (PNat.lt_add_right n 1).le

/-- The transition maps of `F` are the canonical quotient maps by powers of `I`. -/
def IsQuotientInverseSystem {A : Type u} [CommRing A] (I : Ideal A)
    (F : NaturalInverseSystem.{u, w} A) : Prop :=
  ∀ n : ℕ+, Nonempty (QuotientStep I F n)

/-- A quotient identification of the inverse limit with one of its stages. -/
structure LimitQuotientPresentation {A : Type u} [CommRing A] (I : Ideal A)
    (F : NaturalInverseSystem.{u, w} A) (n : ℕ+) where
  equivalence :
    (inverseLimitModule F ⧸
      (I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)))) ≃ₗ[A]
        F.obj (Opposite.op n)
  projection_eq :
    ModuleCat.ofHom
        (equivalence.toLinearMap.comp
          (Submodule.mkQ (I ^ (n : ℕ) •
            (⊤ : Submodule A (inverseLimitModule F))))) =
      limit.π F (Opposite.op n)

/-- The limit of a power-annihilated inverse system is adically complete. -/
theorem limit_complete_pre {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (F : NaturalInverseSystem.{u, w} A)
    (hF : IsPowerAnnihilated I F) :
    IsAdicComplete I (inverseLimitModule F) := by
  sorry

/-- A compatible quotient system has the expected quotients and complete limit. -/
theorem limit_complete {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (F : NaturalInverseSystem.{u, w} A)
    (hF : IsQuotientInverseSystem I F) :
    (∀ n : ℕ+, Nonempty (LimitQuotientPresentation I F n)) ∧
      IsAdicComplete I (inverseLimitModule F) := by
  sorry

/-! ## Graded inverse systems -/

/-- An inverse system of internally graded modules whose transition maps preserve degree. -/
structure GradedInverseSystem {A : Type u} [CommRing A]
    (G : GradedRingData A) where
  system : NaturalInverseSystem.{u, w} A
  grading : ∀ n : ℕ+, GradedModuleData G (system.obj (Opposite.op n))
  map_isGraded : ∀ (n m : ℕ+) (h : m ≤ n),
    IsGradedLinearMap G (grading n) (grading m)
      (transitionMap system (i := n) (j := m) h).hom

/-- Finiteness of every module in a graded inverse system. -/
def IsFiniteGradedInverseSystem {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) : Prop :=
  ∀ n : ℕ+, Module.Finite A (F.system.obj (Opposite.op n))

/-- A graded presentation of a quotient by a homogeneous submodule. -/
structure GradedQuotientPresentation {A : Type u} [CommRing A]
    (G : GradedRingData A) (I : Ideal A)
    {M N : Type w} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) (n : ℕ) where
  quotient : GradedModuleData G (M ⧸ (I ^ n • (⊤ : Submodule A M)))
  equivalence : GradedLinearEquiv G quotient 𝓝

/-- A graded inverse-system step with its canonical quotient map. -/
structure GradedQuotientStep {A : Type u} [CommRing A]
    (G : GradedRingData A) (I : Ideal A)
    (F : GradedInverseSystem.{u, w} G) (n : ℕ+) where
  quotient :
    GradedModuleData G
      (F.system.obj (Opposite.op (n + 1)) ⧸
        (I ^ (n : ℕ) •
          (⊤ : Submodule A (F.system.obj (Opposite.op (n + 1))))) )
  equivalence : GradedLinearEquiv G quotient (F.grading n)
  transition_eq :
    ModuleCat.ofHom
        (equivalence.toLinearEquiv.toLinearMap.comp
          (Submodule.mkQ (I ^ (n : ℕ) •
            (⊤ : Submodule A (F.system.obj (Opposite.op (n + 1))))))) =
      transitionMap F.system (i := n + 1) (j := n)
        (PNat.lt_add_right n 1).le

/-- The transition maps of a graded system are quotient maps by powers of `I`. -/
def IsGradedQuotientInverseSystem {A : Type u} [CommRing A]
    (G : GradedRingData A) (I : Ideal A)
    (F : GradedInverseSystem.{u, w} G) : Prop :=
  ∀ n : ℕ+, Nonempty (GradedQuotientStep G I F n)

/-- The finiteness theorem for graded inverse systems. -/
theorem finiteness_graded {A : Type u} [CommRing A] [IsNoetherianRing A]
    (G : GradedRingData A) (I : Ideal A)
    (hI : I ≤ irrelevantIdeal G) (hIhom : I.IsHomogeneous G.component)
    (F : GradedInverseSystem.{u, w} G)
    (hF : IsGradedQuotientInverseSystem G I F)
    (hfinite : IsFiniteGradedInverseSystem G F) :
    ∃ N : ModuleCat.{w} A, ∃ 𝓝 : GradedModuleData G N,
      Module.Finite A N ∧
        ∀ n : ℕ+,
          Nonempty
            (GradedQuotientPresentation G I 𝓝 (F.grading n) (n : ℕ)) := by
  sorry

/-! ## The Daniel--Litt comparison -/

/-- A compatible system of degree-preserving maps from one graded module. -/
structure GradedCompatibleMap {A : Type u} [CommRing A]
    (G : GradedRingData A) {M : Type w} [AddCommGroup M] [Module A M]
    (𝓜 : GradedModuleData G M) (F : GradedInverseSystem.{u, w} G) where
  map : ∀ n : ℕ+, M →ₗ[A] F.system.obj (Opposite.op n)
  isGraded : ∀ n : ℕ+, IsGradedLinearMap G 𝓜 (F.grading n) (map n)
  compatible : ∀ (n m : ℕ+) (h : m ≤ n),
    (transitionMap F.system (i := n) (j := m) h).hom.comp (map n) = map m

/-- The component map of a transition morphism between graded modules. -/
def gradedComponentMap {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) (d : ℤ)
    {i j : ℕ+ᵒᵖ} (f : i ⟶ j) :
    AddCommGrpCat.of ((F.grading i.unop).component d) ⟶
      AddCommGrpCat.of ((F.grading j.unop).component d) :=
  AddCommGrpCat.ofHom
    (componentAddHom G (F.grading i.unop) (F.grading j.unop)
      (transitionMap F.system (leOfHom f.unop)).hom
      (F.map_isGraded i.unop j.unop (leOfHom f.unop)) d)

theorem gradedComponentMap_id {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) (d : ℤ)
    (i : ℕ+ᵒᵖ) :
    gradedComponentMap G F d (𝟙 i) = 𝟙 _ := by
  sorry

theorem gradedComponentMap_comp {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) (d : ℤ)
    {i j k : ℕ+ᵒᵖ} (f : i ⟶ j) (g : j ⟶ k) :
    gradedComponentMap G F d (f ≫ g) =
      gradedComponentMap G F d f ≫ gradedComponentMap G F d g := by
  sorry

/-- The inverse system of degree-`d` components. -/
def gradedComponentSystem {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) (d : ℤ) :
    InverseSystem ℕ+ (AddCommGrpCat.{w}) where
  obj i := AddCommGrpCat.of ((F.grading i.unop).component d)
  map := gradedComponentMap G F d
  map_id := by
    intro i
    exact gradedComponentMap_id G F d i
  map_comp := by
    intro i j k f g
    exact gradedComponentMap_comp G F d f g

/-- The limit of the degree-`d` components of a graded inverse system. -/
abbrev gradedComponentLimit {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) (d : ℤ) :
    AddCommGrpCat.{w} :=
  InverseSystemLimit (gradedComponentSystem G F d)

/- The following three declarations expose the canonical coordinatewise map
   `M ⊗ A' → G_n` and the induced map to the inverse limit.  The quotient-module
   action is Mathlib's `Module.IsTorsionBySet.module`, transported along the
   canonical map `A' → A/I^n`. -/

noncomputable abbrev completionModule {A : Type u} [CommRing A] (I : Ideal A)
    (n : ℕ) {N : Type w} [AddCommGroup N] [Module A N]
    (hN : Module.IsTorsionBySet A N ((I ^ n : Ideal A) : Set A)) :
    Module (ringCompletion I) N := by
  letI : SMul (A ⧸ I ^ n) N := hN.hasSMul
  letI : Module (A ⧸ I ^ n) N := hN.module
  exact Module.compHom N (AdicCompletion.evalₐ I n).toRingHom

theorem completionModuleScalarTower {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) {N : Type w} [AddCommGroup N] [Module A N]
    (hN : Module.IsTorsionBySet A N ((I ^ n : Ideal A) : Set A)) :
    @IsScalarTower A (ringCompletion I) N Algebra.toSMul
      (completionModule I n hN).toSMul _ :=
  letI : Module (A ⧸ I ^ n) N := hN.module
  by
    let completionSMul : SMul (ringCompletion I) N :=
      (completionModule I n hN).toSMul
    refine @IsScalarTower.mk A (ringCompletion I) N Algebra.toSMul
      completionSMul _ ?_
    intro a b x
    have hsmul (c : ringCompletion I) (y : N) :
        completionSMul.smul c y = (AdicCompletion.evalₐ I n c) • y := by
      change
        (letI : SMul (A ⧸ I ^ n) N := hN.hasSMul
         letI : Module (A ⧸ I ^ n) N := hN.module
         (Module.compHom N (AdicCompletion.evalₐ I n).toRingHom).toSMul).smul c y = _
      rfl
    rw [Algebra.smul_def]
    change completionSMul.smul ((algebraMap A (ringCompletion I)) a * b) x =
      a • completionSMul.smul b x
    rw [hsmul, hsmul]
    rw [map_mul]
    have halg :
        (AdicCompletion.evalₐ I n) ((algebraMap A (ringCompletion I)) a) =
          Ideal.Quotient.mk (I ^ n) a := by
      rw [show algebraMap A (ringCompletion I) a = AdicCompletion.of I A a by rfl,
        AdicCompletion.evalₐ_of]
    rw [halg, @SemigroupAction.mul_smul (A ⧸ I ^ n) N _
      hN.module.toDistribMulAction.toSemigroupAction]
    simpa only [Module.IsTorsionBySet.module] using
      (Module.IsTorsionBySet.mk_smul hN a
        ((AdicCompletion.evalₐ I n) b • x))

noncomputable def completionTensorCoordinate {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) {M N : Type w}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (hN : Module.IsTorsionBySet A N ((I ^ n : Ideal A) : Set A))
    (f : M →ₗ[A] N) :
    M ⊗[A] ringCompletion I →ₗ[A] N := by
  letI : Module (A ⧸ I ^ n) N := hN.module
  letI : Module (ringCompletion I) N := completionModule I n hN
  letI : IsScalarTower A (ringCompletion I) N :=
    completionModuleScalarTower I n hN
  exact TensorProduct.lift
    (((Algebra.lsmul (R := A) (A := ringCompletion I) (B := A) N).toLinearMap.flip).comp f)

theorem completionTensorCoordinate_naturality
    {A : Type u} [CommRing A] (G : GradedRingData A) (I : Ideal A)
    (F : GradedInverseSystem.{u, max u w} G)
    (hF : IsPowerAnnihilated I F.system)
    {M : Type (max u w)} [AddCommGroup M] [Module A M]
    (𝓜 : GradedModuleData G M) (φ : GradedCompatibleMap G 𝓜 F)
    {i j : ℕ+ᵒᵖ} (f : i ⟶ j) :
    (F.system.map f).hom.comp
        (completionTensorCoordinate I (i.unop : ℕ) (hF i.unop)
          (φ.map i.unop)) =
      completionTensorCoordinate I (j.unop : ℕ) (hF j.unop)
        (φ.map j.unop) := by
  sorry

/-- The map induced by a compatible graded system of maps after tensoring with `A'`. -/
noncomputable def inducedTensorLimitMap
    {A : Type u} [CommRing A] (G : GradedRingData A) (I : Ideal A)
    (F : GradedInverseSystem.{u, max u w} G)
    (hF : IsPowerAnnihilated I F.system)
    {M : Type (max u w)} [AddCommGroup M] [Module A M]
    (𝓜 : GradedModuleData G M) (φ : GradedCompatibleMap G 𝓜 F) :
    M ⊗[A] ringCompletion I →ₗ[A] inverseLimitModule F.system := by
  let c : Cone F.system :=
    { pt := ModuleCat.of A (M ⊗[A] ringCompletion I)
      π :=
        { app := fun i =>
            ModuleCat.ofHom
              (completionTensorCoordinate I (i.unop : ℕ) (hF i.unop)
                (φ.map i.unop))
          naturality := by
            intro i j f
            apply ModuleCat.hom_ext
            simpa using
              (completionTensorCoordinate_naturality G I F hF 𝓜 φ f).symm } }
  exact (limit.lift F.system c).hom

theorem inducedTensorLimitMap_projection
    {A : Type u} [CommRing A] (G : GradedRingData A) (I : Ideal A)
    (F : GradedInverseSystem.{u, max u w} G)
    (hF : IsPowerAnnihilated I F.system)
    {M : Type (max u w)} [AddCommGroup M] [Module A M]
    (𝓜 : GradedModuleData G M) (φ : GradedCompatibleMap G 𝓜 F)
    (n : ℕ+) :
    (limit.π F.system (Opposite.op n)).hom.comp
        (inducedTensorLimitMap G I F hF 𝓜 φ) =
      completionTensorCoordinate I (n : ℕ) (hF n) (φ.map n) := by
  sorry

/-- The Daniel--Litt lemma: an isomorphism after completion is detected degreewise. -/
theorem daniel_litt {A : Type u} [CommRing A]
    (G : GradedRingData A) (I : Ideal A)
    (hI : I ≤ irrelevantIdeal G) (hIhom : I.IsHomogeneous G.component)
    (F : GradedInverseSystem.{u, max u w} G)
    (hF : IsPowerAnnihilated I F.system)
    {M : Type (max u w)} [AddCommGroup M] [Module A M]
    (𝓜 : GradedModuleData G M) (φ : GradedCompatibleMap G 𝓜 F)
    (hφ : Function.Bijective (inducedTensorLimitMap G I F hF 𝓜 φ)) :
    ∀ d : ℤ, ∃ e : (𝓜.component d) ≃+ gradedComponentLimit G F d,
      ∀ n : ℕ+, ∀ x : 𝓜.component d,
        (limit.π (gradedComponentSystem G F d) (Opposite.op n)).hom (e x) =
          componentAddHom G 𝓜 (F.grading n) (φ.map n) (φ.isGraded n) d x := by
  sorry

end

end Formalization.Books.Algebra.Unit98
