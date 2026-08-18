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

private theorem power_smul_top_eq_bot_of_torsion
    {A : Type u} [CommRing A] (I : Ideal A)
    {M : Type w} [AddCommGroup M] [Module A M] (n : ℕ)
    (hM : Module.IsTorsionBySet A M ((I ^ n : Ideal A) : Set A)) :
    I ^ n • (⊤ : Submodule A M) = ⊥ := by
  apply le_antisymm
  · refine Submodule.smul_le.mpr ?_
    intro a ha x hx
    exact @hM x ⟨a, show a ∈ (I ^ n : Ideal A) from ha⟩
  · exact bot_le

private theorem isAdicComplete_of_completion_retraction
    {A : Type u} [CommRing A] (I : Ideal A)
    {M : Type w} [AddCommGroup M] [Module A M]
    (hI : I.FG)
    (r : AdicCompletion I M →ₗ[A] M)
    (hr : r.comp (AdicCompletion.of I M) = LinearMap.id) :
    IsAdicComplete I M := by
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · refine ⟨?_⟩
    intro x hx
    have hzero : AdicCompletion.of I M x = 0 := by
      apply IsHausdorff.haus (I := I)
        (inferInstance : IsHausdorff I (AdicCompletion I M))
      intro n
      rw [SModEq.sub_mem]
      have hmap :
          Submodule.map (AdicCompletion.of I M)
              (I ^ n • (⊤ : Submodule A M)) ≤
            I ^ n • (⊤ : Submodule A (AdicCompletion I M)) := by
        rw [Submodule.map_smul'', Submodule.map_top]
        exact smul_mono_right _ le_top
      have hxmem := hmap (Submodule.mem_map_of_mem (SModEq.sub_mem.mp (hx n)))
      simpa using hxmem
    have hrex := congrArg (fun f => f x) hr
    rw [LinearMap.comp_apply, LinearMap.id_apply] at hrex
    rw [← hrex, hzero, map_zero]
  · refine ⟨?_⟩
    intro f hf
    obtain ⟨z, hz⟩ := (AdicCompletion.isAdicComplete hI).toIsPrecomplete.prec'
      (fun n => AdicCompletion.of I M (f n)) (by
        intro m n hmn
        rw [SModEq.sub_mem]
        have hmap :
            Submodule.map (AdicCompletion.of I M)
                (I ^ m • (⊤ : Submodule A M)) ≤
              I ^ m • (⊤ : Submodule A (AdicCompletion I M)) := by
          rw [Submodule.map_smul'', Submodule.map_top]
          exact smul_mono_right _ le_top
        exact hmap (Submodule.mem_map_of_mem (SModEq.sub_mem.mp (hf hmn))))
    refine ⟨r z, ?_⟩
    intro n
    rw [SModEq.sub_mem]
    have hmap :
        Submodule.map r (I ^ n • (⊤ : Submodule A (AdicCompletion I M))) ≤
          I ^ n • (⊤ : Submodule A M) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right _ le_top
    have hzmem := hmap (Submodule.mem_map_of_mem (SModEq.sub_mem.mp (hz n)))
    have hrex := congrArg (fun g => g (f n)) hr
    rw [LinearMap.comp_apply, LinearMap.id_apply] at hrex
    simpa [map_sub, hrex] using hzmem

/-- The limit of a power-annihilated inverse system is adically complete. -/
theorem limit_complete_pre {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (F : NaturalInverseSystem.{u, w} A)
    (hF : IsPowerAnnihilated I F) :
    IsAdicComplete I (inverseLimitModule F) := by
  let hker (n : ℕ+) :
      I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)) ≤
        LinearMap.ker (limit.π F (Opposite.op n)).hom := by
    refine Submodule.smul_le.mpr ?_
    intro a ha x hx
    change (limit.π F (Opposite.op n)).hom (a • x) = 0
    rw [map_smul]
    exact @hF n ((limit.π F (Opposite.op n)).hom x) ⟨a, ha⟩
  let q (n : ℕ+) :
      (inverseLimitModule F ⧸
        (I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F)))) →ₗ[A]
        F.obj (Opposite.op n) :=
    (I ^ (n : ℕ) • (⊤ : Submodule A (inverseLimitModule F))).liftQ
      (limit.π F (Opposite.op n)).hom (hker n)
  let c : Cone F :=
    { pt := ModuleCat.of A (AdicCompletion I (inverseLimitModule F))
      π :=
        { app := fun i =>
            ModuleCat.ofHom
              ((q i.unop).comp
                (AdicCompletion.eval I (inverseLimitModule F) (i.unop : ℕ)))
          naturality := by
            intro i j f
            apply ModuleCat.hom_ext
            ext x
            apply AdicCompletion.induction_on I (inverseLimitModule F) x
            intro b
            have hproj :
                (F.map f).hom.comp (limit.π F i).hom =
                  (limit.π F j).hom := by
              exact congrArg ModuleCat.Hom.hom (limit.w F f)
            have hji : j.unop ≤ i.unop := leOfHom f.unop
            have hdiff : b.val j.unop - b.val i.unop ∈
                I ^ (j.unop : ℕ) • (⊤ : Submodule A (inverseLimitModule F)) :=
              SModEq.sub_mem.mp (b.property hji)
            have hzero := hker j.unop hdiff
            rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hzero
            change
              (limit.π F j).hom (b.val j.unop) =
                (F.map f).hom ((limit.π F i).hom (b.val i.unop))
            calc
              (limit.π F j).hom (b.val j.unop) =
                  (limit.π F j).hom (b.val i.unop) := hzero
              _ = (F.map f).hom ((limit.π F i).hom (b.val i.unop)) := by
                exact (congrArg (fun y => y (b.val i.unop)) hproj).symm
      }
    }
  let r : AdicCompletion I (inverseLimitModule F) →ₗ[A]
      inverseLimitModule F :=
    (limit.lift F c).hom
  apply isAdicComplete_of_completion_retraction I hI r
  apply LinearMap.ext
  intro x
  apply Concrete.limit_ext F
  intro n
  simp [r, c, q]

/-- A compatible quotient system has the expected quotients and complete limit. -/
theorem limit_complete {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (F : NaturalInverseSystem.{u, w} A)
    (hF : IsQuotientInverseSystem I F) :
    (∀ n : ℕ+, Nonempty (LimitQuotientPresentation I F n)) ∧
      IsAdicComplete I (inverseLimitModule F) := by
  constructor
  · sorry
  · apply limit_complete_pre I hI F
    intro n
    rcases hF n with ⟨s⟩
    intro x a
    obtain ⟨z, hz⟩ := Submodule.mkQ_surjective
      (I ^ (n : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (n + 1)))))
      (s.equivalence.inv.hom x)
    calc
      (a : A) • x = (a : A) • s.equivalence.hom.hom (s.equivalence.inv.hom x) := by simp
      _ = s.equivalence.hom.hom ((a : A) • s.equivalence.inv.hom x) := by
        rw [map_smul]
      _ = s.equivalence.hom.hom ((a : A) •
          (I ^ (n : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))).mkQ z) := by
        rw [← hz]
      _ = 0 := by
        have haz :
            (I ^ (n : ℕ) • (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))).mkQ
                ((a : A) • z) = 0 := by
          change Submodule.Quotient.mk ((a : A) • z) = 0
          apply (Submodule.Quotient.mk_eq_zero _).mpr
          exact Submodule.smul_mem_smul a.property (by simp)
        calc
          s.equivalence.hom.hom ((a : A) •
              (I ^ (n : ℕ) •
                (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))).mkQ z) =
              s.equivalence.hom.hom
                ((I ^ (n : ℕ) •
                  (⊤ : Submodule A (F.obj (Opposite.op (n + 1))))).mkQ
                    ((a : A) • z)) := by
            simp only [map_smul]
          _ = 0 := by rw [haz, map_zero]

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
  projection_isGraded :
    IsGradedLinearMap G 𝓜 quotient
      (Submodule.mkQ (I ^ n • (⊤ : Submodule A M)))
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
  projection_isGraded :
    IsGradedLinearMap G (F.grading (n + 1)) quotient
      (Submodule.mkQ (I ^ (n : ℕ) •
        (⊤ : Submodule A (F.system.obj (Opposite.op (n + 1))))))
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
  simp only [gradedComponentMap, transitionMap_refl]
  apply AddCommGrpCat.hom_ext
  ext x
  rfl

theorem gradedComponentMap_comp {A : Type u} [CommRing A]
    (G : GradedRingData A) (F : GradedInverseSystem.{u, w} G) (d : ℤ)
    {i j k : ℕ+ᵒᵖ} (f : i ⟶ j) (g : j ⟶ k) :
    gradedComponentMap G F d (f ≫ g) =
      gradedComponentMap G F d f ≫ gradedComponentMap G F d g := by
  simp only [gradedComponentMap]
  apply AddCommGrpCat.hom_ext
  ext x
  change (transitionMap F.system (leOfHom (f ≫ g).unop)).hom x =
    (transitionMap F.system (leOfHom g.unop)).hom
      ((transitionMap F.system (leOfHom f.unop)).hom x)
  rw [← ConcreteCategory.comp_apply, transitionMap_comp]

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
  let : Module (A ⧸ I ^ (i.unop : ℕ)) (F.system.obj i) := (hF i.unop).module
  let : Module (A ⧸ I ^ (j.unop : ℕ)) (F.system.obj j) := (hF j.unop).module
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m r =>
    induction r using AdicCompletion.induction_on I A with
    | _ a =>
      change (F.system.map f).hom
          ((AdicCompletion.evalₐ I (i.unop : ℕ) (AdicCompletion.mk I A a)) •
            (φ.map i.unop) m) =
        (AdicCompletion.evalₐ I (j.unop : ℕ) (AdicCompletion.mk I A a)) •
          (φ.map j.unop) m
      rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
      change (F.system.map f).hom ((a.val i.unop) • (φ.map i.unop) m) =
        (a.val j.unop) • (φ.map j.unop) m
      rw [map_smul]
      have hcompat :=
        φ.compatible i.unop j.unop (leOfHom f.unop)
      have hmap :
          (F.system.map f).hom.comp (φ.map i.unop) = φ.map j.unop := by
        rw [← hcompat]
        congr 1
      have hmap_apply := congrArg (fun q => q m) hmap
      rw [LinearMap.comp_apply] at hmap_apply
      rw [hmap_apply]
      have ha :
          a.val i.unop ≡ a.val j.unop
            [SMOD ((I ^ (j.unop : ℕ)) • (⊤ : Submodule A A))] :=
        (a.property (leOfHom f.unop)).symm
      have hmem : a.val i.unop - a.val j.unop ∈
          (I ^ (j.unop : ℕ) : Ideal A) := by
        have hmem' : a.val i.unop - a.val j.unop ∈
            (I ^ (j.unop : ℕ)) • (⊤ : Submodule A A) :=
          (SModEq.sub_mem
            (U := (I ^ (j.unop : ℕ)) • (⊤ : Submodule A A))).mp ha
        simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hmem'
      have hzero := @hF j.unop ((φ.map j.unop) m)
        ⟨a.val i.unop - a.val j.unop,
          hmem⟩
      rw [← sub_eq_zero, ← sub_smul]
      simpa using hzero

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
