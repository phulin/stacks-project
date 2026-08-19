import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Mathlib.RingTheory.PicardGroup

/-!
# More on Algebra, Chapter 118: Picard groups of rings

The canonical Mathlib definitions `Module.Invertible` and `CommRing.Pic` are
used for invertible modules and the Picard group.  The declarations below
record the source-facing characterizations and the UFD calculation.
-/

namespace Formalization.Books.MoreAlgebra.Unit118

open scoped TensorProduct

universe u v

noncomputable section

/-! ## Invertible modules -/

/- The source's phrase “trivial invertible module” is represented by the
canonical proposition `Nonempty (M ≃ₗ[R] R)`. -/

/-- An inverse module in the sense of the source's condition (3). -/
def HasTensorInverse
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ N : ModuleCat.{max u v} R,
    Nonempty (M ⊗[R] N ≃ₗ[R] R)

/-- The three conditions in the source's characterization of invertible modules. -/
def invertibleModuleConditions
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : List Prop :=
  [Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank R M 1,
    Module.Invertible R M,
    HasTensorInverse R M]

/-- Finite locally free modules of rank one are precisely the invertible modules. -/
theorem finiteLocallyFreeOfRank_one_iff_invertible
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank R M 1 ↔
      Module.Invertible R M := by
  constructor
  · intro hM
    obtain ⟨s, hs, hsr⟩ := hM
    have hfin : Formalization.Books.Algebra.Unit78.FiniteLocallyFree R M := by
      refine ⟨s, hs, ?_⟩
      intro f
      intro hf
      obtain ⟨e⟩ := hsr f hf
      exact ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
        Module.Free.of_equiv e.symm⟩
    have hfp : Formalization.Books.Algebra.Unit78.FiniteProjective R M :=
      ((Formalization.Books.Algebra.Unit78.finite_projective_characterization
        (R := R) (M := M)).out 6 1).mp hfin
    let : Module.Finite R M := hfp.1
    let : Module.Projective R M := hfp.2
    let : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
    refine ⟨?_⟩
    apply bijective_of_localized_span s hs
    intro r
    let S := Submonoid.powers r.1
    let A := Localization S
    let L := LocalizedModule S M
    obtain ⟨e⟩ := hsr r r.property
    let eA : L ≃ₗ[A] A := e ≪≫ₗ
      Finsupp.uniqueLinearEquiv A (α := Fin 1) A default
    let : Module.Invertible A L := Module.Invertible.congr eA.symm
    let P := Module.Dual R M ⊗[R] M
    let ibcM := LocalizedModule.isBaseChange S M
    let ibcP := LocalizedModule.isBaseChange S P
    let ibcR := LocalizedModule.isBaseChange S R
    have hP (x : P) : ibcP.equiv.symm (LocalizedModule.mk x 1) = 1 ⊗ₜ[R] x := by
      simpa [ibcP] using IsBaseChange.equiv_symm_apply ibcP x
    have hM (x : M) : ibcM.equiv.symm (LocalizedModule.mk x 1) = 1 ⊗ₜ[R] x := by
      simpa [ibcM] using IsBaseChange.equiv_symm_apply ibcM x
    let hdual : A ⊗[R] Module.Dual R M ≃ₗ[A] Module.Dual A L :=
      (Module.FinitePresentation.isBaseChange_map R M R A).equiv
        ≪≫ₗ (TensorProduct.AlgebraTensorModule.rid R A A).congrRight
        ≪≫ₗ ibcM.equiv.congrLeft A A
    let sourceEquiv : LocalizedModule S P ≃ₗ[A] Module.Dual A L ⊗[A] L :=
      ibcP.equiv.symm ≪≫ₗ TensorProduct.AlgebraTensorModule.distribBaseChange R A
        (Module.Dual R M) M ≪≫ₗ TensorProduct.AlgebraTensorModule.congr hdual ibcM.equiv
    let targetEquiv : A ≃ₗ[A] LocalizedModule S R :=
      (TensorProduct.AlgebraTensorModule.rid R A A).symm ≪≫ₗ ibcR.equiv
    have heq : LocalizedModule.map S (contractLeft R M) =
        targetEquiv.toLinearMap.comp
          ((contractLeft A L).comp sourceEquiv.toLinearMap) := by
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := ibcP.equiv.surjective x
      induction x using TensorProduct.induction_on with
      | zero => simp [sourceEquiv, targetEquiv]
      | add x y hx hy => simp [map_add, hx, hy]
      | tmul a x =>
        induction x using TensorProduct.induction_on with
        | zero => simp [sourceEquiv, targetEquiv]
        | add x y hx hy =>
          calc
            _ = ((LocalizedModule.map S) (contractLeft R M))
                  (ibcP.equiv (a ⊗ₜ[R] x)) +
                ((LocalizedModule.map S) (contractLeft R M))
                  (ibcP.equiv (a ⊗ₜ[R] y)) := by
              simp only [TensorProduct.tmul_add, map_add]
            _ = (targetEquiv.toLinearMap.comp
                  ((contractLeft A L).comp sourceEquiv.toLinearMap))
                  (ibcP.equiv (a ⊗ₜ[R] x)) +
                (targetEquiv.toLinearMap.comp
                  ((contractLeft A L).comp sourceEquiv.toLinearMap))
                  (ibcP.equiv (a ⊗ₜ[R] y)) := by rw [hx, hy]
            _ = _ := by
              simp only [TensorProduct.tmul_add, map_add]
        | tmul f m =>
          have hbase :
              ((TensorProduct.AlgebraTensorModule.rid R A A).congrRight
                (LinearMap.baseChange A f)) (1 ⊗ₜ[R] m) = algebraMap R A (f m) := by
            change (TensorProduct.AlgebraTensorModule.rid R A A)
                ((LinearMap.baseChange A f) (1 ⊗ₜ[R] m)) = algebraMap R A (f m)
            rw [LinearMap.baseChange_tmul,
              TensorProduct.AlgebraTensorModule.rid_tmul]
            simp [Algebra.smul_def]
          simp [sourceEquiv, targetEquiv, hdual, ibcM, ibcP, ibcR, hP,
            LocalizedModule.mk, Module.FinitePresentation.isBaseChange_map]
          rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
            TensorProduct.AlgebraTensorModule.congr_tmul]
          simp [hdual, ibcM, ibcP, ibcR, hP, hM,
            LocalizedModule.mk,
            TensorProduct.AlgebraTensorModule.rid_tmul, IsBaseChange.equiv_tmul,
            LinearMap.baseChange_tmul, hbase,
            Module.FinitePresentation.isBaseChange_map]
          have hmk : f m /ₒ (1 : S) = algebraMap R A (f m) := by
            change Localization.mk (f m) (1 : S) = algebraMap R A (f m)
            exact Localization.mk_one_eq_algebraMap (f m)
          rw [hmk]
          rw [← OreLocalization.one_def, mul_one]
    rw [heq]
    exact (targetEquiv.bijective.comp Module.Invertible.bijective).comp
      sourceEquiv.bijective
  · intro hM
    let : Module.Invertible R M := hM
    obtain ⟨s, hs, hsr⟩ := Module.Invertible.exists_finset_free_localization R M
    refine ⟨s, ?_, ?_⟩
    · simpa using hs
    · intro f hf
      let : Module.Free (Localization.Away f) (LocalizedModule.Away f M) := hsr f hf
      obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := Localization.Away f)
        (M := LocalizedModule.Away f M)).mp inferInstance
      exact ⟨e ≪≫ₗ (Finsupp.uniqueLinearEquiv (Localization.Away f)
        (Localization.Away f) default).symm⟩

/-- A module is invertible precisely when it has a tensor inverse. -/
theorem invertible_iff_hasTensorInverse
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Invertible R M ↔ HasTensorInverse R M := by
  constructor
  · intro hM
    let _ : Module.Invertible R M := hM
    refine ⟨ModuleCat.of R (Module.Dual R M), ?_⟩
    exact ⟨TensorProduct.comm R M (Module.Dual R M) ≪≫ₗ
      Module.Invertible.linearEquiv R M⟩
  · rintro ⟨N, ⟨e⟩⟩
    exact Module.Invertible.left e

/-- The three conditions in the source's lemma are equivalent. -/
theorem invertibleModuleConditions_tfae
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    List.TFAE (invertibleModuleConditions R M) := by
  change List.TFAE [
    Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank R M 1,
    Module.Invertible R M,
    HasTensorInverse R M]
  tfae_have 1 ↔ 2 := finiteLocallyFreeOfRank_one_iff_invertible
  tfae_have 2 ↔ 3 := invertible_iff_hasTensorInverse
  tfae_finish

/-- Any tensor inverse is isomorphic to the dual module. -/
theorem tensorInverse_equiv_dual
    {R : Type u} {M : Type v} {N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ⊗[R] N ≃ₗ[R] R) :
    Nonempty (N ≃ₗ[R] Module.Dual R M) := by
  exact ⟨Module.Invertible.linearEquivDual
    (TensorProduct.comm R N M ≪≫ₗ e)⟩

/-- Triviality of an invertible module is the same as freeness. -/
theorem trivial_invertible_iff_free
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Invertible R M] :
    Nonempty (M ≃ₗ[R] R) ↔ Module.Free R M :=
  Module.Invertible.free_iff_linearEquiv.symm

/-! ## The Picard group -/

/- The source's `Pic(R)` is Mathlib's `CommRing.Pic R`.  Its `CommGroup`
instance, tensor-product multiplication, identity, and dual inverse are
already provided by `Mathlib.RingTheory.PicardGroup`; the following
source-facing statements expose those operations together. -/

/-- The class of a tensor product is the product of the classes. -/
theorem picard_class_tensor
    {R : Type u} {M N : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Invertible R M]
    [AddCommGroup N] [Module R N] [Module.Invertible R N] :
    CommRing.Pic.mk R (M ⊗[R] N) = CommRing.Pic.mk R M * CommRing.Pic.mk R N :=
  CommRing.Pic.mk_tensor

/-- The inverse class is represented by the dual module. -/
theorem picard_class_dual
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Invertible R M] :
    CommRing.Pic.mk R (Module.Dual R M) = (CommRing.Pic.mk R M)⁻¹ :=
  CommRing.Pic.mk_dual

/-- The free rank-one module represents the identity in the Picard group. -/
theorem picard_class_ring (R : Type u) [CommRing R] :
    CommRing.Pic.mk R R = 1 :=
  CommRing.Pic.mk_self

/-- A Picard class is the identity precisely when its module is trivial. -/
theorem picard_class_eq_one_iff_trivial
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Invertible R M] :
    CommRing.Pic.mk R M = 1 ↔ Nonempty (M ≃ₗ[R] R) :=
  CommRing.Pic.mk_eq_one_iff

/-! ## UFDs -/

/-- The Picard group of a unique factorization domain is trivial. -/
theorem picard_group_subsingleton_of_ufd
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    Subsingleton (CommRing.Pic R) := by
  infer_instance

end

end Formalization.Books.MoreAlgebra.Unit118
