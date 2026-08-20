import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Formalization.Books.Algebra.Unit134.NaiveCotangentComplex
import Formalization.Books.Algebra.Unit14.BaseChange
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.Quotient

/-!
# Commutative Algebra, Chapter 138: Formally smooth maps

This file records the lifting, cotangent, descent, and exact-sequence
statements in the chapter.  The formal-smooth and smooth predicates are the
canonical `RingHom` predicates, while the extension and filtered-colimit
interfaces reuse Mathlib and the earlier formalization chapters.
-/

namespace Formalization.Books.Algebra.Unit138

open scoped TensorProduct

noncomputable section

universe u v

/-! ## Source-facing interfaces for split sequences and presentations -/

/-- A split short exact sequence of modules, with the splitting written as a
section of the surjection. -/
def IsSplitExactLinearSequence
    {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) : Prop :=
  Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
    ∃ s : P →ₗ[R] N, g.comp s = LinearMap.id

/-- A section of the square-zero quotient attached to an algebra extension.
The kernel in the quotient is the kernel of the extension map. -/
def extensionHasSection
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) : Prop :=
  ∃ σ : S →ₐ[R]
      P.Ring ⧸ (RingHom.ker (IsScalarTower.toAlgHom R P.Ring S).toRingHom ^ 2),
    (IsScalarTower.toAlgHom R P.Ring S).kerSquareLift.comp σ =
      AlgHom.id R S

/-- The conormal--cotangent--differential sequence attached to an extension
is split exact. -/
def extensionDifferentialSplitExact
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) : Prop :=
  IsSplitExactLinearSequence P.cotangentComplex P.toKaehler

/-- The presentation-independent cotangent criterion for formal smoothness. -/
def formalSmoothCotangentCriterion
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  Subsingleton (Algebra.H1Cotangent R S) ∧
    Module.Projective S
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S)

/-! The quotient and filtered-colimit constructions used by later statements. -/

/-- The map on quotients induced by extending an ideal along a ring map. -/
noncomputable def quotientBaseChangeRingMap
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) :
    R ⧸ I →+* S ⧸ Ideal.map f I :=
  Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map

/-- The extension of `A → B → C` determined by a surjection `B → C`. -/
noncomputable def surjectiveExtensionOver
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (h : Function.Surjective (algebraMap B C)) :
    Algebra.Extension A C :=
  Algebra.Extension.ofSurjective (IsScalarTower.toAlgHom A B C) h

/-- The map of extensions induced by `A → B` when both surjections are viewed
as extensions over `A`.  This keeps the cotangent complex of `B → C` over
`A`, so its target is `C ⊗[B] Ω[B⁄A]`. -/
noncomputable def surjectiveExtensionOverHom
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hBC : Function.Surjective (algebraMap B C)) :
    (Formalization.Books.Algebra.Unit134.surjectiveExtension hAC).Hom
      (surjectiveExtensionOver (A := A) hBC) :=
  { toRingHom := algebraMap A B
    toRingHom_algebraMap := by
      intro a
      change algebraMap A B a = algebraMap A B a
      rfl
    algebraMap_toRingHom := by
      intro a
      change algebraMap B C (algebraMap A B a) = algebraMap A C a
      exact (IsScalarTower.algebraMap_apply A B C a).symm }

/-- The tensor product appearing when a stage of a directed system of ring
maps is base changed to the represented source ring. -/
abbrev directedStageBaseChangeRing
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : Formalization.Books.Algebra.Unit127.DirectedRingMapColimit f)
    (i : D.index) : Type u :=
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra (D.sourceDiagram.obj i) (D.targetDiagram.obj i) :=
    (D.stageMap i).toAlgebra
  letI : Algebra (D.sourceDiagram.obj i) R :=
    (D.sourceStageToTarget i).toAlgebra
  D.targetDiagram.obj i ⊗[D.sourceDiagram.obj i] R

/-! ## Formally smooth maps and presentations -/

theorem formallySmooth_iff_lifting
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    f.FormallySmooth ↔
      ∀ ⦃A : Type max u v⦄ [CommRing A] [Algebra R A]
        (I : Ideal A), I ^ 2 = ⊥ →
          Function.Surjective
            ((Ideal.Quotient.mkₐ R I).comp :
              (S →ₐ[R] A) → S →ₐ[R] A ⧸ I) := by
  let : Algebra R S := f.toAlgebra
  exact Algebra.FormallySmooth.iff_comp_surjective (R := R) (A := S)

theorem formallySmooth_baseChange
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hf : f.FormallySmooth) :
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).FormallySmooth := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R R' := g.toAlgebra
  let : Algebra R' (S ⊗[R] R') :=
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).toAlgebra
  let : Algebra.FormallySmooth R S := hf
  rw [RingHom.FormallySmooth]
  exact Algebra.FormallySmooth.of_equiv (Algebra.TensorProduct.commRight R R' S)

theorem formallySmooth_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : f.FormallySmooth) (hg : g.FormallySmooth) :
    (g.comp f).FormallySmooth := by
  exact hf.comp hg

theorem polynomialRing_formallySmooth
    {R : Type u} [CommRing R] (ι : Type v) :
    (algebraMap R (MvPolynomial ι R)).FormallySmooth := by
  exact RingHom.formallySmooth_algebraMap.mpr inferInstance

theorem formallySmooth_iff_extension_section
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension.{u} R S)
    [Algebra.FormallySmooth R P.Ring] :
    Algebra.FormallySmooth R S ↔ extensionHasSection P := by
  simpa only [extensionHasSection] using
    (Algebra.FormallySmooth.iff_split_surjection
      (IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective)

theorem formallySmooth_iff_presentation_section
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι)
    [Algebra.FormallySmooth R P.Ring] :
    Algebra.FormallySmooth R S ↔ extensionHasSection P.toExtension := by
  let oldAlg : Algebra R P.Ring := inferInstance
  let oldFormal : Algebra.FormallySmooth R P.Ring := inferInstance
  have alg_eq : oldAlg = P.toExtension.algebra₁ := by
    apply Algebra.algebra_ext
    intro r
    rfl
  let : Algebra R P.toExtension.Ring := P.toExtension.algebra₁
  let : @Algebra.FormallySmooth R P.toExtension.Ring _ _ P.toExtension.algebra₁ := by
    exact alg_eq ▸ oldFormal
  simpa only [extensionHasSection] using
    (Algebra.FormallySmooth.iff_split_surjection
      (IsScalarTower.toAlgHom R P.toExtension.Ring S)
      P.toExtension.algebraMap_surjective)

private theorem formallySmooth_iff_extension_split_exact
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S)
    [Algebra.FormallySmooth R P.Ring] :
    Algebra.FormallySmooth R S ↔ extensionDifferentialSplitExact P := by
  rw [P.formallySmooth_iff_split_injection]
  simp only [extensionDifferentialSplitExact]
  have hExact : Function.Exact P.cotangentComplex P.toKaehler :=
    P.exact_cotangentComplex_toKaehler
  have hSurj : Function.Surjective P.toKaehler := P.toKaehler_surjective
  constructor
  · rintro ⟨l, hl⟩
    have hinj : Function.Injective P.cotangentComplex := by
      intro x y hxy
      have hleft : ∀ z, l (P.cotangentComplex z) = z := LinearMap.congr_fun hl
      exact (hleft x).symm.trans ((congrArg l hxy).trans (hleft y))
    have hsplit := hExact.split_tfae hinj hSurj
    have hright : ∃ s, P.toKaehler ∘ₗ s = LinearMap.id :=
      (hsplit.out 1 0).mp
        (show ∃ l, l ∘ₗ P.cotangentComplex = LinearMap.id from ⟨l, hl⟩)
    exact ⟨hinj, hExact, hSurj, hright⟩
  · rintro ⟨hinj, hexact, hsurj, ⟨s, hs⟩⟩
    have hsplit := hexact.split_tfae hinj hsurj
    exact (hsplit.out 0 1).mp
      (show ∃ s, P.toKaehler ∘ₗ s = LinearMap.id from ⟨s, hs⟩)

theorem formallySmooth_iff_presentation_split_exact
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι)
    [Algebra.FormallySmooth R P.Ring] :
    Algebra.FormallySmooth R S ↔ extensionDifferentialSplitExact P.toExtension := by
  let oldAlg : Algebra R P.Ring := inferInstance
  let oldFormal : Algebra.FormallySmooth R P.Ring := inferInstance
  have alg_eq : oldAlg = P.toExtension.algebra₁ := by
    apply Algebra.algebra_ext
    intro r
    rfl
  let : Algebra R P.toExtension.Ring := P.toExtension.algebra₁
  let : @Algebra.FormallySmooth R P.toExtension.Ring _ _ P.toExtension.algebra₁ := by
    exact alg_eq ▸ oldFormal
  exact formallySmooth_iff_extension_split_exact P.toExtension

theorem formallySmooth_iff_cotangent_criterion
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.FormallySmooth R S ↔ formalSmoothCotangentCriterion (R := R) (S := S) := by
  rw [Algebra.formallySmooth_iff]
  constructor
  · rintro ⟨hprojective, hsubsingleton⟩
    exact ⟨hsubsingleton, hprojective⟩
  · rintro ⟨hsubsingleton, hprojective⟩
    exact ⟨hprojective, hsubsingleton⟩

theorem h1Cotangent_subsingleton_of_formallySmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallySmooth R S] :
    Subsingleton (Algebra.H1Cotangent R S) :=
  ((formallySmooth_iff_cotangent_criterion
    (R := R) (S := S)).mp inferInstance).1

theorem differentials_projective_of_formallySmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallySmooth R S] :
    Module.Projective S
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) :=
  ((formallySmooth_iff_cotangent_criterion
    (R := R) (S := S)).mp inferInstance).2

theorem formallySmooth_of_h1Cotangent_subsingleton_of_differentials_projective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hH1 : Subsingleton (Algebra.H1Cotangent R S))
    (hΩ : Module.Projective S
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S)) :
    Algebra.FormallySmooth R S :=
  (formallySmooth_iff_cotangent_criterion
    (R := R) (S := S)).mpr ⟨hH1, hΩ⟩

theorem formallySmooth_presentation_characterization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    List.TFAE
      [ Algebra.FormallySmooth R S,
        ∃ P : Algebra.Extension.{u} R S,
          Algebra.FormallySmooth R P.Ring ∧ extensionHasSection P,
        ∀ P : Algebra.Extension.{u} R S,
          Algebra.FormallySmooth R P.Ring → extensionHasSection P,
        ∃ P : Algebra.Extension.{u} R S,
          Algebra.FormallySmooth R P.Ring ∧ extensionDifferentialSplitExact P,
        ∀ P : Algebra.Extension.{u} R S,
          Algebra.FormallySmooth R P.Ring → extensionDifferentialSplitExact P,
        formalSmoothCotangentCriterion (R := R) (S := S) ] := by
  let Q : Formalization.Books.Algebra.Unit134.Presentation R S S :=
    Algebra.Generators.self R S
  have hQ : Algebra.FormallySmooth R Q.Ring := inferInstance
  have hQsection :
      Algebra.FormallySmooth R S ↔ extensionHasSection Q.toExtension :=
    formallySmooth_iff_presentation_section Q
  have hQsplit :
      Algebra.FormallySmooth R S ↔ extensionDifferentialSplitExact Q.toExtension :=
    formallySmooth_iff_presentation_split_exact Q
  let oldAlg : Algebra R Q.Ring := inferInstance
  have alg_eq : oldAlg = Q.toExtension.algebra₁ := by
    apply Algebra.algebra_ext
    intro r
    rfl
  have hQformal :
      @Algebra.FormallySmooth R Q.toExtension.Ring _ _ Q.toExtension.algebra₁ := by
    exact alg_eq ▸ hQ
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h
      exact ⟨Q.toExtension, hQformal, hQsection.mp h⟩
    · rintro ⟨P, hP, hsection⟩
      let _ : Algebra.FormallySmooth R P.Ring := hP
      exact (formallySmooth_iff_extension_section P).mpr hsection
  tfae_have 1 ↔ 3 := by
    constructor
    · intro h P hP
      let _ : Algebra.FormallySmooth R P.Ring := hP
      exact (formallySmooth_iff_extension_section P).mp h
    · intro h
      exact hQsection.mpr (h Q.toExtension hQformal)
  tfae_have 1 ↔ 4 := by
    constructor
    · intro h
      exact ⟨Q.toExtension, hQformal, hQsplit.mp h⟩
    · rintro ⟨P, hP, hsplit⟩
      let _ : Algebra.FormallySmooth R P.Ring := hP
      exact (formallySmooth_iff_extension_split_exact P).mpr hsplit
  tfae_have 1 ↔ 5 := by
    constructor
    · intro h P hP
      let _ : Algebra.FormallySmooth R P.Ring := hP
      exact (formallySmooth_iff_extension_split_exact P).mp h
    · intro h
      exact hQsplit.mpr (h Q.toExtension hQformal)
  tfae_have 1 ↔ 6 := formallySmooth_iff_cotangent_criterion
  tfae_finish

/-! ## Differential sequences -/

theorem ses_formallySmooth
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hBC : Algebra.FormallySmooth B C) :
    IsSplitExactLinearSequence
      (KaehlerDifferential.mapBaseChange A B C)
      (KaehlerDifferential.map A B C C) := by
  let _ : Algebra.FormallySmooth B C := hBC
  have hExact : Function.Exact
      (KaehlerDifferential.mapBaseChange A B C)
      (KaehlerDifferential.map A B C C) :=
    Formalization.Books.Algebra.Unit131.exact_sequence_of_differentials
      (A := A) (B := B) (C := C)
  have hSurj : Function.Surjective (KaehlerDifferential.map A B C C) :=
    Formalization.Books.Algebra.Unit131.exact_sequence_of_differentials_surjective
      (A := A) (B := B) (C := C)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (KaehlerDifferential.map A B C C) (LinearMap.id)
    hSurj
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange A B C) := by
    intro x y hxy
    have hzero : KaehlerDifferential.mapBaseChange A B C (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ :=
      (Algebra.H1Cotangent.exact_δ_mapBaseChange A B C (x - y)).mp hzero
    have hz' : z = 0 := Subsingleton.elim _ _
    have hxy' : x - y = 0 := by
      rw [← hz, hz', map_zero]
    exact sub_eq_zero.mp hxy'
  exact ⟨hinj, hExact, hSurj, ⟨s, hs⟩⟩

theorem differential_seq_formallySmooth
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Algebra.FormallySmooth A C)
    (hBC : Function.Surjective (algebraMap B C)) :
    extensionDifferentialSplitExact (surjectiveExtensionOver (A := A) hBC) := by
  let _ : Algebra.FormallySmooth A C := hAC
  let P := surjectiveExtensionOver (A := A) hBC
  change IsSplitExactLinearSequence P.cotangentComplex P.toKaehler
  have hPsub : Subsingleton P.H1Cotangent := by
    constructor
    intro x y
    obtain ⟨x', rfl⟩ := Algebra.Extension.H1Cotangent.map_defaultHom_surjective P x
    obtain ⟨y', rfl⟩ := Algebra.Extension.H1Cotangent.map_defaultHom_surjective P y
    exact congrArg _ (@Subsingleton.elim _ hAC.subsingleton_h1Cotangent x' y')
  have hinj : Function.Injective P.cotangentComplex :=
    P.subsingleton_h1Cotangent.mp hPsub
  have hExact : Function.Exact P.cotangentComplex P.toKaehler :=
    P.exact_cotangentComplex_toKaehler
  have hSurj : Function.Surjective P.toKaehler := P.toKaehler_surjective
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.toKaehler LinearMap.id hSurj
  exact ⟨hinj, hExact, hSurj, ⟨s, hs⟩⟩

theorem surjective_of_composite_algebraMap
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C)) :
    Function.Surjective (algebraMap B C) := by
  intro c
  obtain ⟨a, ha⟩ := hAC c
  refine ⟨algebraMap A B a, ?_⟩
  rw [← IsScalarTower.algebraMap_apply A B C a]
  exact ha

private theorem cotangent_map_injective_of_formallySmooth
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hAB : Algebra.FormallySmooth A B)
    (hBC : Function.Surjective (algebraMap B C)) :
    Function.Injective
      (Algebra.Extension.Cotangent.map
        (Formalization.Books.Algebra.Unit134.surjectiveExtensionHom hAC hBC)) := by
  let _ : Algebra.FormallySmooth A B := hAB
  let fAC : A →ₐ[A] C := IsScalarTower.toAlgHom A A C
  let q := fAC.kerSquareLift
  have hfAC : Function.Surjective fAC := by
    simpa [fAC] using hAC
  have hq : Function.Surjective q :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hfAC
  have hqnil : IsNilpotent (RingHom.ker q.toRingHom) := by
    refine ⟨2, ?_⟩
    rw [AlgHom.ker_kerSquareLift]
    exact Ideal.cotangentIdeal_square _
  let σ : B →ₐ[A] A ⧸ (RingHom.ker fAC.toRingHom) ^ 2 :=
    Algebra.FormallySmooth.liftOfSurjective
      (IsScalarTower.toAlgHom A B C) q hq hqnil
  have hσ : q.comp σ = IsScalarTower.toAlgHom A B C :=
    Algebra.FormallySmooth.comp_liftOfSurjective
      (IsScalarTower.toAlgHom A B C) q hq hqnil
  have hmapf (a : A) :
      (Formalization.Books.Algebra.Unit134.surjectiveExtensionHom hAC hBC).toAlgHom a =
        algebraMap A B a := by
    change (Formalization.Books.Algebra.Unit134.surjectiveExtensionHom hAC hBC).toRingHom a = _
    simpa [Formalization.Books.Algebra.Unit134.surjectiveExtension] using
      (Formalization.Books.Algebra.Unit134.surjectiveExtensionHom hAC hBC).toRingHom_algebraMap a
  intro x y hxy
  obtain ⟨x, rfl⟩ :=
    Algebra.Extension.Cotangent.mk_surjective (P :=
      Formalization.Books.Algebra.Unit134.surjectiveExtension hAC) x
  obtain ⟨y, rfl⟩ :=
    Algebra.Extension.Cotangent.mk_surjective (P :=
      Formalization.Books.Algebra.Unit134.surjectiveExtension hAC) y
  have hprod :
      algebraMap A B (x - y) ∈ (RingHom.ker (algebraMap B C)) ^ 2 := by
    have hmk := hxy
    simp only at hmk
    have hmem := (Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem _ _).mp hmk
    change
      (Formalization.Books.Algebra.Unit134.surjectiveExtensionHom hAC hBC).toAlgHom
          (x : A) -
        (Formalization.Books.Algebra.Unit134.surjectiveExtensionHom hAC hBC).toAlgHom
          (y : A) ∈
          (Formalization.Books.Algebra.Unit134.surjectiveExtension hBC).ker ^ 2 at hmem
    rw [hmapf, hmapf] at hmem
    simpa using hmem
  have hker : ∀ (z : B), z ∈ RingHom.ker (algebraMap B C) →
      σ z ∈ RingHom.ker q.toRingHom := by
    intro z hz
    change q (σ z) = 0
    rw [show q (σ z) = (IsScalarTower.toAlgHom A B C) z from
      DFunLike.congr_fun hσ z]
    exact RingHom.mem_ker.mp hz
  have hmap :
      Ideal.map σ.toRingHom (RingHom.ker (algebraMap B C)) ≤
        RingHom.ker q.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    exact hker
  have hprod' :
      σ (algebraMap A B (x - y)) ∈ (RingHom.ker q.toRingHom) ^ 2 := by
    have hmap_pow :
        Ideal.map σ.toRingHom (RingHom.ker (algebraMap B C) ^ 2) ≤
          (RingHom.ker q.toRingHom) ^ 2 := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hmap 2
    exact hmap_pow (Ideal.mem_map_of_mem σ.toRingHom hprod)
  have hqzero : (RingHom.ker q.toRingHom) ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift]
    exact Ideal.cotangentIdeal_square _
  have hzero : σ (algebraMap A B (x - y)) = 0 := by
    rw [← Ideal.mem_bot, ← hqzero]
    exact hprod'
  have hzero' :
      algebraMap A (A ⧸ (RingHom.ker fAC.toRingHom) ^ 2) (x - y) = 0 := by
    rw [← σ.commutes]
    exact hzero
  rw [Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem]
  have hmemI : (x - y : A) ∈ (RingHom.ker fAC.toRingHom) ^ 2 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← Ideal.Quotient.algebraMap_eq]
    exact hzero'
  simpa [fAC, Formalization.Books.Algebra.Unit134.surjectiveExtension] using hmemI

private theorem cotangent_map_injective_of_formallySmooth_over
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hAB : Algebra.FormallySmooth A B)
    (hBC : Function.Surjective (algebraMap B C)) :
    Function.Injective
      (Algebra.Extension.Cotangent.map (surjectiveExtensionOverHom hAC hBC)) := by
  let P := surjectiveExtensionOver (A := A) hBC
  let f := surjectiveExtensionOverHom hAC hBC
  change Function.Injective (Algebra.Extension.Cotangent.map f)
  let _ : Algebra.FormallySmooth A P.Ring := hAB
  let fAC : A →ₐ[A] C := IsScalarTower.toAlgHom A A C
  let q := fAC.kerSquareLift
  have hfAC : Function.Surjective fAC := by
    simpa [fAC] using hAC
  have hq : Function.Surjective q :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hfAC
  have hqnil : IsNilpotent (RingHom.ker q.toRingHom) := by
    refine ⟨2, ?_⟩
    rw [AlgHom.ker_kerSquareLift]
    exact Ideal.cotangentIdeal_square _
  let σ : P.Ring →ₐ[A] A ⧸ (RingHom.ker fAC.toRingHom) ^ 2 :=
    Algebra.FormallySmooth.liftOfSurjective
      (IsScalarTower.toAlgHom A P.Ring C) q hq hqnil
  have hσ : q.comp σ = IsScalarTower.toAlgHom A P.Ring C :=
    Algebra.FormallySmooth.comp_liftOfSurjective
      (IsScalarTower.toAlgHom A P.Ring C) q hq hqnil
  have hmapf (a : A) :
      f.toAlgHom a = algebraMap A P.Ring a := by
    rfl
  intro x y hxy
  obtain ⟨x, rfl⟩ :=
    Algebra.Extension.Cotangent.mk_surjective (P :=
      Formalization.Books.Algebra.Unit134.surjectiveExtension hAC) x
  obtain ⟨y, rfl⟩ :=
    Algebra.Extension.Cotangent.mk_surjective (P :=
      Formalization.Books.Algebra.Unit134.surjectiveExtension hAC) y
  have hprod :
      algebraMap A P.Ring (x - y) ∈ P.ker ^ 2 := by
    have hmk := hxy
    simp only at hmk
    have hmem := (Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem _ _).mp hmk
    change
      f.toAlgHom (x : A) - f.toAlgHom (y : A) ∈ P.ker ^ 2 at hmem
    rw [hmapf, hmapf] at hmem
    simpa only [map_sub] using hmem
  have hker : ∀ (z : P.Ring), z ∈ P.ker →
      σ z ∈ RingHom.ker q.toRingHom := by
    intro z hz
    change q (σ z) = 0
    rw [show q (σ z) = (IsScalarTower.toAlgHom A P.Ring C) z from
      DFunLike.congr_fun hσ z]
    change (algebraMap P.Ring C) z = 0
    exact RingHom.mem_ker.mp hz
  have hmap :
      Ideal.map σ.toRingHom P.ker ≤
        RingHom.ker q.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    exact hker
  have hprod' :
      σ (algebraMap A P.Ring (x - y)) ∈ (RingHom.ker q.toRingHom) ^ 2 := by
    have hmap_pow :
        Ideal.map σ.toRingHom (P.ker ^ 2) ≤
          (RingHom.ker q.toRingHom) ^ 2 := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hmap 2
    exact hmap_pow (Ideal.mem_map_of_mem σ.toRingHom hprod)
  have hqzero : (RingHom.ker q.toRingHom) ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift]
    exact Ideal.cotangentIdeal_square _
  have hzero : σ (algebraMap A P.Ring (x - y)) = 0 := by
    rw [← Ideal.mem_bot, ← hqzero]
    exact hprod'
  have hzero' :
      algebraMap A (A ⧸ (RingHom.ker fAC.toRingHom) ^ 2) (x - y) = 0 := by
    rw [← σ.commutes]
    exact hzero
  rw [Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem]
  have hmemI : (x - y : A) ∈ (RingHom.ker fAC.toRingHom) ^ 2 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← Ideal.Quotient.algebraMap_eq]
    exact hzero'
  simpa [fAC, Formalization.Books.Algebra.Unit134.surjectiveExtension] using hmemI

/-- The source's application lemma with its canonical differential map. -/
theorem application_NL_formallySmooth_canonical
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hAB : Algebra.FormallySmooth A B) :
    IsSplitExactLinearSequence
      (Algebra.Extension.Cotangent.map
        (surjectiveExtensionOverHom hAC
          (surjective_of_composite_algebraMap (B := B) hAC)))
      (surjectiveExtensionOver (A := A)
        (surjective_of_composite_algebraMap (B := B) hAC)).cotangentComplex := by
  let hBC := surjective_of_composite_algebraMap (B := B) hAC
  let _ : Algebra.FormallySmooth A B := hAB
  let E := Formalization.Books.Algebra.Unit134.surjectiveExtension hAC
  let P := surjectiveExtensionOver (A := A) hBC
  let f := surjectiveExtensionOverHom hAC hBC
  change IsSplitExactLinearSequence (Algebra.Extension.Cotangent.map f) P.cotangentComplex
  let ERT := E.h1CotangentEquivCotangent
  let EST := P.h1CotangentEquivCotangent
  have hmapid :
      Algebra.H1Cotangent.map A A C C = LinearMap.id := by
    change Algebra.Extension.H1Cotangent.map
      ((Algebra.Generators.self A C).defaultHom
        (Algebra.Generators.self A C)).toExtensionHom = _
    rw [Algebra.Extension.H1Cotangent.map_eq]
    exact Algebra.Extension.H1Cotangent.map_id
  have hEeq :
      ERT =
        E.h1Cotangentι ∘ₗ
          Algebra.Extension.H1Cotangent.map E.defaultHom := by
    have h := E.h1CotangentEquivCotangent_comp_map
    simpa only [ERT, E, hmapid, LinearMap.comp_id] using h
  have hPeq := P.h1CotangentEquivCotangent_comp_map
  have hcomp :
      Algebra.Extension.Cotangent.map f ∘ₗ ERT.toLinearMap =
        EST.toLinearMap ∘ₗ (Algebra.H1Cotangent.map A P.Ring C C) := by
    rw [hEeq, hPeq]
    rw [← LinearMap.comp_assoc, Algebra.Extension.Cotangent.map_comp_h1Cotangentι]
    rw [LinearMap.comp_assoc]
    ext x
    simp only [LinearMap.comp_apply]
    rw [← Algebra.Extension.H1Cotangent.map_comp_apply E.defaultHom f]
    have hmapeq := Algebra.Extension.H1Cotangent.map_eq
      (f.comp E.defaultHom)
      P.defaultHom
    exact congrArg (fun z => Algebra.Extension.h1Cotangentι z)
      (DFunLike.congr_fun hmapeq x)
  have hPcomp :
      P.cotangentComplex.comp EST.toLinearMap =
        Algebra.H1Cotangent.δ A P.Ring C :=
    P.cotangentComplex_comp_h1CotangentEquivCotangent
  have hd_eq :
      (Algebra.H1Cotangent.δ A P.Ring C).comp EST.symm.toLinearMap =
        P.cotangentComplex := by
    rw [← hPcomp, LinearMap.comp_assoc]
    simp
  have hcanon :
      Function.Exact
        (EST.toLinearMap.comp (Algebra.H1Cotangent.map A P.Ring C C))
        ((Algebra.H1Cotangent.δ A P.Ring C).comp EST.symm.toLinearMap) :=
    (LinearEquiv.conj_exact_iff_exact
      (Algebra.H1Cotangent.map A P.Ring C C)
      (Algebra.H1Cotangent.δ A P.Ring C) EST).2
      (Algebra.H1Cotangent.exact_map_δ A P.Ring C)
  have htarget :
      Function.Exact
        ((Algebra.Extension.Cotangent.map f).comp ERT.toLinearMap)
        P.cotangentComplex := by
    rw [hcomp, ← hd_eq]
    exact hcanon
  have hexact :
      Function.Exact (Algebra.Extension.Cotangent.map f) P.cotangentComplex := by
    intro z
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := (htarget z).mp hz
      exact ⟨ERT x, by simpa [LinearMap.comp_apply] using hx⟩
    · rintro ⟨x, hx⟩
      apply (htarget z).mpr
      refine ⟨ERT.symm x, ?_⟩
      simpa [LinearMap.comp_apply] using hx
  let _ : Subsingleton (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials A C) :=
    Formalization.Books.Algebra.Unit131.moduleOfDifferentials_subsingleton_of_surjective
      hAC
  have hsurj : Function.Surjective P.cotangentComplex := by
    intro z
    have hz : P.toKaehler z = 0 := Subsingleton.elim _ _
    exact (P.exact_cotangentComplex_toKaehler z).mp hz
  have hinj : Function.Injective (Algebra.Extension.Cotangent.map f) := by
    exact cotangent_map_injective_of_formallySmooth_over hAC hAB hBC
  let _ : Algebra.FormallySmooth A P.Ring := hAB
  let _ : Module.Projective C P.CotangentSpace := by
    infer_instance
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.cotangentComplex LinearMap.id hsurj
  exact ⟨hinj, hexact, hsurj, ⟨s, hs⟩⟩

/-- Compatibility form of `application_NL_formallySmooth_canonical` retained
for clients which supplied the differential map as an existential. -/
theorem application_NL_formallySmooth
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C))
    (hAB : Algebra.FormallySmooth A B) :
    ∃ d :
        (Formalization.Books.Algebra.Unit134.surjectiveExtension
            (surjective_of_composite_algebraMap (B := B) hAC)).Cotangent →ₗ[C]
          C ⊗[B] Formalization.Books.Algebra.Unit131.ModuleOfDifferentials A B,
      IsSplitExactLinearSequence
        (Algebra.Extension.Cotangent.map
          (Formalization.Books.Algebra.Unit134.surjectiveExtensionHom hAC
            (surjective_of_composite_algebraMap (B := B) hAC))) d := by
  let hBC := surjective_of_composite_algebraMap (B := B) hAC
  let _ : Algebra.FormallySmooth A B := hAB
  obtain ⟨d, hd, hdsurj⟩ :=
    Formalization.Books.Algebra.Unit134.conormal_exact_for_two_surjections hAC hBC
  refine ⟨d,
    cotangent_map_injective_of_formallySmooth hAC hAB hBC,
    hd, hdsurj, ?_⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property d LinearMap.id hdsurj
  exact ⟨s, hs⟩

/-! ## Square-zero lifting and smoothness -/

private theorem isNilpotent_ideal_span_finset
    {R : Type*} [CommRing R] (s : Finset R)
    (hs : ∀ x ∈ s, IsNilpotent x) :
    IsNilpotent (Ideal.span (s : Set R)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_⟩
      simp
  | @insert a s ha ih =>
      obtain ⟨n, hn⟩ := hs a (Finset.mem_insert_self a s)
      obtain ⟨m, hm⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
      have ha_span : (Ideal.span ({a} : Set R)) ^ n = ⊥ := by
        rw [Ideal.span_singleton_pow, hn]
        simp
      refine ⟨n + m, le_antisymm ?_ bot_le⟩
      rw [Finset.coe_insert, Ideal.span_insert]
      exact (Ideal.sup_pow_add_le_pow_sup_pow.trans (by rw [ha_span, hm]; simp))

theorem formallySmooth_of_squareZero_flat
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hflat : f.Flat)
    (hquot : (quotientBaseChangeRingMap f I).FormallySmooth) :
    f.FormallySmooth := by
  let qR : R →+* R ⧸ I := Ideal.Quotient.mk I
  let qS : S →+* S ⧸ Ideal.map f I := Ideal.Quotient.mk _
  let g := quotientBaseChangeRingMap f I
  have hkerqR : RingHom.ker qR = I := by
    simp [qR]
  apply RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero f hflat qR qS g
  · exact Ideal.Quotient.mk_surjective
  · exact Ideal.Quotient.mk_surjective
  · symm
    simpa [qR, qS, g, quotientBaseChangeRingMap] using
      (Ideal.quotientMap_comp_mk (f := f) (H := Ideal.le_comap_map))
  · rw [hkerqR]
    exact hI
  · rw [hkerqR]
    simp [qS]
  · exact hquot

theorem smooth_iff_formallySmooth_and_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    f.Smooth ↔ f.FormallySmooth ∧ f.FinitePresentation :=
  RingHom.smooth_def

theorem smooth_finite_type_descent
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.Smooth) :
    letI : Algebra R S := f.toAlgebra
    ∃ (R₀ : Type u) (S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
      (_ : Algebra ℤ R₀) (_ : Algebra R₀ R) (_ : Algebra R₀ S₀),
      Function.Injective (algebraMap R₀ R) ∧
        Algebra.FiniteType ℤ R₀ ∧ Algebra.Smooth R₀ S₀ ∧
          Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀) := by
  exact
    letI : Algebra R S := f.toAlgebra
    letI : Algebra.Smooth R S := hf.toAlgebra
    Algebra.Smooth.exists_finiteType ℤ R S

/-
Prior attempt (rejected interface):

theorem smooth_descends_through_colimit
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (D : Formalization.Books.Algebra.Unit127.DirectedFinitePresentationApproximation f)
    (hf : f.Smooth) :
    ∃ i : D.base.colimit.index,
      (D.base.colimit.stageMap i).Smooth ∧
        Nonempty (directedStageBaseChangeRing D.base.colimit i ≃+* B) := by
  sorry

The Chapter 127 approximation records finite-type stages and bijective
transition base changes, but it does not record the stage-to-target data
needed for this conclusion for an arbitrary approximation.  The
source-faithful smooth finite-type model is recorded by
`smooth_finite_type_descent` above instead.
-/

theorem formallySmooth_iff_faithfullyFlat_baseChange
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hff : g.FaithfullyFlat) :
    f.FormallySmooth ↔
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).FormallySmooth := by
  constructor
  · exact formallySmooth_baseChange f g
  · /-
    This is precisely the missing fpqc descent theorem
    `Algebra.FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat`
    in Mathlib's `RingTheory/Etale/Descent.lean` (currently marked
    `proof_wanted`).  A source-faithful proof uses
    `formallySmooth_iff_cotangent_criterion`: flat base change for
    `H1Cotangent` is already in `Extension/Cotangent/BaseChange`, projectivity
    descends along faithfully flat maps, and faithful tensoring reflects a
    subsingleton module.  Those three generic results should close this
    branch without another presentation calculation here.
    -/
    sorry

theorem smooth_strong_lift
    {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R A] (f : R →+* S) (hf : f.Smooth) :
    letI : Algebra R S := f.toAlgebra
    ∀ (I : Ideal A),
      Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I →
        ∀ (g : S →ₐ[R] A ⧸ I),
          ∃ lift : S →ₐ[R] A,
            (Ideal.Quotient.mkₐ R I).comp lift = g := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra.FormallySmooth R S := hf.formallySmooth.toAlgebra
  let _ : Algebra.FinitePresentation R S := hf.finitePresentation
  intro I hI g
  classical
  let P := Algebra.Presentation.ofFinitePresentation R S
  let pMap : P.Ring →ₐ[R] S := IsScalarTower.toAlgHom R P.Ring S
  let a : (Fin (Algebra.Presentation.ofFinitePresentationVars R S)) → A :=
    fun i => (Ideal.Quotient.mk_surjective (g (P.val i))).choose
  have ha (i : Fin (Algebra.Presentation.ofFinitePresentationVars R S)) :
      Ideal.Quotient.mk I (a i) = g (P.val i) :=
    (Ideal.Quotient.mk_surjective (g (P.val i))).choose_spec
  let evalA : P.Ring →ₐ[R] A := MvPolynomial.aeval a
  let rel : Finset A := Finset.univ.image (fun j => evalA (P.relation j))
  let J : Ideal A := Ideal.span (rel : Set A)
  have heval :
      (Ideal.Quotient.mkₐ R I).comp evalA = g.comp pMap := by
    apply MvPolynomial.algHom_ext
    intro i
    change Ideal.Quotient.mk I (evalA (.X i)) = g (pMap (.X i))
    simpa [evalA, a, pMap] using ha i
  have hrelI (j : Fin (Algebra.Presentation.ofFinitePresentationRels R S)) :
      evalA (P.relation j) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := congrArg
      (fun k : P.Ring →ₐ[R] A ⧸ I => k (P.relation j)) heval
    simpa [AlgHom.comp_apply, pMap, P.aeval_val_relation] using h
  have hrelJ (j : Fin (Algebra.Presentation.ofFinitePresentationRels R S)) :
      evalA (P.relation j) ∈ J := by
    apply Ideal.subset_span
    change evalA (P.relation j) ∈ rel
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hJle : J ≤ I := by
    apply Ideal.span_le.2
    intro x hx
    change x ∈ rel at hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact hrelI j
  have hJnil : IsNilpotent J := by
    apply isNilpotent_ideal_span_finset rel
    intro x hx
    change x ∈ rel at hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact hI _ (hrelI j)
  let qJ : A →ₐ[R] A ⧸ J := Ideal.Quotient.mkₐ R J
  let evalQ : P.Ring →ₐ[R] A ⧸ J := qJ.comp evalA
  have hker : P.ker ≤ RingHom.ker evalQ.toRingHom := by
    rw [← P.span_range_relation_eq_ker]
    apply Ideal.span_le.2
    intro x hx
    obtain ⟨j, rfl⟩ := Set.mem_range.mp hx
    change evalQ (P.relation j) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hrelJ j)
  let pLift := AlgHom.liftOfSurjective pMap P.algebraMap_surjective evalQ hker
  let gJ := pLift
  let qJI : A ⧸ J →ₐ[R] A ⧸ I := Ideal.Quotient.factorₐ R hJle
  have hqJI : qJI.comp qJ = Ideal.Quotient.mkₐ R I := by
    exact Ideal.Quotient.factorₐ_comp_mk R hJle
  have hpLift : pLift.comp pMap = evalQ := by
    apply AlgHom.ext
    intro x
    simpa [pLift, AlgHom.comp_apply] using
      (AlgHom.liftOfSurjective_apply pMap P.algebraMap_surjective evalQ hker x)
  have hgJ : qJI.comp gJ = g := by
    have hpMap : Function.Surjective pMap := by
      simpa [pMap] using P.algebraMap_surjective
    rw [← AlgHom.cancel_right hpMap]
    calc
      (qJI.comp pLift).comp pMap = qJI.comp (pLift.comp pMap) := by
        simp only [AlgHom.comp_assoc]
      _ = qJI.comp evalQ := by rw [hpLift]
      _ = (qJI.comp qJ).comp evalA := by
        simp only [evalQ, AlgHom.comp_assoc]
      _ = (Ideal.Quotient.mkₐ R I).comp evalA := by rw [hqJI]
      _ = g.comp pMap := heval
  obtain ⟨lift, hlift⟩ := Algebra.FormallySmooth.exists_lift J hJnil gJ
  refine ⟨lift, ?_⟩
  rw [← hgJ, ← hqJI]
  simpa only [AlgHom.comp_assoc] using
    congrArg (fun k : S →ₐ[R] A ⧸ J => qJI.comp k) hlift

end

end Formalization.Books.Algebra.Unit138
