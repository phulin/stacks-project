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
      letI : Algebra.FormallySmooth R P.Ring := hP
      exact (formallySmooth_iff_extension_section P).mpr hsection
  tfae_have 1 ↔ 3 := by
    constructor
    · intro h P hP
      letI : Algebra.FormallySmooth R P.Ring := hP
      exact (formallySmooth_iff_extension_section P).mp h
    · intro h
      exact hQsection.mpr (h Q.toExtension hQformal)
  tfae_have 1 ↔ 4 := by
    constructor
    · intro h
      exact ⟨Q.toExtension, hQformal, hQsplit.mp h⟩
    · rintro ⟨P, hP, hsplit⟩
      letI : Algebra.FormallySmooth R P.Ring := hP
      exact (formallySmooth_iff_extension_split_exact P).mpr hsplit
  tfae_have 1 ↔ 5 := by
    constructor
    · intro h P hP
      letI : Algebra.FormallySmooth R P.Ring := hP
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
  letI : Algebra.FormallySmooth B C := hBC
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
  sorry

theorem surjective_of_composite_algebraMap
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAC : Function.Surjective (algebraMap A C)) :
    Function.Surjective (algebraMap B C) := by
  sorry

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
  sorry

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
  sorry

/-! ## Square-zero lifting and smoothness -/

theorem formallySmooth_of_squareZero_flat
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hflat : f.Flat)
    (hquot : (quotientBaseChangeRingMap f I).FormallySmooth) :
    f.FormallySmooth := by
  sorry

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

theorem smooth_descends_through_colimit
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (D : Formalization.Books.Algebra.Unit127.DirectedRingMapColimit f)
    (hf : f.Smooth) :
    ∃ i : D.index,
      (D.stageMap i).Smooth ∧
        Nonempty (directedStageBaseChangeRing D i ≃+* B) := by
  sorry

theorem formallySmooth_iff_faithfullyFlat_baseChange
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hff : g.FaithfullyFlat) :
    f.FormallySmooth ↔
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).FormallySmooth := by
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
  sorry

end

end Formalization.Books.Algebra.Unit138
