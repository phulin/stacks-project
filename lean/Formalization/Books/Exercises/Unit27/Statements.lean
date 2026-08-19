import Formalization.Books.Exercises.Unit27.Core
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Exercises, Chapter 27: statements

This file records the source-facing assertions in their chapter order.  The
canonical Mathlib constructions and the small interfaces needed for the
blowup examples live in `Core.lean`.
-/

noncomputable section

universe u v

open CategoryTheory
open TopologicalSpace
open _root_.Topology
open AlgebraicGeometry

namespace Formalization.Books.Exercises.Unit27

variable {R : Type u} [CommRing R]

/-! ## 27.1. Homogeneous ideals -/

theorem homogeneousIdeal_iff_homogeneous_generators
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (I : Ideal R) :
    IsHomogeneousIdeal 𝒜 I ↔
      ∃ S : Set (SetLike.homogeneousSubmonoid 𝒜),
        I = Ideal.span ((↑) '' S) := by sorry
theorem homogeneousIdeal_iff_components
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (I : Ideal R) :
    IsHomogeneousIdeal 𝒜 I ↔
      ∀ r, r ∈ I → ∀ n, GradedRing.proj 𝒜 n r ∈ I := by sorry
theorem homogeneousIdeal_components_mem_iff
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {I : Ideal R} (hI : IsHomogeneousIdeal 𝒜 I) (r : R) :
    r ∈ I ↔ ∀ n, GradedRing.proj 𝒜 n r ∈ I := by sorry
theorem projToPrimeSpectrum_injective
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    Function.Injective (projToPrimeSpectrum 𝒜) := by sorry
theorem projToPrimeSpectrum_inducing
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    IsInducing (projToPrimeSpectrum 𝒜) := by sorry
theorem projToPrimeSpectrum_isEmbedding
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    IsEmbedding (projToPrimeSpectrum 𝒜) := by sorry
theorem mem_dPlus_iff
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (f : R) (x : ProjPoints 𝒜) :
    x ∈ dPlus 𝒜 f ↔ f ∉ x.asHomogeneousIdeal := by sorry
theorem mem_vPlus_iff
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (I : HomogeneousIdeal 𝒜) (x : ProjPoints 𝒜) :
    x ∈ vPlus 𝒜 I ↔ (I : Set R) ⊆ x.asHomogeneousIdeal := by sorry
theorem isOpen_dPlus
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (f : R) :
    IsOpen (dPlus 𝒜 f) := by sorry
theorem isOpen_dPlus_of_positive_homogeneous
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {m : ℕ} {f : R} (_hf : f ∈ 𝒜 m) (_hm : 0 < m) :
    IsOpen (dPlus 𝒜 f) := by sorry
theorem dPlus_mul
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (f f' : R) :
    dPlus 𝒜 (f * f') = dPlus 𝒜 f ∩ dPlus 𝒜 f' := by sorry
theorem dOnProj_eq_iUnion_projections
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (g : R) :
    dOnProj 𝒜 g =
      ⋃ n : ℕ, dPlus 𝒜 (GradedRing.proj 𝒜 n g) := by sorry
theorem dOnProj_eq_zero_component_union_positive
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] (g : R) :
    dOnProj 𝒜 g =
      dOnProj 𝒜 (GradedRing.proj 𝒜 0 g) ∪
        ⋃ n : {n : ℕ // 0 < n},
          dPlus 𝒜 (GradedRing.proj 𝒜 n.1 g) := by sorry
theorem dOnProj_degree_zero_eq_iUnion_mul
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {g : R} (_hg : g ∈ 𝒜 0) {ι : Type v} (f : ι → R)
    (_hf : ∀ i, ∃ n : ℕ, 0 < n ∧ f i ∈ 𝒜 n)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range f)) :
    dOnProj 𝒜 g = ⋃ i, dPlus 𝒜 (g * f i) := by sorry
theorem dPlus_isTopologicalBasis
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    IsTopologicalBasis
      {U : Set (ProjPoints 𝒜) |
        ∃ (n : ℕ) (_hn : 0 < n) (f : R), f ∈ 𝒜 n ∧ U = dPlus 𝒜 f} := by sorry
noncomputable def dPlusHomeomorph
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {m : ℕ} {f : R} (_hf : f ∈ 𝒜 m) (_hm : 0 < m) :
    {x : ProjPoints 𝒜 // x ∈ dPlus 𝒜 f} ≃ₜ
      PrimeSpectrum (degreeZeroLocalization 𝒜 f) :=
  TopCat.homeoOfIso
    (AlgebraicGeometry.projIsoSpecTopComponent _hf _hm)

theorem dPlus_chart_bijective
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    {m : ℕ} {f : R} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    Function.Bijective (dPlusHomeomorph 𝒜 hf hm) := by sorry
abbrev InfinitePolynomialGrading (k : Type u) [CommRing k] :
    ℕ → Submodule k (MvPolynomial ℕ k) :=
  MvPolynomial.homogeneousSubmodule ℕ k

noncomputable def infinitePolynomialProj (k : Type u) [CommRing k] : Type u :=
  letI : GradedAlgebra (InfinitePolynomialGrading k) := MvPolynomial.gradedAlgebra
  ProjectiveSpectrum (InfinitePolynomialGrading k)

theorem infinitePolynomialProj_not_quasiCompact (k : Type u) [Field k] :
    letI : GradedAlgebra (InfinitePolynomialGrading k) := MvPolynomial.gradedAlgebra
    ¬ CompactSpace (ProjectiveSpectrum (InfinitePolynomialGrading k)) := by sorry
theorem exists_homogeneousIdeal_eq_vPlus
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (T : Set (ProjPoints 𝒜)) (hT : IsClosed T) :
    ∃ I : HomogeneousIdeal 𝒜, T = vPlus 𝒜 I := by sorry
noncomputable def projToSpecZeroPointMap
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    ProjPoints 𝒜 → PrimeSpectrum (𝒜 0) :=
  (projToSpecZeroScheme 𝒜).base

theorem projToSpecZeroPointMap_continuous
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] :
    Continuous (projToSpecZeroPointMap 𝒜) := by sorry
abbrev oneVariablePolynomialRing (A : Type u) [CommRing A] :=
  MvPolynomial (Fin 1) A

noncomputable def oneVariablePolynomialEquiv (A : Type u) [CommRing A] :
    oneVariablePolynomialRing A ≃ₐ[A] Polynomial A :=
  MvPolynomial.uniqueAlgEquiv A (Fin 1)

abbrev oneVariablePolynomialGrading (A : Type u) [CommRing A] :
    ℕ → Submodule A (oneVariablePolynomialRing A) :=
  MvPolynomial.homogeneousSubmodule (Fin 1) A

theorem oneVariableDegreeZeroEquiv_exists (A : Type u) [CommRing A] :
    Nonempty {
      e : (oneVariablePolynomialGrading A 0) ≃+* A //
        ∀ a : A,
          ((e.symm a : oneVariablePolynomialGrading A 0) :
              oneVariablePolynomialRing A) = MvPolynomial.C a } := by sorry
noncomputable def oneVariableDegreeZeroEquivData (A : Type u) [CommRing A] :
    {e : (oneVariablePolynomialGrading A 0) ≃+* A //
      ∀ a : A,
        ((e.symm a : oneVariablePolynomialGrading A 0) :
            oneVariablePolynomialRing A) = MvPolynomial.C a} :=
  Classical.choice (oneVariableDegreeZeroEquiv_exists A)

noncomputable def oneVariableDegreeZeroEquiv (A : Type u) [CommRing A] :
    (oneVariablePolynomialGrading A 0) ≃+* A :=
  (oneVariableDegreeZeroEquivData A).1

theorem oneVariableDegreeZeroEquiv_spec (A : Type u) [CommRing A] (a : A) :
    (((oneVariableDegreeZeroEquiv A).symm a : oneVariablePolynomialGrading A 0) :
        oneVariablePolynomialRing A) =
      MvPolynomial.C a := by sorry
noncomputable def oneVariableProjScheme (A : Type u) [CommRing A] : Scheme :=
  letI : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
  AlgebraicGeometry.«Proj» (oneVariablePolynomialGrading A)

noncomputable def oneVariableProjToSpec (A : Type u) [CommRing A] :
    oneVariableProjScheme A ⟶ Spec (CommRingCat.of A) :=
  letI : GradedAlgebra (oneVariablePolynomialGrading A) := MvPolynomial.gradedAlgebra
  AlgebraicGeometry.Proj.toSpecZero (oneVariablePolynomialGrading A) ≫
    Spec.map (CommRingCat.ofHom (oneVariableDegreeZeroEquiv A).symm.toRingHom)

theorem oneVariableProjToSpec_bijective (A : Type u) [CommRing A] :
    Function.Bijective (oneVariableProjToSpec A).base := by sorry
theorem oneVariableProjToSpec_isHomeomorph (A : Type u) [CommRing A] :
    IsHomeomorph (oneVariableProjToSpec A).base := by sorry
theorem blowupBaseOpen_isOpen {A : Type u} [CommRing A] (I : Ideal A) :
    IsOpen (blowupBaseOpen I) := by sorry
theorem blowupRestrictionMap_isHomeomorph
    {A : Type u} [CommRing A] {I : Ideal A}
    (P : BlowupPresentation I) :
    IsHomeomorph (blowupRestrictionMap P) := by sorry
theorem strictTransform_conditions
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} (D : StrictTransformData P) :
    D.genericPoint ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧
      ¬ (D.Z : Set (PrimeSpectrum A)) ⊆
        PrimeSpectrum.zeroLocus (I : Set A) ∧
      D.genericPoint ∈ blowupBaseOpen I ∧
      ((D.Z : Set (PrimeSpectrum A)) ∩ blowupBaseOpen I).Nonempty := by sorry
theorem strictTransform_eq_viaOpen
    {A : Type u} [CommRing A] {I : Ideal A}
    {P : BlowupPresentation I} (D : StrictTransformData P) :
    strictTransform D = strictTransformViaOpen D := by sorry
abbrev twoVariablePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

def twoVariableX (k : Type u) [Field k] : twoVariablePolynomialRing k :=
  MvPolynomial.X 0

def twoVariableY (k : Type u) [Field k] : twoVariablePolynomialRing k :=
  MvPolynomial.X 1

def twoVariableMaximalIdeal (k : Type u) [Field k] :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span {twoVariableX k, twoVariableY k}

def twoVariableXIdeal (k : Type u) [Field k] :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span {twoVariableX k}

def twoVariableYIdeal (k : Type u) [Field k] :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span {twoVariableY k}

def twoVariableParabolaIdeal (k : Type u) [Field k] :
    Ideal (twoVariablePolynomialRing k) :=
  Ideal.span {twoVariableX k - twoVariableY k ^ 2}

theorem twoVariableBlowupPresentation_exists (k : Type u) [Field k] :
    Nonempty (BlowupPresentation (twoVariableMaximalIdeal k)) := by sorry
noncomputable def twoVariableBlowupPresentation (k : Type u) [Field k] :
    BlowupPresentation (twoVariableMaximalIdeal k) :=
  Classical.choice (twoVariableBlowupPresentation_exists k)

theorem twoVariableXIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableXIdeal k).IsPrime := by sorry
theorem twoVariableYIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableYIdeal k).IsPrime := by sorry
theorem twoVariableParabolaIdeal_isPrime (k : Type u) [Field k] :
    (twoVariableParabolaIdeal k).IsPrime := by sorry
theorem twoVariableXStrictTransformData_exists (k : Type u) [Field k] :
    Nonempty (PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableXIdeal k) (twoVariableXIdeal_isPrime k)) := by sorry
theorem twoVariableYStrictTransformData_exists (k : Type u) [Field k] :
    Nonempty (PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableYIdeal k) (twoVariableYIdeal_isPrime k)) := by sorry
theorem twoVariableParabolaStrictTransformData_exists (k : Type u) [Field k] :
    Nonempty (PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableParabolaIdeal k) (twoVariableParabolaIdeal_isPrime k)) := by sorry
noncomputable def twoVariableXStrictTransformData (k : Type u) [Field k] :
    PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableXIdeal k) (twoVariableXIdeal_isPrime k) :=
  Classical.choice (twoVariableXStrictTransformData_exists k)

noncomputable def twoVariableYStrictTransformData (k : Type u) [Field k] :
    PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableYIdeal k) (twoVariableYIdeal_isPrime k) :=
  Classical.choice (twoVariableYStrictTransformData_exists k)

noncomputable def twoVariableParabolaStrictTransformData (k : Type u) [Field k] :
    PrimeStrictTransformData (twoVariableBlowupPresentation k)
      (twoVariableParabolaIdeal k) (twoVariableParabolaIdeal_isPrime k) :=
  Classical.choice (twoVariableParabolaStrictTransformData_exists k)

theorem twoVariable_x_y_strictTransforms_disjoint (k : Type u) [Field k] :
    Disjoint
      (primeStrictTransform (twoVariableXStrictTransformData k))
      (primeStrictTransform (twoVariableYStrictTransformData k)) := by sorry
theorem twoVariable_x_parabola_strictTransforms_not_disjoint
    (k : Type u) [Field k] :
    ¬ Disjoint
      (primeStrictTransform (twoVariableXStrictTransformData k))
      (primeStrictTransform (twoVariableParabolaStrictTransformData k)) := by sorry
theorem exists_twoVariable_separatingIdeal (k : Type u) [Field k] :
    ∃ J : Ideal (twoVariablePolynomialRing k),
      PrimeSpectrum.zeroLocus (J : Set (twoVariablePolynomialRing k)) =
        PrimeSpectrum.zeroLocus
          (twoVariableMaximalIdeal k : Set (twoVariablePolynomialRing k)) ∧
      ∃ P : BlowupPresentation J,
        ∃ dx : PrimeStrictTransformData P
          (twoVariableXIdeal k) (twoVariableXIdeal_isPrime k),
        ∃ dp : PrimeStrictTransformData P
          (twoVariableParabolaIdeal k) (twoVariableParabolaIdeal_isPrime k),
          Disjoint (primeStrictTransform dx) (primeStrictTransform dp) := by sorry
theorem projPoints_isEmpty_of_eventually_zero
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    (hzero : ∀ᶠ n in Filter.atTop, 𝒜 n = ⊥) :
    IsEmpty (ProjPoints 𝒜) := by sorry
theorem projPoints_irreducibleSpace_of_domain
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜] [IsDomain R]
    (hplus : HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥) :
    IrreducibleSpace (ProjPoints 𝒜) := by sorry
theorem empty_projPoints_not_irreducible
    (𝒜 : ℕ → Submodule ℤ R) [GradedAlgebra 𝒜]
    [IsEmpty (ProjPoints 𝒜)] :
    ¬ IsIrreducible (Set.univ : Set (ProjPoints 𝒜)) := by sorry
abbrev blowupQuotientRing {A : Type u} [CommRing A] (p : Ideal A) := A ⧸ p

abbrev blowupQuotientIdeal {A : Type u} [CommRing A]
    (I p : Ideal A) : Ideal (blowupQuotientRing p) :=
  quotientIdeal I p

theorem exists_surjective_blowupQuotientRingHom
    {A : Type u} [CommRing A] {I p : Ideal A} :
    ∃ φ : blowupAlgebra I →+* blowupAlgebra (blowupQuotientIdeal I p),
      Function.Surjective φ := by sorry
theorem exists_blowupQuotientMapData
    {A : Type u} [CommRing A] {I p : Ideal A}
    (P : BlowupPresentation I)
    (Q : BlowupPresentation (blowupQuotientIdeal I p)) :
    Nonempty (BlowupQuotientMapData P Q) := by sorry
noncomputable def blowupQuotientMapData
    {A : Type u} [CommRing A] {I p : Ideal A}
    (P : BlowupPresentation I)
    (Q : BlowupPresentation (blowupQuotientIdeal I p)) :
    BlowupQuotientMapData P Q :=
  Classical.choice (exists_blowupQuotientMapData P Q)

theorem blowupQuotientMapData_surjective
    {A : Type u} [CommRing A] {I p : Ideal A}
    {P : BlowupPresentation I}
    {Q : BlowupPresentation (blowupQuotientIdeal I p)}
    (F : BlowupQuotientMapData P Q) :
    Function.Surjective F.map :=
  F.surjective

theorem blowupQuotientProjMap_image_strictTransform
    {A : Type u} [CommRing A] {I p : Ideal A}
    {P : BlowupPresentation I}
    {Q : BlowupPresentation (blowupQuotientIdeal I p)}
    {hp : p.IsPrime} (F : BlowupQuotientMapData P Q)
    (D : PrimeStrictTransformData P p hp) :
    Function.Injective (blowupQuotientProjMap F).base ∧
      Set.range (blowupQuotientProjMap F).base = primeStrictTransform D := by sorry
noncomputable def blowupStrictTransformComponentAsSet
    {A : Type u} [CommRing A] {I p : Ideal A}
    {P : BlowupPresentation I}
    {Q : BlowupPresentation (blowupQuotientIdeal I p)}
    (F : BlowupQuotientMapData P Q) (d : ℕ) :
    letI : GradedRing P.gradedPieces := P.graded
    letI : GradedRing Q.gradedPieces := Q.graded
    Set A :=
  letI : GradedRing P.gradedPieces := P.graded
  letI : GradedRing Q.gradedPieces := Q.graded
  {a | ∃ ha : a ∈ I ^ d,
    reesHomogeneousElement I d ha ∈
      (blowupStrictTransformIdeal F : Set (blowupAlgebra I))}

theorem blowupStrictTransformComponentAsSet_eq
    {A : Type u} [CommRing A] {I p : Ideal A}
    {P : BlowupPresentation I}
    {Q : BlowupPresentation (blowupQuotientIdeal I p)}
    (F : BlowupQuotientMapData P Q) (d : ℕ) :
    blowupStrictTransformComponentAsSet F d =
      ((I ^ d : Ideal A) : Set A) ∩ (p : Set A) := by sorry
theorem primeStrictTransform_eq_vPlus_of_blowupQuotient
    {A : Type u} [CommRing A] {I p : Ideal A}
    {P : BlowupPresentation I}
    {Q : BlowupPresentation (blowupQuotientIdeal I p)}
    {hp : p.IsPrime} (F : BlowupQuotientMapData P Q)
    (D : PrimeStrictTransformData P p hp) :
    letI : GradedRing P.gradedPieces := P.graded
    letI : GradedRing Q.gradedPieces := Q.graded
    primeStrictTransform D =
      vPlus P.gradedPieces (blowupStrictTransformIdeal F) := by sorry
theorem exists_separating_blowup_for_incomparable_primes
    {A : Type u} [CommRing A] {p q : Ideal A}
    (hp : p.IsPrime) (hq : q.IsPrime)
    (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p) :
    ∃ P : BlowupPresentation (p + q),
      ∃ Dp : PrimeStrictTransformData P p hp,
        ∃ Dq : PrimeStrictTransformData P q hq,
          Disjoint (primeStrictTransform Dp) (primeStrictTransform Dq) := by sorry
