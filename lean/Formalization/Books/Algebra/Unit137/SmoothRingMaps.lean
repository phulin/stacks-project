import Formalization.Books.Algebra.Unit136.SyntomicMorphisms
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.Pi
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Commutative Algebra, Chapter 137: Smooth ring maps

The canonical Mathlib classes `Algebra.Smooth` and
`Algebra.IsStandardSmooth` are used for the two notions in this chapter.
The source's presentation-independent cotangent complex is the one exposed
by Chapter 134, while the standard-smooth presentation and its Jacobian are
Mathlib's `SubmersivePresentation`.
-/

namespace Formalization.Books.Algebra.Unit137

open Set
open Module
open scoped BigOperators TensorProduct

noncomputable section

universe u v w

/-! ## The cotangent criterion for smoothness -/

/- The exact sequence in the hypersurface example is the specialization of
   `PresentationExtension.exact_cotangentComplex_toKaehler`; the displayed
   polynomial basis is already provided by `Presentation.cotangentSpaceBasis`.
   We record the presentation-level statement so the source's exact sequence
   has a named chapter-facing interface. -/
theorem presentation_exact_sequence
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι) :
    Function.Exact P.toExtension.cotangentComplex P.toExtension.toKaehler := by
  exact P.toExtension.exact_cotangentComplex_toKaehler

theorem presentation_differential_formula
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι)
    (x : P.toExtension.ker) :
    P.toExtension.cotangentComplex (Algebra.Extension.Cotangent.mk x) =
      1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x.1 := by
  exact P.toExtension.cotangentComplex_mk x

/- The source's rank-two computation and its failure of smoothness are kept as
   one warning theorem.  The free module is the canonical
   `ModuleOfDifferentials`; no parallel differential object is introduced. -/
abbrev Hypersurface (R : Type u) [CommRing R]
    (f : MvPolynomial (Fin 2) R) : Type u :=
  MvPolynomial (Fin 2) R ⧸
    Ideal.span ({f} : Set (MvPolynomial (Fin 2) R))

noncomputable def hypersurfacePartial
    {R : Type u} [CommRing R] {f : MvPolynomial (Fin 2) R}
    (i : Fin 2) : Hypersurface R f :=
  Ideal.Quotient.mk _ (MvPolynomial.pderiv i f)

theorem hypersurface_exact_sequence
    {R : Type u} [CommRing R] (f : MvPolynomial (Fin 2) R) (hf : f ≠ 0) :
    ∃ (d : Hypersurface R f →ₗ[Hypersurface R f] (Fin 2 → Hypersurface R f))
      (π : (Fin 2 → Hypersurface R f) →ₗ[Hypersurface R f]
        Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
          (Hypersurface R f)),
      Function.Exact d π ∧ Function.Surjective π ∧
        d 1 = (fun i => hypersurfacePartial (f := f) i) := by
  sorry

/-- A source-facing formulation of a finite module being locally free of a
    fixed rank, using Mathlib's free locus and stalk rank. -/
def IsLocallyFreeOfRank
    (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M] (n : ℕ) : Prop :=
  Module.freeLocus A M = Set.univ ∧
    ∀ q : PrimeSpectrum A, Module.rankAtStalk M q = n

theorem hypersurface_jacobian_smooth
    {R : Type u} [CommRing R] (f : MvPolynomial (Fin 2) R)
    (hjac : Ideal.span (Set.range (hypersurfacePartial (f := f))) =
      (⊤ : Ideal (Hypersurface R f))) :
    Algebra.Smooth R (Hypersurface R f) ∧
      IsLocallyFreeOfRank (Hypersurface R f)
        (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
          (Hypersurface R f)) 1 := by
  sorry

/- The inseparable specialization uses the same hypersurface presentation. -/
abbrev InseparableHypersurface (R : Type u) [CommRing R] (p : ℕ) : Type u :=
  Hypersurface R (MvPolynomial.X (0 : Fin 2) ^ p +
    MvPolynomial.X (1 : Fin 2) ^ p)

theorem inseparable_hypersurface_warning
    {R : Type u} [CommRing R] [Nontrivial R]
    (p : ℕ) (hp : Nat.Prime p) [CharP R p] :
    IsLocallyFreeOfRank (InseparableHypersurface R p)
        (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
          (InseparableHypersurface R p)) 2 ∧
      Formalization.Books.Algebra.Unit136.IsRelativeGlobalCompleteIntersection
        (algebraMap R (InseparableHypersurface R p)) ∧
      ¬ Algebra.Smooth R (InseparableHypersurface R p) := by
  sorry

/- The textbook definition is exactly Mathlib's `Smooth` class: formal
   smoothness (projective Kähler differentials and vanishing H₁) together with
   finite presentation. -/
theorem smooth_iff_formallySmooth_and_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.Smooth R S ↔
      Algebra.FormallySmooth R S ∧ Algebra.FinitePresentation R S := by
  constructor
  · intro h
    exact ⟨h.formallySmooth, h.finitePresentation⟩
  · rintro ⟨hformal, hfp⟩
    exact { formallySmooth := hformal, finitePresentation := hfp }

theorem smooth_presentation_iff_split_injection
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι)
    [Algebra.FinitePresentation R S] :
    Algebra.Smooth R S ↔
      ∃ l : P.toExtension.CotangentSpace →ₗ[S] P.toExtension.Cotangent,
        l ∘ₗ P.toExtension.cotangentComplex = LinearMap.id := by
  constructor
  · intro h
    let _ : Algebra.FormallySmooth R P.toExtension.Ring :=
      Algebra.instFormallySmoothMvPolynomial ι
    exact (Algebra.Extension.formallySmooth_iff_split_injection
      P.toExtension).mp h.formallySmooth
  · intro h
    let _ : Algebra.FormallySmooth R P.toExtension.Ring :=
      Algebra.instFormallySmoothMvPolynomial ι
    let hformal : Algebra.FormallySmooth R S :=
      (Algebra.Extension.formallySmooth_iff_split_injection
        P.toExtension).mpr h
    exact { formallySmooth := hformal, finitePresentation := inferInstance }

/- The conormal/cokernel formulation is the source-facing strengthening of
   the split-injection criterion.  The quotient is Mathlib's module quotient,
   and the conormal is `PresentationConormal P`. -/
theorem smooth_presentation_conormal_cokernel
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι)
    [Algebra.Smooth R S] :
    Function.Injective P.toExtension.cotangentComplex ∧
      Module.Finite S
        (P.toExtension.CotangentSpace ⧸
          LinearMap.range P.toExtension.cotangentComplex) ∧
      Module.Projective S
        (P.toExtension.CotangentSpace ⧸
          LinearMap.range P.toExtension.cotangentComplex) ∧
      Module.Finite S P.toExtension.Cotangent ∧
      Module.Projective S P.toExtension.Cotangent := by
  sorry

theorem smooth_presentation_module_decomposition
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Formalization.Books.Algebra.Unit134.Presentation R S ι)
    [Algebra.Smooth R S] :
    Nonempty (P.toExtension.CotangentSpace ≃ₗ[S]
      P.toExtension.Cotangent ×
        Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) := by
  sorry

/-! ## Localization, base change, and the field case -/

theorem smooth_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (g : S) :
    Algebra.Smooth R (Localization.Away g) := by
  sorry

theorem smooth_localization_of_base
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [Algebra (Localization.Away r) S]
    [IsScalarTower R (Localization.Away r) S]
    (hunit : IsUnit (algebraMap R S r)) [Algebra.Smooth R S] :
    Algebra.Smooth (Localization.Away r) S := by
  sorry

theorem smooth_base_change
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.Smooth R S] :
    Algebra.Smooth R' (R' ⊗[R] S) := by
  infer_instance

theorem smooth_over_field_is_local_complete_intersection
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.Smooth k S] :
    Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S := by
  sorry

/-! ## Standard smooth presentations -/

/- `Algebra.IsStandardSmooth` is Mathlib's quotient-by-relations definition:
   it is existence of a finite `SubmersivePresentation`, whose `map` selects
   the variables used by the Jacobian minor. -/
theorem submersive_presentation_consequences
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Finite σ] (P : Algebra.SubmersivePresentation R S ι σ) :
    Algebra.Smooth R S ∧
      Function.Injective P.toExtension.cotangentComplex ∧
      Module.Free S P.toExtension.Cotangent ∧
      Nonempty (Basis σ S P.toExtension.Cotangent) ∧
      Module.Free S (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) ∧
      Nonempty (Basis ((Set.range P.map)ᶜ : Set ι) S
        (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S)) := by
  sorry

theorem submersive_presentation_relative_dimension
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Finite ι] [Finite σ] [Nontrivial S]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    Module.rank S (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) =
      P.dimension := by
  sorry

theorem standard_smooth_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmooth R S] (g : S) :
    Algebra.IsStandardSmooth R (Localization.Away g) := by
  sorry

theorem standard_smooth_base_change
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.IsStandardSmooth R S] :
    Algebra.IsStandardSmooth R' (R' ⊗[R] S) := by
  infer_instance

theorem standard_smooth_localization_of_base
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [Algebra (Localization.Away r) S]
    [IsScalarTower R (Localization.Away r) S]
    (hunit : IsUnit (algebraMap R S r))
    [Algebra.IsStandardSmooth R S] :
    Algebra.IsStandardSmooth (Localization.Away r) S := by
  sorry

theorem standard_smooth_is_relative_global_complete_intersection
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmooth R S] :
    Formalization.Books.Algebra.Unit136.IsRelativeGlobalCompleteIntersection
      (algebraMap R S) := by
  sorry

/-- The polynomial lift along the inclusion of variables `Fin n ↪ Fin (n+1)`. -/
noncomputable def liftPolynomialToSucc
    {R : Type u} [CommRing R] {n : ℕ}
    (f : MvPolynomial (Fin n) R) : MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.rename (Fin.castLE (Nat.le_succ n)) f

/-- The Jacobian determinant on the first `c` variables. -/
noncomputable def jacobianDeterminant
    {R : Type u} [CommRing R] {n c : ℕ} (hcn : c ≤ n)
    (fs : Fin c → MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R :=
  Matrix.det (fun i j =>
    MvPolynomial.pderiv (Fin.castLE hcn i) (fs j))

/-- The quotient in the standard-smooth localization example. -/
noncomputable def jacobianInversionIdeal
    {R : Type u} [CommRing R] {n c : ℕ} (hcn : c ≤ n)
    (fs : Fin c → MvPolynomial (Fin n) R) :
    Ideal (MvPolynomial (Fin (n + 1)) R) :=
  Ideal.span
    (Set.range (fun i : Fin c => liftPolynomialToSucc (fs i)) ∪
      {MvPolynomial.X (Fin.last n) *
          liftPolynomialToSucc (jacobianDeterminant hcn fs) - 1})

noncomputable abbrev jacobianInversionRing
    {R : Type u} [CommRing R] {n c : ℕ} (hcn : c ≤ n)
    (fs : Fin c → MvPolynomial (Fin n) R) : Type u :=
  MvPolynomial (Fin (n + 1)) R ⧸ jacobianInversionIdeal hcn fs

theorem jacobian_inversion_is_standard_smooth
    {R : Type u} [CommRing R] {n c : ℕ} (hcn : c ≤ n)
    (fs : Fin c → MvPolynomial (Fin n) R) :
    Algebra.IsStandardSmooth R (jacobianInversionRing hcn fs) := by
  sorry

theorem standard_smooth_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Algebra.IsStandardSmooth R S]
    [Algebra.IsStandardSmooth S T] :
    Algebra.IsStandardSmooth R T := by
  exact Algebra.IsStandardSmooth.trans R S T

theorem smooth_standard_smooth_cover
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] :
    ∃ s : Set S, Ideal.span s = (⊤ : Ideal S) ∧
      ∀ g ∈ s, Algebra.IsStandardSmooth R (Localization.Away g) := by
  exact Algebra.Smooth.exists_span_eq_top_isStandardSmooth R S

theorem smooth_standard_smooth_basic_open_cover
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] :
    ∃ s : Set S,
      (⋃ g ∈ s, (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))) = Set.univ ∧
        ∀ g ∈ s, Algebra.IsStandardSmooth R (Localization.Away g) := by
  sorry

theorem smooth_is_syntomic
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] :
    Formalization.Books.Algebra.Unit136.IsSyntomic (algebraMap R S) := by
  sorry

/-! ## Smoothness at points and the Jacobian criterion -/

/-- Source-facing smoothness at a prime: smoothness on some basic open. -/
def IsSmoothAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ Algebra.Smooth R (Localization.Away g)

def SmoothLocus
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Set (PrimeSpectrum S) := {q | IsSmoothAt R S q}

def H1VanishingAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  Subsingleton (Algebra.H1Cotangent R (Localization.AtPrime q.asIdeal))

def DifferentialsFiniteFreeAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  Module.Finite (Localization.AtPrime q.asIdeal)
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
        (Localization.AtPrime q.asIdeal)) ∧
    Module.Free (Localization.AtPrime q.asIdeal)
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
        (Localization.AtPrime q.asIdeal))

def DifferentialsProjectiveAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  Module.Finite (Localization.AtPrime q.asIdeal)
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
        (Localization.AtPrime q.asIdeal)) ∧
    Module.Projective (Localization.AtPrime q.asIdeal)
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
        (Localization.AtPrime q.asIdeal))

def DifferentialsFlatAt
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  Module.Finite (Localization.AtPrime q.asIdeal)
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
        (Localization.AtPrime q.asIdeal)) ∧
    Module.Flat (Localization.AtPrime q.asIdeal)
      (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R
        (Localization.AtPrime q.asIdeal))

theorem smooth_at_iff_local_cotangent_conditions
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (q : PrimeSpectrum S) :
    List.TFAE
      [ IsSmoothAt R S q,
        H1VanishingAt R S q ∧ DifferentialsFiniteFreeAt R S q,
        H1VanishingAt R S q ∧ DifferentialsProjectiveAt R S q,
        H1VanishingAt R S q ∧ DifferentialsFlatAt R S q ] := by
  sorry

theorem smooth_iff_smooth_at_all_primes
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.Smooth R S ↔ ∀ q : PrimeSpectrum S, IsSmoothAt R S q := by
  sorry

theorem isOpen_smoothLocus
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] :
    IsOpen (SmoothLocus R S) := by
  sorry

theorem smooth_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Algebra.Smooth R S] [Algebra.Smooth S T] :
    Algebra.Smooth R T := by
  exact Algebra.Smooth.comp R S T

theorem smooth_product_iff
    {R S' S'' : Type*} [CommRing R] [CommRing S'] [CommRing S'']
    [Algebra R S'] [Algebra R S''] :
    Algebra.Smooth R (S' × S'') ↔
      Algebra.Smooth R S' ∧ Algebra.Smooth R S'' := by
  sorry

/-- A maximal Jacobian minor indexed by an embedding of variables. -/
noncomputable def jacobianMinor
    {R : Type u} [CommRing R] {n c : ℕ}
    (fs : Fin c → MvPolynomial (Fin n) R) (e : Fin c ↪ Fin n) :
    MvPolynomial (Fin n) R :=
  Matrix.det (fun i j => MvPolynomial.pderiv (e i) (fs j))

theorem relative_global_complete_intersection_jacobian_criterion
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n c : ℕ} (P : Formalization.Books.Algebra.Unit134.Presentation
      R S (Fin n)) (fs : Fin c → P.Ring)
    (hker : P.ker = Ideal.ofList (List.ofFn fs))
    (q : PrimeSpectrum S) :
    IsSmoothAt R S q ↔
      ∃ e : Fin c ↪ Fin n,
        (algebraMap P.Ring S) (jacobianMinor (R := R) (fun i => fs i) e) ∉ q.asIdeal := by
  sorry

/-! ## Flat fibres, smooth loci, field extension, and lifting -/

/-- Smoothness on a fibre at a chosen prime, in the same basic-open language. -/
def FiberSmoothAt
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum (Formalization.Books.Algebra.Unit136.Fiber R S p)) : Prop :=
  letI : Algebra p.asIdeal.ResidueField
      (Formalization.Books.Algebra.Unit136.Fiber R S p) :=
    Algebra.TensorProduct.leftAlgebra
  ∃ g, g ∉ q.asIdeal ∧
    Algebra.Smooth p.asIdeal.ResidueField
      (Localization.Away g)

noncomputable def fiberMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) :
    S →ₐ[R]
      Formalization.Books.Algebra.Unit136.Fiber R S p := by
  exact Algebra.TensorProduct.includeRight

theorem smooth_at_of_flat_fiber
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : p.asIdeal = q.asIdeal.comap (algebraMap R S))
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧
      Algebra.FinitePresentation R (Localization.Away g))
    (hflat : RingHom.Flat
      (Localization.localRingHom p.asIdeal q.asIdeal
        (algebraMap R S) hlying))
    (qf : PrimeSpectrum (Formalization.Books.Algebra.Unit136.Fiber R S p))
    (hcorresponding : PrimeSpectrum.comap
      (fiberMap (R := R) (S := S) p).toRingHom qf = q)
    (hfiber : FiberSmoothAt p qf) :
    IsSmoothAt R S q := by
  sorry

theorem flat_base_change_smooth_locus
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.FinitePresentation R S]
    [Module.Flat R R'] :
    SmoothLocus R' (R' ⊗[R] S) =
      (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight :
        S →ₐ[R] (R' ⊗[R] S)).toRingHom) ⁻¹' SmoothLocus R S := by
  sorry

theorem smooth_field_change_at
    {k K S : Type*} [Field k] [Field K] [CommRing S]
    [Algebra k S] [Algebra k K] [Algebra.FiniteType k S]
    (qK : PrimeSpectrum (K ⊗[k] S)) (q : PrimeSpectrum S)
    (hlying : q.asIdeal = qK.asIdeal.comap
      (Algebra.TensorProduct.includeRight :
        S →ₐ[k] (K ⊗[k] S)).toRingHom) :
    letI : Algebra K (K ⊗[k] S) := Algebra.TensorProduct.leftAlgebra
    IsSmoothAt k S q ↔ IsSmoothAt K (K ⊗[k] S) qK := by
  sorry

/-- The source's local lifting conclusion, expressed using algebra equivalences
    and the canonical quotient ideal `I Sᵢ`. -/
def HasStandardSmoothLiftCover
    {R Sbar : Type u} [CommRing R] [CommRing Sbar]
    (I : Ideal R) [Algebra (R ⧸ I) Sbar] : Prop :=
  letI : Algebra R Sbar := Algebra.compHom Sbar
    ((algebraMap (R ⧸ I) Sbar).comp (Ideal.Quotient.mk I))
  ∃ (ι : Type*) (g : ι → Sbar),
    Ideal.span (Set.range g) = (⊤ : Ideal Sbar) ∧
      ∀ i, ∃ (T : Type*) (hT : CommRing T) (hRT : Algebra R T),
        letI : CommRing T := hT
        letI : Algebra R T := hRT
        letI : Algebra (R ⧸ I)
            (T ⧸ Ideal.map (algebraMap R T) I) :=
          Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
        Algebra.IsStandardSmooth R T ∧
          Nonempty (Localization.Away (g i) ≃ₐ[R ⧸ I]
            (T ⧸ Ideal.map (algebraMap R T) I))

theorem smooth_lift_standard_smooth_cover
    {R Sbar : Type u} [CommRing R] [CommRing Sbar]
    (I : Ideal R) [Algebra (R ⧸ I) Sbar]
    (h : Algebra.Smooth (R ⧸ I) Sbar) :
    HasStandardSmoothLiftCover (Sbar := Sbar) I := by
  sorry

end
end Formalization.Books.Algebra.Unit137
