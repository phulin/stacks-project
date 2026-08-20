import Formalization.Books.Algebra.Unit113.DimensionFormula
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Formalization.Books.Algebra.Unit136.SyntomicMorphisms
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Commutative Algebra, Chapter 143: Étale ring maps

This file records the definitions and theorem interfaces in the first chapter
section on étale maps.  Étale algebras themselves are Mathlib's canonical
`Algebra.Etale` class; the source-facing definitions below only package the
local, approximation, diagrammatic, and polynomial data that the textbook
uses explicitly.
-/

namespace Formalization.Books.Algebra.Unit143

open Set
open Polynomial
open Formalization.Books.Algebra.Unit136
open scoped TensorProduct

noncomputable section

universe u v

/-! ## The definition and the standard-smooth presentation -/

/-- The source definition of étale, expressed through Mathlib's canonical
finite-presentation and naive-cotangent-complex interfaces. -/
theorem etale_iff_finitePresentation_and_cotangent_vanishing
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.Etale R S ↔
      Algebra.FinitePresentation R S ∧
        Subsingleton (Algebra.H1Cotangent R S) ∧
          Subsingleton (KaehlerDifferential R S) := by
  constructor
  · intro h
    exact ⟨h.finitePresentation, h.formallyEtale.subsingleton_h1Cotangent,
      h.formallyEtale.subsingleton_kaehlerDifferential⟩
  · rintro ⟨hfp, hh1, hkd⟩
    exact ⟨{ subsingleton_kaehlerDifferential := hkd
             subsingleton_h1Cotangent := hh1 }, hfp⟩

/- The introductory relative-dimension formulation is already the canonical
   Mathlib theorem; expose it under the chapter namespace without defining a
   parallel notion of relative dimension. -/
theorem etale_iff_standardSmoothOfRelativeDimension_zero
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.Etale R S ↔
      Algebra.IsStandardSmoothOfRelativeDimension 0 R S :=
  Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero

/-- An étale algebra has zero Kähler differentials. -/
theorem etale_subsingleton_kaehlerDifferential
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] :
    Subsingleton (KaehlerDifferential R S) := by
  infer_instance

/-- For a smooth algebra, étaleness is equivalent to vanishing of the
Kähler differentials. -/
theorem smooth_etale_iff_subsingleton_kaehlerDifferential
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] :
    Algebra.Etale R S ↔
      Subsingleton (KaehlerDifferential R S) := by
  constructor
  · intro h
    exact h.formallyEtale.subsingleton_kaehlerDifferential
  · intro h
    exact ⟨{ subsingleton_kaehlerDifferential := h
             subsingleton_h1Cotangent := inferInstance }, inferInstance⟩

/-- The source's basic-open definition of étale at a prime. -/
def IsEtaleAt
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∃ g : S, g ∉ q.asIdeal ∧ Algebra.Etale R (Localization.Away g)

/-- At finite presentation, the source's basic-open definition agrees with
Mathlib's stalk definition. -/
theorem isEtaleAt_iff_mathlib
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (q : PrimeSpectrum S) :
    IsEtaleAt R S q ↔ Algebra.IsEtaleAt R q.asIdeal := by
  constructor
  · rintro ⟨g, hg, hEtale⟩
    have hsub : (↑(PrimeSpectrum.basicOpen g) : Set (PrimeSpectrum S)) ⊆
        Algebra.etaleLocus R S :=
      (Algebra.basicOpen_subset_etaleLocus_iff_etale (R := R) (f := g)).2 hEtale
    exact hsub ((PrimeSpectrum.mem_basicOpen g q).2 hg)
  · intro h
    let _ : Algebra.IsEtaleAt R q.asIdeal := h
    exact Algebra.exists_etale_of_isEtaleAt (R := R) (A := S) q.asIdeal

/-- A source-facing standard-smooth presentation with equally many variables
and relations.  `SubmersivePresentation` contains the Jacobian invertibility
condition used in the source definition. -/
structure EtaleStandardSmoothPresentation
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  number : ℕ
  presentation :
    Algebra.SubmersivePresentation R S (Fin number) (Fin number)

/-- Every étale algebra admits the source's standard-smooth presentation. -/
theorem etale_exists_standardSmoothPresentation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] :
    Nonempty (EtaleStandardSmoothPresentation R S) := by
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension 0 R S :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := R) (S := S)).mp
      (inferInstance : Algebra.Etale R S)
  obtain ⟨ι, σ, hσ, hι, P, hP⟩ := hstd.out
  let _ : Finite σ := hσ
  let _ : Finite ι := hι
  let _ : Fintype σ := Fintype.ofFinite σ
  let _ : Fintype ι := Fintype.ofFinite ι
  have hle : Nat.card ι ≤ Nat.card σ := by
    apply Nat.sub_eq_zero_iff_le.mp
    simpa [Algebra.Presentation.dimension] using hP
  have hge : Nat.card σ ≤ Nat.card ι :=
    P.toPreSubmersivePresentation.card_relations_le_card_vars_of_isFinite
  have hcard : Fintype.card ι = Fintype.card σ := by
    apply Nat.le_antisymm
    · simpa only [Nat.card_eq_fintype_card] using hle
    · simpa only [Nat.card_eq_fintype_card] using hge
  let e : ι ≃ σ := Fintype.equivOfCardEq hcard
  let P' := P.reindex (Fintype.equivFin ι).symm
    ((Fintype.equivFin ι).symm.trans e)
  exact ⟨⟨Fintype.card ι, P'⟩⟩

/-! ## Permanence properties -/

/-- A principal localization is étale over its base. -/
theorem etale_localization_away
    {R : Type u} [CommRing R] (f : R) :
    Algebra.Etale R (Localization.Away f) := by
  exact Algebra.Etale.of_isLocalizationAway f

/-- Étale maps are stable under composition. -/
theorem etale_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.Etale R S] [Algebra.Etale S T] :
    Algebra.Etale R T := by
  exact Algebra.Etale.comp R S T

/-- Étale maps are stable under arbitrary base change. -/
theorem etale_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.Etale R S] :
    Algebra.Etale R' (R' ⊗[R] S) := by
  infer_instance

/-- A standard étale presentation has at most `|T|` algebra maps to a
finite target `T`: every map is determined by the distinguished generator. -/
theorem card_algHom_le_of_isStandardEtale
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Fintype T] [Fintype (S →ₐ[R] T)]
    (hS : Algebra.IsStandardEtale R S) :
    Fintype.card (S →ₐ[R] T) ≤ Fintype.card T := by
  let _ : Algebra.IsStandardEtale R S := hS
  let P : StandardEtalePresentation R S :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  exact Fintype.card_le_of_injective (fun f : S →ₐ[R] T ↦ f P.x)
    (fun _ _ h ↦ P.hom_ext h)

/-- Étaleness is local on the target for a finite basic-open cover. -/
theorem etale_local_on_target
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (m : ℕ) (g : Fin m → S)
    (hgen : Ideal.span (Set.range g) = (⊤ : Ideal S))
    (hEtale : ∀ i, Algebra.Etale R (Localization.Away (g i))) :
    Algebra.Etale R S := by
  rw [← RingHom.etale_algebraMap]
  refine @RingHom.Etale.ofLocalizationSpanTarget R S _ _ (algebraMap R S)
    (Set.range g) hgen ?_
  rintro ⟨r, ⟨i, rfl⟩⟩
  have hcomp :
      (algebraMap S (Localization.Away (g i))).comp (algebraMap R S) =
        algebraMap R (Localization.Away (g i)) :=
    (IsScalarTower.algebraMap_eq R S (Localization.Away (g i))).symm
  rw [hcomp]
  exact (RingHom.etale_algebraMap (R := R)
    (S := Localization.Away (g i))).mpr (hEtale i)

/-- The étale locus commutes with flat base change for a finitely presented
algebra.  The inverse image is taken along the canonical map from `S` to the
base-change algebra. -/
theorem etale_locus_flat_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    (hfp : Algebra.FinitePresentation R S)
    (hflat : RingHom.Flat (algebraMap R R')) :
    letI : Algebra.FinitePresentation R S := hfp
    letI : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    Algebra.etaleLocus R' (R' ⊗[R] S) =
      (PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight :
          S →ₐ[R] (R' ⊗[R] S)).toRingHom) ⁻¹'
        Algebra.etaleLocus R S := by
  sorry

/-- Étale maps are syntomic. -/
theorem etale_is_syntomic
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : RingHom.Etale f) :
    Formalization.Books.Algebra.Unit136.IsSyntomic f := by
  sorry

/-- Étale maps are flat. -/
theorem etale_is_flat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : RingHom.Etale f) :
    RingHom.Flat f := by
  exact (RingHom.Etale.iff_flat_and_formallyUnramified.mp h).1

/-- Over a field, finite type plus vanishing differentials is equivalent to
étaleness. -/
theorem etale_over_field_iff_subsingleton_kaehlerDifferential
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] :
    Algebra.Etale k S ↔
      Subsingleton (KaehlerDifferential k S) := by
  sorry

/-! ## Finite-type approximation and filtered colimits -/

/-- Data for the finite-type-over-`ℤ` approximation of an étale map. -/
structure EtaleFiniteTypeApproximation
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  R₀ : Type u
  [commRingR₀ : CommRing R₀]
  S₀ : Type u
  [commRingS₀ : CommRing S₀]
  [algebraIntR₀ : Algebra ℤ R₀]
  [algebraR₀R : Algebra R₀ R]
  [algebraR₀S₀ : Algebra R₀ S₀]
  finiteTypeOverInt : Algebra.FiniteType ℤ R₀
  etale : Algebra.Etale R₀ S₀
  baseChange :
    letI : Algebra R (R ⊗[R₀] S₀) := Algebra.TensorProduct.leftAlgebra
    Nonempty (R ⊗[R₀] S₀ ≃ₐ[R] S)

/-- Every étale map is obtained by base change from one whose source is of
finite type over the integers. -/
theorem etale_finite_type_approximation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] :
    Nonempty (EtaleFiniteTypeApproximation R S) := by
  obtain ⟨R₀, S₀, _, _, hfg, hEtale, hbase⟩ :=
    Algebra.Etale.exists_subalgebra_fg (R := ℤ) (A := R) (B := S)
  obtain ⟨hbase⟩ := hbase
  let hfiniteType : Algebra.FiniteType ℤ R₀ := ⟨R₀.fg_top.mpr hfg⟩
  exact ⟨{
    R₀ := R₀
    S₀ := S₀
    finiteTypeOverInt := hfiniteType
    etale := hEtale
    baseChange := ⟨hbase.symm⟩
  }⟩

/-- A stage of a directed ring colimit together with an étale algebra whose
base change is the given étale algebra.  The directed-ring-colimit fields are
the canonical filtered-colimit presentation from Chapter 127. -/
structure EtaleDirectedColimitData
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (D : Formalization.Books.Algebra.Unit127.DirectedRingColimit (R := A)) where
  i : D.index
  Bᵢ : Type u
  [commRingBᵢ : CommRing Bᵢ]
  stageAlgebra :
    letI : Preorder D.index := D.indexPreorder
    Algebra (D.diagram.obj i) Bᵢ
  etale :
    letI : Preorder D.index := D.indexPreorder
    letI : Algebra (D.diagram.obj i) Bᵢ := stageAlgebra
    Algebra.Etale (D.diagram.obj i) Bᵢ
  baseChange :
    letI : Preorder D.index := D.indexPreorder
    letI : Algebra (D.diagram.obj i) Bᵢ := stageAlgebra
    letI : Algebra (D.diagram.obj i) A :=
      (D.stageToTarget i).toAlgebra
    Nonempty (A ⊗[D.diagram.obj i] Bᵢ ≃ₐ[A] B)

/-- Étaleness descends to a stage in a filtered colimit of rings. -/
theorem etale_descends_filtered_colimit
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (D : Formalization.Books.Algebra.Unit127.DirectedRingColimit (R := A))
    [Algebra.Etale A B] :
    Nonempty (EtaleDirectedColimitData A B D) := by
  sorry

/-- Data expressing that an étale algebra over a localization descends to an
étale algebra before localization. -/
structure EtaleLocalizationDescentData
    (A B' : Type u) [CommRing A] [CommRing B'] (M : Submonoid A)
    [Algebra (Localization M) B'] where
  B : Type u
  [commRingB : CommRing B]
  [algebraAB : Algebra A B]
  etale : Algebra.Etale A B
  localizationEquiv :
    Nonempty (B' ≃ₐ[Localization M]
      Localization (Algebra.algebraMapSubmonoid B M))

/-- An étale map out of a localization spreads out to an étale map before
localization. -/
theorem etale_spreads_out_of_localization
    {A B' : Type u} [CommRing A] [CommRing B'] (M : Submonoid A)
    [Algebra (Localization M) B'] [Algebra.Etale (Localization M) B'] :
    Nonempty (EtaleLocalizationDescentData A B' M) := by
  sorry

/-! ## Products and fields -/

/-- Étaleness of a product is equivalent to étaleness of both factors. -/
theorem etale_prod_iff
    {A B' B'' : Type u} [CommRing A] [CommRing B'] [CommRing B'']
    [Algebra A B'] [Algebra A B''] :
    Algebra.Etale A (B' × B'') ↔
      Algebra.Etale A B' ∧ Algebra.Etale A B'' := by
  sorry

/-- Over a field, an étale algebra is precisely a finite product of finite
separable field extensions.  This is Mathlib's canonical classification. -/
theorem etale_over_field_iff_finite_product_separable
    {k S : Type u} [Field k] [CommRing S] [Algebra k S] :
    Algebra.Etale k S ↔
      ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u)
        (_ : ∀ i, Field (Ai i)) (_ : ∀ i, Algebra k (Ai i))
        (_ : S ≃ₐ[k] Π i, Ai i),
        ∀ i, Module.Finite k (Ai i) ∧ Algebra.IsSeparable k (Ai i) := by
  exact Algebra.Etale.iff_exists_algEquiv_prod k S

/-! ## Étale maps at primes and local criteria -/

/-- The equality of the two extended prime ideals in the local ring at `q`,
together with the assertion that they are maximal. -/
def EtalePrimeIdealCondition
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) : Prop :=
  let f : R →+* Localization.AtPrime q.asIdeal :=
    (algebraMap S (Localization.AtPrime q.asIdeal)).comp (algebraMap R S)
  Ideal.map f p.asIdeal =
      Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) q.asIdeal ∧
    Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) q.asIdeal =
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)

/-- The condition used in the converse local criterion: the extension of the
base prime to the local ring at `q` is its maximal ideal. -/
def EtaleMaximalIdealCondition
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) : Prop :=
  let f : R →+* Localization.AtPrime q.asIdeal :=
    (algebraMap S (Localization.AtPrime q.asIdeal)).comp (algebraMap R S)
  Ideal.map f p.asIdeal =
    IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)

/-- The finite separable residue-field condition at a prime. -/
def EtaleResidueFieldCondition
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : PrimeSpectrum.comap (algebraMap R S) q = p) : Prop :=
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (Formalization.Books.Algebra.Unit113.residueFieldMapAt
      (algebraMap R S) p q hlying).toAlgebra
  Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField ∧
    Algebra.IsSeparable p.asIdeal.ResidueField q.asIdeal.ResidueField

/-- Flatness of the induced map on the local rings at a pair of primes. -/
def EtaleFlatAtPrime
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : PrimeSpectrum.comap (algebraMap R S) q = p) : Prop :=
  let hcomap : p.asIdeal = q.asIdeal.comap (algebraMap R S) := by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hlying).symm
  RingHom.Flat
    (Localization.localRingHom p.asIdeal q.asIdeal
      (algebraMap R S) hcomap)

/-- Étaleness at a prime forces equality of the extended prime ideals and a
finite separable residue-field extension. -/
theorem etale_at_prime
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : PrimeSpectrum.comap (algebraMap R S) q = p)
    (h : IsEtaleAt R S q) :
    EtalePrimeIdealCondition p q ∧
      EtaleResidueFieldCondition p q hlying := by
  sorry

/-- Étale maps are quasi-finite. -/
theorem etale_is_quasiFinite
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : RingHom.Etale f) :
    RingHom.QuasiFinite f := by
  sorry

/-- The local criterion for being étale at a prime. -/
theorem characterize_etale_at_prime
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : PrimeSpectrum.comap (algebraMap R S) q = p)
    (hfp : RingHom.FinitePresentation (algebraMap R S))
    (hflat : EtaleFlatAtPrime p q hlying)
    (hmaximal : EtaleMaximalIdealCondition p q)
    (hresidue : EtaleResidueFieldCondition p q hlying) :
    IsEtaleAt R S q := by
  sorry

/-- A map between two étale algebras over the same base is étale. -/
theorem etale_map_between_etale_algebras
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S']
    (hS : Algebra.Etale R S) (hS' : Algebra.Etale R S')
    (f : S' →ₐ[R] S) :
    letI : Algebra S' S := f.toAlgebra
    Algebra.Etale S' S := by
  sorry

/-! ## Lifting lemmas -/

/-- A surjective flat finitely presented map is the localization at an
idempotent. -/
theorem surjective_flat_finitely_presented_is_localization
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hsurj : Function.Surjective f)
    (hflat : RingHom.Flat f)
    (hfp : RingHom.FinitePresentation f) :
    letI : Algebra R S := f.toAlgebra
    ∃ e : R, IsIdempotentElem e ∧
      Nonempty (S ≃ₐ[R] Localization.Away e) := by
  sorry

/-- Data for lifting an étale algebra across the quotient by an ideal. -/
structure EtaleLiftData
    (R Sbar : Type u) [CommRing R] [CommRing Sbar]
    (I : Ideal R) [Algebra (R ⧸ I) Sbar] where
  S : Type u
  [commRingS : CommRing S]
  [algebraRS : Algebra R S]
  etale : Algebra.Etale R S
  quotientEquiv :
    letI : Algebra (R ⧸ I)
        (S ⧸ Ideal.map (algebraMap R S) I) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    Nonempty
      ((S ⧸ Ideal.map (algebraMap R S) I) ≃ₐ[R ⧸ I] Sbar)

/-- Étale algebras lift along a quotient of the base ring. -/
theorem etale_lift_along_quotient
    {R Sbar : Type u} [CommRing R] [CommRing Sbar]
    (I : Ideal R) [Algebra (R ⧸ I) Sbar]
    [Algebra.Etale (R ⧸ I) Sbar] :
    Nonempty (EtaleLiftData R Sbar I) := by
  sorry

/-- A square-zero diagram with exact rows and the source's base-change
identification of the two kernels. -/
structure SquareZeroEtaleDiagram
    (A A' B B' : Type u)
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B'] where
  AToB : A →+* B
  A'ToA : A' →+* A
  A'ToB' : A' →+* B'
  B'ToB : B' →+* B
  commutes : B'ToB.comp A'ToB' = AToB.comp A'ToA
  surjectiveA : Function.Surjective A'ToA
  surjectiveB : Function.Surjective B'ToB
  kernelASquareZero : (RingHom.ker A'ToA) ^ 2 = ⊥
  kernelBSquareZero : (RingHom.ker B'ToB) ^ 2 = ⊥
  I : Type u
  [addCommGroupI : AddCommGroup I]
  [moduleAI : Module A I]
  J : Type u
  [addCommGroupJ : AddCommGroup J]
  [moduleBJ : Module B J]
  i : I →+ A'
  j : J →+ B'
  exactA : Function.Exact i A'ToA
  exactB : Function.Exact j B'ToB
  iInjective : Function.Injective i
  jInjective : Function.Injective j
  i_smul : ∀ (a' : A') (x : I),
    i ((A'ToA a') • x) = a' * i x
  j_smul : ∀ (b' : B') (y : J),
    j ((B'ToB b') • y) = b' * j y
  kernelMap :
    letI : Algebra A B := AToB.toAlgebra
    letI : Module A J := Module.restrictScalars A B J
    I →ₗ[A] J
  kernelMap_commutes :
    letI : Algebra A B := AToB.toAlgebra
    letI : Module A J := Module.restrictScalars A B J
    ∀ x, j (kernelMap x) = A'ToB' (i x)
  kernelBaseChange :
    letI : Algebra A B := AToB.toAlgebra
    letI : Module A J := Module.restrictScalars A B J
    ∃ e : B ⊗[A] I ≃ₗ[B] J,
      ∀ (b : B) (x : I), e (b ⊗ₜ[A] x) = b • kernelMap x

/-- Étaleness lifts across the source's square-zero exact diagram. -/
theorem etale_lift_infinitesimal
    {A A' B B' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    (D : SquareZeroEtaleDiagram A A' B B')
    (h : RingHom.Etale D.AToB) :
    RingHom.Etale D.A'ToB' := by
  sorry

/-! ## The factor-polynomial example -/

/-- The universal left factor `g`. -/
noncomputable def factorLeftPolynomial (n m : ℕ) :
    Polynomial (FactorPolynomialTarget n m) :=
  Formalization.Books.Algebra.Unit136.monicPolynomial n
    (fun i => MvPolynomial.X (Sum.inl i))

/-- The universal right factor `h`. -/
noncomputable def factorRightPolynomial (n m : ℕ) :
    Polynomial (FactorPolynomialTarget n m) :=
  Formalization.Books.Algebra.Unit136.monicPolynomial m
    (fun j => MvPolynomial.X (Sum.inr j))

/-- The Sylvester matrix of the two universal factors. -/
noncomputable def factorSylvesterMatrix (n m : ℕ) :
    Matrix (Fin (n + m)) (Fin (n + m)) (FactorPolynomialTarget n m) :=
  Polynomial.sylvester (factorLeftPolynomial n m) (factorRightPolynomial n m) n m

/-- The resultant of the two universal factors. -/
noncomputable def factorResultant (n m : ℕ) : FactorPolynomialTarget n m :=
  Polynomial.resultant (factorLeftPolynomial n m) (factorRightPolynomial n m) n m

/- The quotient presentation used by the source's factor-polynomial example
   is already constructed in Chapter 136; this source-facing theorem retains
   that assertion without introducing a second presentation. -/
theorem factor_polynomial_map_presentation
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    letI : Algebra (FactorPolynomialBase n m) (FactorPolynomialTarget n m) :=
      (Formalization.Books.Algebra.Unit136.factorPolynomialMap n m).toAlgebra
    ∃ (P : Formalization.Books.Algebra.Unit134.Presentation
        (FactorPolynomialBase n m) (FactorPolynomialTarget n m) (Fin (n + m)))
      (fs : Fin (n + m) → P.Ring),
      Formalization.Books.Algebra.Unit136.IsPolynomialQuotientPresentation P fs := by
  exact Formalization.Books.Algebra.Unit136.factorPolynomialMap_has_expected_presentation
    hn hm

/-- The multiplication map represented by the Sylvester matrix. -/
noncomputable def factorSylvesterMap
    (n m : ℕ)
    (hn : (factorLeftPolynomial n m).natDegree ≤ n)
    (hm : (factorRightPolynomial n m).natDegree ≤ m) :
  Polynomial.degreeLT (FactorPolynomialTarget n m) m ×
        Polynomial.degreeLT (FactorPolynomialTarget n m) n →ₗ[
          FactorPolynomialTarget n m]
      Polynomial.degreeLT (FactorPolynomialTarget n m) (m + n) :=
  Polynomial.sylvesterMap (factorRightPolynomial n m)
    (factorLeftPolynomial n m) hm hn

/-- The target polynomial is the product of the two universal factors. -/
theorem factor_target_polynomial_eq_product (n m : ℕ) :
    Formalization.Books.Algebra.Unit136.factorTargetPolynomial n m =
      factorLeftPolynomial n m * factorRightPolynomial n m := by
  rfl

/-- The determinant of the displayed Sylvester matrix is the resultant. -/
theorem factor_sylvester_matrix_det_eq_resultant (n m : ℕ) :
    (factorSylvesterMatrix n m).det = factorResultant n m := by
  rfl

/-- The Sylvester map sends `(a,b)` to `g b + h a`, the displayed polynomial
linear map in the source. -/
theorem factor_sylvester_map_apply
    (n m : ℕ)
    (hn : (factorLeftPolynomial n m).natDegree ≤ n)
    (hm : (factorRightPolynomial n m).natDegree ≤ m)
    (a : Polynomial.degreeLT (FactorPolynomialTarget n m) m)
    (b : Polynomial.degreeLT (FactorPolynomialTarget n m) n) :
    (factorSylvesterMap n m hn hm (a, b)).1 =
      factorRightPolynomial n m * b.1 + factorLeftPolynomial n m * a.1 := by
  rfl

/-- Reduction of the universal left factor at a prime. -/
noncomputable def factorLeftPolynomialAtPrime
    (n m : ℕ) (q : PrimeSpectrum (FactorPolynomialTarget n m)) :
    Polynomial q.asIdeal.ResidueField :=
  (factorLeftPolynomial n m).map
    (algebraMap (FactorPolynomialTarget n m) q.asIdeal.ResidueField)

/-- Reduction of the universal right factor at a prime. -/
noncomputable def factorRightPolynomialAtPrime
    (n m : ℕ) (q : PrimeSpectrum (FactorPolynomialTarget n m)) :
    Polynomial q.asIdeal.ResidueField :=
  (factorRightPolynomial n m).map
    (algebraMap (FactorPolynomialTarget n m) q.asIdeal.ResidueField)

/-- The three equivalent descriptions of the étale locus in the factor
polynomial example. -/
theorem factor_polynomial_etale_locus
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (q : PrimeSpectrum (FactorPolynomialTarget n m)) :
    letI : Algebra (FactorPolynomialBase n m) (FactorPolynomialTarget n m) :=
      (Formalization.Books.Algebra.Unit136.factorPolynomialMap n m).toAlgebra
    List.TFAE
      [ IsEtaleAt (FactorPolynomialBase n m)
          (FactorPolynomialTarget n m) q,
        factorResultant n m ∉ q.asIdeal,
        IsCoprime (factorLeftPolynomialAtPrime n m q)
          (factorRightPolynomialAtPrime n m q) ] := by
  sorry

/-- The localization at the resultant is étale over the universal coefficient
ring. -/
theorem factor_polynomial_localization_etale
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    letI : Algebra (FactorPolynomialBase n m) (FactorPolynomialTarget n m) :=
      (Formalization.Books.Algebra.Unit136.factorPolynomialMap n m).toAlgebra
    Algebra.Etale (FactorPolynomialBase n m)
      (Localization.Away (factorResultant n m)) := by
  sorry

/-! ## Lifting a coprime factorization modulo a prime -/

/-- Data produced by the coprime factor-lifting lemma. -/
structure FactorModLiftData
    {R : Type u} [CommRing R] (f : Polynomial R)
    (p : PrimeSpectrum R)
    (gbar hbar : Polynomial p.asIdeal.ResidueField) where
  R' : Type u
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  etale : Algebra.Etale R R'
  p' : PrimeSpectrum R'
  liesOver : PrimeSpectrum.comap (algebraMap R R') p' = p
  residueFieldMapBijective :
    Function.Bijective
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt
        (algebraMap R R') p p' liesOver)
  g : Polynomial R'
  h : Polynomial R'
  factorization : Polynomial.map (algebraMap R R') f =
    (g : Polynomial R') * (h : Polynomial R')
  g_reduces :
    Polynomial.map (algebraMap R' p'.asIdeal.ResidueField) g =
      Polynomial.map
        (Formalization.Books.Algebra.Unit113.residueFieldMapAt
          (algebraMap R R') p p' liesOver) gbar
  h_reduces :
    Polynomial.map (algebraMap R' p'.asIdeal.ResidueField) h =
      Polynomial.map
        (Formalization.Books.Algebra.Unit113.residueFieldMapAt
          (algebraMap R R') p p' liesOver) hbar
  coprime : IsCoprime g h

/-- A coprime factorization of a monic polynomial modulo a prime lifts after
an étale extension, with equal residue fields and relatively prime lifted
factors. -/
theorem factor_mod_prime_lift_etale
    {R : Type u} [CommRing R] (f : Polynomial R) (hf : f.Monic)
    (p : PrimeSpectrum R)
    (gbar hbar : Polynomial p.asIdeal.ResidueField)
    (hfactor : Polynomial.map (algebraMap R p.asIdeal.ResidueField) f = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    Nonempty (FactorModLiftData f p gbar hbar) := by
  sorry

/-! ## Finite separable residue-field extensions -/

/-- An étale algebra realizing a prescribed finite separable extension of
the residue field at a prime. -/
structure EtalePrescribedResidueFieldData
    (A : Type u) [CommRing A] (p : PrimeSpectrum A)
    (L : Type v) [Field L] [Algebra p.asIdeal.ResidueField L] where
  S : Type u
  [commRingS : CommRing S]
  [algebraAS : Algebra A S]
  etale : RingHom.Etale (algebraMap A S)
  q : PrimeSpectrum S
  liesOver : PrimeSpectrum.comap (algebraMap A S) q = p
  residueEquiv :
    letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt
        (algebraMap A S) p q liesOver).toAlgebra
    Nonempty (q.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] L)

/-- An étale algebra together with a presentation of a finite separable
extension as a quotient of it.  The compatibility field keeps the interface
independent of a chosen `Algebra A L` instance. -/
structure EtaleSurjectiveExtensionData
    (A k : Type u) (L : Type v)
    [CommRing A] [Field k] [Field L]
    (r : A →+* k) [Algebra k L] where
  S : Type u
  [commRingS : CommRing S]
  [algebraAS : Algebra A S]
  etale : Algebra.Etale A S
  map : S →+* L
  commutes : map.comp (algebraMap A S) = (algebraMap k L).comp r
  surjective : Function.Surjective map

/-- The prime cut out by the quotient map in
`EtaleSurjectiveExtensionData`. -/
def EtaleSurjectiveExtensionData.prime
    {A k : Type u} {L : Type v}
    [CommRing A] [Field k] [Field L]
    {r : A →+* k} [Algebra k L]
    (D : EtaleSurjectiveExtensionData A k L r) :
      @PrimeSpectrum D.S D.commRingS.toCommSemiring :=
  letI := D.commRingS
  letI := D.algebraAS
  ⟨RingHom.ker D.map, RingHom.ker_isPrime D.map⟩

/-- The prime defined by the quotient map contracts to the kernel of the
chosen map from the base ring to the residue field. -/
theorem EtaleSurjectiveExtensionData.comap_prime
    {A k : Type u} {L : Type v}
    [CommRing A] [Field k] [Field L]
    {r : A →+* k} [Algebra k L]
    (D : EtaleSurjectiveExtensionData A k L r) :
    let _ : CommRing D.S := D.commRingS
    let _ : Algebra A D.S := D.algebraAS
    Ideal.comap (algebraMap A D.S) D.prime.asIdeal = RingHom.ker r := by
  let _ := D.commRingS
  let _ := D.algebraAS
  ext a
  change D.map (algebraMap A D.S a) = 0 ↔ r a = 0
  rw [show D.map (algebraMap A D.S a) = algebraMap k L (r a) by
    exact DFunLike.congr_fun D.commutes a]
  simp

/-- The quotient map induces the canonical residue-field ring equivalence. -/
theorem EtaleSurjectiveExtensionData.residueFieldEquiv
    {A k : Type u} {L : Type v}
    [CommRing A] [Field k] [Field L]
    {r : A →+* k} [Algebra k L]
    (D : EtaleSurjectiveExtensionData A k L r) :
    let _ : CommRing D.S := D.commRingS
    let _ : Algebra A D.S := D.algebraAS
    Nonempty (D.prime.asIdeal.ResidueField ≃+* L) := by
  let _ := D.commRingS
  let _ := D.algebraAS
  let q := D.prime
  have hq : q.asIdeal = (⊥ : Ideal L).comap D.map := by
    rfl
  have hbij : Function.Bijective
      (Ideal.ResidueField.map q.asIdeal (⊥ : Ideal L) D.map hq) :=
    RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_surjective D.surjective)
      q.asIdeal (⊥ : Ideal L) hq
  let e₁ : q.asIdeal.ResidueField ≃+*
      (⊥ : Ideal L).ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map q.asIdeal (⊥ : Ideal L) D.map hq) hbij
  let e₂ : L ≃+* (⊥ : Ideal L).ResidueField :=
    Ideal.algEquivResidueFieldOfField (⊥ : Ideal L)
  exact ⟨e₁.trans e₂.symm⟩

/-- The induced residue-field equivalence agrees with the quotient map on
elements coming from the base ring. -/
theorem EtaleSurjectiveExtensionData.residueFieldEquiv_with_baseMap
    {A k : Type u} {L : Type v}
    [CommRing A] [Field k] [Field L]
    {r : A →+* k} [Algebra k L]
    (D : EtaleSurjectiveExtensionData A k L r) :
    let _ : CommRing D.S := D.commRingS
    let _ : Algebra A D.S := D.algebraAS
    ∃ e : D.prime.asIdeal.ResidueField ≃+* L,
      ∀ a : A, e (algebraMap A D.prime.asIdeal.ResidueField a) =
        D.map (algebraMap A D.S a) := by
  let _ := D.commRingS
  let _ := D.algebraAS
  let q := D.prime
  have hq : q.asIdeal = (⊥ : Ideal L).comap D.map := by
    rfl
  have hbij : Function.Bijective
      (Ideal.ResidueField.map q.asIdeal (⊥ : Ideal L) D.map hq) :=
    RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_surjective D.surjective)
      q.asIdeal (⊥ : Ideal L) hq
  let e₁ : q.asIdeal.ResidueField ≃+*
      (⊥ : Ideal L).ResidueField :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map q.asIdeal (⊥ : Ideal L) D.map hq) hbij
  let e₂ : L ≃+* (⊥ : Ideal L).ResidueField :=
    Ideal.algEquivResidueFieldOfField (⊥ : Ideal L)
  refine ⟨e₁.trans e₂.symm, ?_⟩
  intro a
  change e₂.symm (e₁ (algebraMap A q.asIdeal.ResidueField a)) = _
  rw [IsScalarTower.algebraMap_apply A D.S q.asIdeal.ResidueField]
  rw [show e₁ (algebraMap D.S q.asIdeal.ResidueField
      (algebraMap A D.S a)) =
      Ideal.ResidueField.map q.asIdeal (⊥ : Ideal L) D.map hq
        (algebraMap D.S q.asIdeal.ResidueField
          (algebraMap A D.S a)) by rfl]
  rw [Ideal.ResidueField.map_algebraMap]
  rw [← Ideal.algEquivResidueFieldOfField_apply]
  exact (Ideal.algEquivResidueFieldOfField (⊥ : Ideal L)).symm_apply_apply _

/-- The induced residue-field equivalence agrees with the original quotient
map on the base algebra. -/
theorem EtaleSurjectiveExtensionData.residueFieldEquiv_with_algebraMap
    {A : Type u} {L : Type v}
    [CommRing A] [IsLocalRing A] [Field L]
    {r : A →+* (IsLocalRing.ResidueField A)}
    [Algebra (IsLocalRing.ResidueField A) L]
    (D : EtaleSurjectiveExtensionData A (IsLocalRing.ResidueField A) L r) :
    let _ : CommRing D.S := D.commRingS
    let _ : Algebra A D.S := D.algebraAS
    ∃ e : D.prime.asIdeal.ResidueField ≃+* L,
      ∀ a : A, e (algebraMap A D.prime.asIdeal.ResidueField a) =
        D.map (algebraMap A D.S a) := by
  simpa using D.residueFieldEquiv_with_baseMap

/-- A finite separable extension of a residue field is a quotient of an
étale algebra over the local ring. -/
theorem exists_etale_surjective_extension
    {A k : Type u} {L : Type v}
    [CommRing A] [Field k] [Field L]
    (r : A →+* k) (hr : Function.Surjective r)
    [Algebra k L] [Module.Finite k L]
    [Algebra.IsSeparable k L] :
    let _ : Algebra A L := ((algebraMap k L).comp r).toAlgebra
    Nonempty (EtaleSurjectiveExtensionData A k L r) := by
  let _ : Algebra A L := ((algebraMap k L).comp r).toAlgebra
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k L
  let _ : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  have hgen : Algebra.adjoin k ({α} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α), hα,
      IntermediateField.top_toSubalgebra]
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hgen
  have hmin_monic : (minpoly k α).Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral α)
  obtain ⟨f, hfmap, _, hfmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective hr (minpoly k α)) hmin_monic
  let P : StandardEtalePair A :=
    ⟨f, hfmonic, f.derivative, 1, 0, 1, by simp⟩
  have hroot : aeval α f = 0 := by
    rw [aeval_eq_aeval_map (R := A) (T := k) (S := L) rfl, hfmap]
    exact minpoly.aeval k α
  have hderiv : IsUnit (aeval α f.derivative) := by
    apply isUnit_iff_ne_zero.mpr
    rw [aeval_eq_aeval_map (R := A) (T := k) (S := L) rfl,
      ← derivative_map, hfmap]
    exact (Algebra.IsSeparable.isSeparable k α).aeval_derivative_ne_zero
      (minpoly.aeval k α)
  let φ : P.Ring →ₐ[A] L := P.lift α ⟨hroot, hderiv⟩
  have hφ_surjective : Function.Surjective φ := by
    intro y
    obtain ⟨q, hq⟩ := hgen y
    obtain ⟨qA, hqA⟩ := Polynomial.map_surjective r hr q
    have hφ_aeval (z : Polynomial A) :
        φ (aeval P.X z) = aeval α z := by
      change φ.toRingHom (aeval P.X z) = aeval α z
      rw [map_aeval_eq_aeval_map (R := A) (S := P.Ring) (T := A)
        (ψ := φ.toRingHom) (φ := RingHom.id A) ?_]
      · have hX : φ.toRingHom P.X = α := by
          exact P.lift_X α ⟨hroot, hderiv⟩
        rw [hX]
        simp
      · ext a
        simp [φ]
    refine ⟨aeval P.X qA, ?_⟩
    calc
      φ (aeval P.X qA) = aeval α qA := hφ_aeval qA
      _ = aeval α (qA.map r) := by
        exact aeval_eq_aeval_map (R := A) (T := k) (S := L) rfl qA α
      _ = aeval α q := by rw [hqA]
      _ = y := hq
  refine ⟨{
    S := P.Ring
    etale := inferInstance
    map := φ.toRingHom
    commutes := ?_
    surjective := hφ_surjective
  }⟩
  ext a
  exact φ.commutes a

/-- The preceding construction specializes to the residue map of any local
ring. -/
theorem exists_etale_surjective_extension_over_local_ring
    {A : Type u} [CommRing A] [IsLocalRing A]
    (L : Type v) [Field L] [Algebra (IsLocalRing.ResidueField A) L]
    [Module.Finite (IsLocalRing.ResidueField A) L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) L] :
    Nonempty (EtaleSurjectiveExtensionData A (IsLocalRing.ResidueField A) L
      (algebraMap A (IsLocalRing.ResidueField A))) := by
  simpa using
    (exists_etale_surjective_extension
      (A := A) (k := IsLocalRing.ResidueField A) (L := L)
      (algebraMap A (IsLocalRing.ResidueField A))
      IsLocalRing.residue_surjective)

/-- The construction over the local ring at a prime, in the notation used for
residue fields of the original ring. -/
theorem exists_etale_surjective_extension_over_atPrime
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (L : Type v) [Field L] [Algebra p.asIdeal.ResidueField L]
    [Module.Finite p.asIdeal.ResidueField L]
    [Algebra.IsSeparable p.asIdeal.ResidueField L] :
    Nonempty (EtaleSurjectiveExtensionData
      (Localization.AtPrime p.asIdeal) p.asIdeal.ResidueField L
      (algebraMap (Localization.AtPrime p.asIdeal) p.asIdeal.ResidueField)) := by
  simpa using
    (exists_etale_surjective_extension_over_local_ring
      (A := Localization.AtPrime p.asIdeal) L)

/-- A finite separable extension of the residue field at a prime is realized
by an étale algebra over the original ring. -/
theorem exists_etale_prescribed_residue_field
    {A : Type u} [CommRing A] (p : PrimeSpectrum A)
    (L : Type v) [Field L] [Algebra p.asIdeal.ResidueField L]
    [Module.Finite p.asIdeal.ResidueField L]
    [Algebra.IsSeparable p.asIdeal.ResidueField L] :
    Nonempty (EtalePrescribedResidueFieldData A p L) := by
  /-
  The local construction above gives a standard étale presentation over
  `Localization.AtPrime p.asIdeal`.  Choose the finitely many coefficients
  and inverse witnesses occurring in that presentation, clear their
  denominators by one element outside `p`, and descend the pair to
  `Localization.Away s`.  Composition with `A → Localization.Away s` is
  étale.  The quotient map to `L` defines `q`; `comap_prime` identifies its
  contraction, while `residueFieldEquiv_with_baseMap` supplies compatibility
  on `A`.  Naturality of `Ideal.ResidueField.map` upgrades the resulting ring
  equivalence to the displayed algebra equivalence.
  -/
  sorry

end

end Formalization.Books.Algebra.Unit143
