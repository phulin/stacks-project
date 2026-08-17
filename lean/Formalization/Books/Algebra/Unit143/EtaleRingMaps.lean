import Formalization.Books.Algebra.Unit113.DimensionFormula
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Formalization.Books.Algebra.Unit136.SyntomicMorphisms
import Formalization.Books.Algebra.Unit137.SmoothRingMaps
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.Smooth.StandardSmooth
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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

/-- Étaleness is local on the target for a finite basic-open cover. -/
theorem etale_local_on_target
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (m : ℕ) (g : Fin m → S)
    (hgen : Ideal.span (Set.range g) = (⊤ : Ideal S))
    (hEtale : ∀ i, Algebra.Etale R (Localization.Away (g i))) :
    Algebra.Etale R S := by
  sorry

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
  baseChange : Nonempty (R ⊗[R₀] S₀ ≃ₐ[R] S)

/-- Every étale map is obtained by base change from one whose source is of
finite type over the integers. -/
theorem etale_finite_type_approximation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] :
    Nonempty (EtaleFiniteTypeApproximation R S) := by
  sorry

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
    Nonempty (B' ≃+* Localization (M.map (algebraMap A B)))

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
  kernelBaseChange :
    letI : Algebra A B := AToB.toAlgebra
    Nonempty (B ⊗[A] I ≃ₗ[B] J)

/-- Étaleness lifts across the source's square-zero exact diagram. -/
theorem etale_lift_infinitesimal
    {A A' B B' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    (D : SquareZeroEtaleDiagram A A' B B')
    (h : RingHom.Etale D.AToB) :
    RingHom.Etale D.A'ToB' := by
  sorry

/-! ## The factor-polynomial example -/

abbrev FactorPolynomialBase (n m : ℕ) :=
  Formalization.Books.Algebra.Unit136.FactorPolynomialBase n m

abbrev FactorPolynomialTarget (n m : ℕ) :=
  Formalization.Books.Algebra.Unit136.FactorPolynomialTarget n m

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

/-- The quotient presentation of the universal factor-polynomial map.  This
reexports the canonical presentation constructed in Chapter 136. -/
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

/-- The residue-field map associated to a prime lying over a prime. -/
noncomputable def factorResidueFieldMap
    {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (p : PrimeSpectrum R) (p' : PrimeSpectrum R')
    (hlying : PrimeSpectrum.comap f p' = p) :
    p.asIdeal.ResidueField →+* p'.asIdeal.ResidueField :=
  Formalization.Books.Algebra.Unit113.residueFieldMapAt f p p' hlying

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
    Function.Bijective (factorResidueFieldMap (algebraMap R R') p p' liesOver)
  g : Polynomial R'
  h : Polynomial R'
  factorization : Polynomial.map (algebraMap R R') f =
    (g : Polynomial R') * (h : Polynomial R')
  g_reduces :
    Polynomial.map (algebraMap R' p'.asIdeal.ResidueField) g =
      Polynomial.map (factorResidueFieldMap (algebraMap R R') p p' liesOver) gbar
  h_reduces :
    Polynomial.map (algebraMap R' p'.asIdeal.ResidueField) h =
      Polynomial.map (factorResidueFieldMap (algebraMap R R') p p' liesOver) hbar
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

end

end Formalization.Books.Algebra.Unit143
