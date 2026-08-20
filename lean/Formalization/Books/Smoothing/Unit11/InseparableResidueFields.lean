import Formalization.Books.Algebra.Unit54.EssentiallyFiniteType
import Formalization.Books.Algebra.Unit127.ColimitsAndFinitePresentation
import Formalization.Books.Algebra.Unit134.NaiveCotangentComplex
import Formalization.Books.Algebra.Unit166.GeometricallyRegular
import Formalization.Books.Smoothing.Unit09
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Smooth

/-!
# Smoothing Ring Maps, Chapter 11: Inseparable residue fields

This file records the source's four lemmas in the inseparable-residue-field
section.  The canonical cotangent `H₁`, directed algebra colimits, local
situations, singular ideals, and localization maps are reused from earlier
chapters.  The proof's polynomial and quotient constructions are exposed as
source-facing definitions; theorem proofs are deferred to the proof stage.
-/

namespace Formalization.Books.Smoothing.Unit11

open Formalization.Books.Algebra.Unit127
open Formalization.Books.Algebra.Unit134
open Formalization.Books.Algebra.Unit166
open Formalization.Books.Algebra.Unit03
open Formalization.Books.Smoothing.Unit02
open Formalization.Books.Smoothing.Unit09

noncomputable section

universe u v

/-! ## Common source predicates -/

/-- A convenient proposition for the source's phrase “local Artinian ring”. -/
def IsLocalArtinianRing (R : Type u) [CommRing R] : Prop :=
  IsArtinianRing R ∧ IsLocalRing R

/-- The standard algebraic presentation of an essentially smooth map: an
essentially finite-type map which is formally smooth.  This is Mathlib's
canonical pair of predicates, packaged because the source uses the phrase as
a single adjective. -/
def IsEssentiallySmooth
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  RingHom.EssFiniteType f ∧ RingHom.FormallySmooth f

/-- The positive-characteristic hypothesis used throughout the section. -/
def IsPositiveCharacteristic (k : Type u) [Field k] (p : ℕ) : Prop :=
  0 < p ∧ CharP k p

/-- The finite-dimensionality condition on the degree-one naive cotangent
complex in the helper lemma. -/
def FiniteCotangentH1
    (k K : Type u) [Field k] [Field K] [Algebra k K] : Prop :=
  Module.Finite K (NaiveCotangentH1 k K)

/-- The directed-colimit package for the helper lemma.  The displayed ideal
equality is the source's `m_A Λ = m`, expressed by the canonical map from a
chosen colimit stage to the represented target. -/
structure DirectedLocalArtinianApproximation
    {k Λ : Type u} [CommRing k] [CommRing Λ]
    (f : k →+* Λ) (hΛ : IsLocalArtinianRing Λ)
    extends DirectedAlgebraColimit f where
  stageLocalArtinian : ∀ i,
    IsLocalArtinianRing ((diagram.obj i).right)
  stageEssentiallyFiniteType : ∀ i,
    RingHom.EssFiniteType (diagram.obj i).hom.hom
  stageFlat : ∀ i,
    letI : Preorder index := indexPreorder
    RingHom.Flat (DirectedAlgebraColimit.stageToTarget toDirectedAlgebraColimit i)
  stageMaximalIdeal : ∀ i,
    letI : Preorder index := indexPreorder
    letI : IsLocalRing ((diagram.obj i).right) := (stageLocalArtinian i).2
    letI : IsLocalRing Λ := hΛ.2
    Ideal.map (DirectedAlgebraColimit.stageToTarget toDirectedAlgebraColimit i)
        (IsLocalRing.maximalIdeal ((diagram.obj i).right)) =
      IsLocalRing.maximalIdeal Λ

/-! ## The helper lemma -/

/-- A field of characteristic `p` and an Artinian local algebra with finite
cotangent `H₁` admit the source's filtered colimit by local Artinian stages. -/
theorem helper
    {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ]
    [IsArtinianRing Λ] [IsLocalRing Λ]
    (p : ℕ) (hp : IsPositiveCharacteristic k p)
    (hH1 : FiniteCotangentH1 k (IsLocalRing.ResidueField Λ)) :
    Nonempty (DirectedLocalArtinianApproximation (algebraMap k Λ)
      ⟨inferInstance, inferInstance⟩) := by
  sorry

/-- The exact Jacobi--Zariski package used in the proof of `helper`, with the
canonical `H₁` and Kähler differential maps.  The first term is the
source's `H₁(L_{K/k})`, and the four exactness/surjectivity clauses are the
Mathlib form of the displayed sequence after taking `F_p ⊂ k ⊂ K`. -/
def JacobiZariskiSequence
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    [Algebra (ZMod p) k] [Algebra (ZMod p) K]
    [IsScalarTower (ZMod p) k K] : Prop :=
  Function.Exact (Algebra.H1Cotangent.map (ZMod p) k K K)
      (Algebra.H1Cotangent.δ (ZMod p) k K) ∧
    Function.Exact (Algebra.H1Cotangent.δ (ZMod p) k K)
      (KaehlerDifferential.mapBaseChange (ZMod p) k K) ∧
    Function.Exact (KaehlerDifferential.mapBaseChange (ZMod p) k K)
      (KaehlerDifferential.map (ZMod p) k K K) ∧
    Function.Surjective (KaehlerDifferential.map (ZMod p) k K K)

/-! ## Quotients and local factorizations -/

/-- The localization of a ring at a prime, quotiented by the extension of a
power of that prime. -/
abbrev LocalizedPowerQuotient
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] (n : ℕ) : Type u :=
  Localization p.primeCompl ⧸
    Ideal.map (algebraMap R (Localization p.primeCompl)) (p ^ n)

noncomputable instance localizedPowerQuotientCommRing
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (n : ℕ) :
    CommRing (LocalizedPowerQuotient R p n) :=
  letI : CommRing (Localization p.primeCompl) := inferInstance
  Ideal.Quotient.commRing _

/-- The canonical quotient map from the localized ring to its local power
quotient. -/
def localizedPowerQuotientMk
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (n : ℕ) :
    Localization p.primeCompl →+* LocalizedPowerQuotient R p n :=
  Ideal.Quotient.mk _

/-- The canonical map on localizations induced by a ring map and a prime in
the target.  It is the earlier chapter's `Localization.localRingHom`, with
the contracted prime made explicit. -/
noncomputable def localizedAtPrimeMap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) :
    Localization (q.asIdeal.comap f).primeCompl →+*
      Localization q.asIdeal.primeCompl := by
  apply IsLocalization.map (Q := Localization q.asIdeal.primeCompl)
    (R := R) (P := S) (M := (q.asIdeal.comap f).primeCompl)
    (T := q.asIdeal.primeCompl) f
  intro x hx
  change f x ∉ q.asIdeal
  intro hfx
  exact hx hfx

/-- The same localization map with a separately named contracted prime. -/
noncomputable def localizedAtPrimeMapFrom
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S)
    (p : Ideal R) [p.IsPrime] (hp : p = q.asIdeal.comap f) :
    Localization p.primeCompl →+* Localization q.asIdeal.primeCompl := by
  subst p
  exact localizedAtPrimeMap f q

/-- A factorization through a local Artinian ring.  The two `IsLocalHom`
fields make “homomorphisms of local Artinian rings” explicit. -/
structure LocalArtinianFactorization
    {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (hT : IsLocalArtinianRing T) where
  D : Type u
  [commRingD : CommRing D]
  localArtinianD : IsLocalArtinianRing D
  sourceToD : R →+* D
  DToTarget : D →+* T
  sourceToD_local : IsLocalHom sourceToD
  DToTarget_local : IsLocalHom DToTarget
  essentiallySmooth : IsEssentiallySmooth sourceToD
  flat : RingHom.Flat DToTarget
  factorization : DToTarget.comp sourceToD = f

noncomputable instance LocalArtinianFactorization.commRingDInstance
    {R T : Type u} [CommRing R] [CommRing T]
    {f : R →+* T} {hT : IsLocalArtinianRing T}
    (s : LocalArtinianFactorization f hT) : CommRing s.D :=
  s.commRingD

/-- A solution modulo `q^n`, including the canonical compatibility with the
unquotiented localization map and containment of the prescribed finite set. -/
structure SolutionModuloFactorization
    {k Λ : Type u} {m : ℕ} [Field k] [CommRing Λ] [Algebra k Λ]
    (φ : MvPolynomial (Fin m) k →+* Λ) (q : PrimeSpectrum Λ)
    (p : Ideal (MvPolynomial (Fin m) k)) [p.IsPrime]
    (hp : p = q.asIdeal.comap φ)
    (n : ℕ) (E : Set (LocalizedPowerQuotient Λ q.asIdeal n)) where
  targetLocalArtinian : IsLocalArtinianRing (LocalizedPowerQuotient Λ q.asIdeal n)
  baseMap :
    LocalizedPowerQuotient (MvPolynomial (Fin m) k) p n →+*
      LocalizedPowerQuotient Λ q.asIdeal n
  factor : LocalArtinianFactorization baseMap targetLocalArtinian
  compatibleWithLocalization :
    baseMap.comp (localizedPowerQuotientMk p n) =
      (localizedPowerQuotientMk q.asIdeal n).comp
        (localizedAtPrimeMapFrom φ q p hp)
  contains : E ⊆ Set.range factor.DToTarget

/-- The image of an element of `Λ` in the local power quotient at `q`. -/
def localizedPowerClass
    {Λ : Type u} [CommRing Λ] (q : PrimeSpectrum Λ) (n : ℕ) (x : Λ) :
    LocalizedPowerQuotient Λ q.asIdeal n :=
  localizedPowerQuotientMk q.asIdeal n
    (algebraMap Λ (Localization q.asIdeal.primeCompl) x)

/-- The conclusion of the source's `solution-modulo` lemma. -/
theorem solution_modulo
    {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (hΛ : IsGeometricallyRegular k Λ)
    (q : PrimeSpectrum Λ) (n : ℕ) (hn : 1 ≤ n)
    (E : Finset (LocalizedPowerQuotient Λ q.asIdeal n)) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →+* Λ)
      (p : Ideal (MvPolynomial (Fin m) k))
      (hp : p = q.asIdeal.comap φ) (hpprime : p.IsPrime),
      letI : p.IsPrime := hpprime
      Ideal.map ((algebraMap Λ (Localization q.asIdeal.primeCompl)).comp φ) p =
          Ideal.map (algebraMap Λ (Localization q.asIdeal.primeCompl)) q.asIdeal ∧
        RingHom.Flat (localizedAtPrimeMapFrom φ q p hp) ∧
        Nonempty (SolutionModuloFactorization φ q p hp n (E : Set _)) := by
  sorry

/-- An enlargement of a solution modulo `q^n`; this is the source's
factorization `D → D' → Λ_q/q^n`, with the power of the prescribed element
represented in the image of `D'`. -/
structure EnlargedSolutionModulo
    {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ]
    {m : ℕ} {φ : MvPolynomial (Fin m) k →+* Λ} {q : PrimeSpectrum Λ}
    {p : Ideal (MvPolynomial (Fin m) k)} [p.IsPrime]
    (hp : p = q.asIdeal.comap φ)
    {n : ℕ} {E : Set (LocalizedPowerQuotient Λ q.asIdeal n)}
    (s : SolutionModuloFactorization φ q p hp n E) (lambda : Λ) (r : ℕ) where
  D' : Type u
  [commRingD' : CommRing D']
  localArtinianD' : IsLocalArtinianRing D'
  DToD' : s.factor.D →+* D'
  DToD'_local : IsLocalHom DToD'
  D'ToTarget : D' →+* LocalizedPowerQuotient Λ q.asIdeal n
  D'ToTarget_local : IsLocalHom D'ToTarget
  essentiallySmooth : IsEssentiallySmooth DToD'
  flat : RingHom.Flat D'ToTarget
  factorization : D'ToTarget.comp DToD' = s.factor.DToTarget
  power_mem_range :
    ∃ x : D', D'ToTarget x = localizedPowerClass q n (lambda ^ r)

/-- The source's enlargement lemma for a prescribed element outside the prime. -/
theorem enlarge_solution_modulo
    {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (hΛ : IsGeometricallyRegular k Λ)
    {m : ℕ} {φ : MvPolynomial (Fin m) k →+* Λ} {q : PrimeSpectrum Λ}
    {p : Ideal (MvPolynomial (Fin m) k)} [p.IsPrime]
    {hp : p = q.asIdeal.comap φ}
    {n : ℕ} {E : Set (LocalizedPowerQuotient Λ q.asIdeal n)}
    (s : SolutionModuloFactorization φ q p hp n E)
    (lambda : Λ) (hlambda : lambda ∉ q.asIdeal) :
    ∃ r : ℕ, 0 < r ∧ Nonempty (EnlargedSolutionModulo hp s lambda r) := by
  sorry

/-! ## Polynomial and annihilator data from the proof of `resolve-general` -/

/-- The finite positive-power containment used to choose `N`. -/
def PowerContainment
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] (s : LocalSituation R A Λ) (N : ℕ) : Prop :=
  Ideal.map (algebraMap Λ (Localization s.q.asIdeal.primeCompl))
      (s.q.asIdeal ^ N) ≤
    Ideal.map (algebraMap Λ (Localization s.q.asIdeal.primeCompl))
      (Ideal.map s.map (singularIdeal R A))

/-- Finite generators for the singular ideal of the intermediate algebra. -/
def SingularIdealGenerators
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] (s : LocalSituation R A Λ) (t : ℕ)
    (a : Fin t → A) : Prop :=
  singularIdeal R A = Ideal.span (Set.range a)

/-- The dimension witness for the localized target. -/
def LocalDimensionWitness
    {R A Λ : Type u} [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] (s : LocalSituation R A Λ) (d : ℕ) : Prop :=
  ringKrullDim (Localization s.q.asIdeal.primeCompl) = d

/-- The polynomial ring in the `x_i` and `z_ij` variables of the standardizer
construction. -/
abbrev StandardizerPolynomial (A : Type u) [CommRing A]
    (d t : ℕ) : Type u :=
  MvPolynomial (Fin d ⊕ (Fin d × Fin t)) A

/-- The relation `x_i^(2N) - Σ_j z_ij a_j`. -/
def standardizerRelation
    {A : Type u} [CommRing A] (N : ℕ) (d t : ℕ)
    (a : Fin t → A) (i : Fin d) : StandardizerPolynomial A d t :=
  MvPolynomial.X (Sum.inl i) ^ (2 * N) -
    ∑ j : Fin t,
      MvPolynomial.C (a j) * MvPolynomial.X (Sum.inr (i, j))

/-- The standardizer ring `B` from the source's displayed presentation. -/
abbrev StandardizerRing
    {A : Type u} [CommRing A] (N d t : ℕ) (a : Fin t → A) : Type u :=
  StandardizerPolynomial A d t ⧸
    Ideal.span (Set.range (standardizerRelation N d t a))

/-- The canonical map from the standardizer to `Λ` obtained by evaluating the
named `x_i` and `z_ij`, subject to the displayed defining relations. -/
def standardizerMap
    {A Λ : Type u} [CommRing A] [CommRing Λ]
    (f : A →+* Λ) (N d t : ℕ) (a : Fin t → A)
    (x : Fin d → Λ) (z : Fin d → Fin t → Λ)
    (hrel : ∀ i, x i ^ (2 * N) =
      ∑ j : Fin t, f (a j) * z i j) :
    StandardizerRing N d t a →+* Λ := by
  let e : StandardizerPolynomial A d t →+* Λ :=
    MvPolynomial.eval₂Hom f (fun v =>
      match v with
      | Sum.inl i => x i
      | Sum.inr ij => z ij.1 ij.2)
  apply Ideal.Quotient.lift _ e
  intro y hy
  have hker : Ideal.span (Set.range (standardizerRelation N d t a)) ≤
      RingHom.ker e := by
    apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    apply RingHom.mem_ker.mpr
    change e (standardizerRelation N d t a i) = 0
    simp only [standardizerRelation, map_sub, map_pow, map_sum, map_mul,
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
    simpa [e] using (sub_eq_zero.mpr (hrel i))
  have hy' : y ∈ RingHom.ker e := hker hy
  exact RingHom.mem_ker.mp hy'

/-- Strict-standard powers of the `x_i` coordinates in the improved ring. -/
def StrictStandardCoordinatePowers
    {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    (d c : ℕ) (x : Fin d → C) : Prop :=
  ∀ i, IsStrictlyStandard R C (x i ^ c)

/-- The source's `γ_i = π_i t_i` in the polynomial ring in `y` and `t`. -/
abbrev ParameterPolynomial (k : Type u) [CommRing k] (m d : ℕ) : Type u :=
  MvPolynomial (Fin m ⊕ Fin d) k

def gamma
    {k : Type u} [CommRing k] {m d : ℕ}
    (π : Fin d → MvPolynomial (Fin m) k) (i : Fin d) :
    ParameterPolynomial k m d :=
  MvPolynomial.rename (fun j => Sum.inl j) (π i) *
    MvPolynomial.X (Sum.inr i)

/-- The numerical choices `n = N + d c` and `e = 8 c` made in the final
resolution argument. -/
def ResolutionParameters (N d c n e : ℕ) : Prop :=
  n = N + d * c ∧ e = 8 * c

/-- The ideal generated by a fixed power of a finite sequence. -/
def IdealOfPowers
    {R : Type u} [CommRing R] {d : ℕ} (x : Fin d → R) (e : ℕ) : Ideal R :=
  Ideal.span (Set.range (fun i => x i ^ e))

/-- The ideal `I = (γ₁ᵉ, ..., γ_dᵉ)` in the auxiliary polynomial ring. -/
def AuxiliaryPowerIdeal
    {k : Type u} [CommRing k] {m d : ℕ}
    (π : Fin d → MvPolynomial (Fin m) k) (e : ℕ) :
    Ideal (ParameterPolynomial k m d) :=
  IdealOfPowers (fun i => gamma π i) e

/-- The ideal `J = (π₁ᵉ, ..., π_dᵉ)` in the original polynomial ring. -/
def ParameterPowerIdeal
    {k : Type u} [CommRing k] {m d : ℕ}
    (π : Fin d → MvPolynomial (Fin m) k) (e : ℕ) :
    Ideal (MvPolynomial (Fin m) k) :=
  IdealOfPowers π e

/-- The map `R → Λ` sending the `y` variables through `φ` and the `t_i` to
the selected elements `δ_i`. -/
def parameterRingMap
    {k Λ : Type u} [CommRing k] [CommRing Λ] {m d : ℕ}
    (φ : MvPolynomial (Fin m) k →+* Λ) (δ : Fin d → Λ) :
    ParameterPolynomial k m d →+* Λ :=
  let coeff : k →+* Λ := φ.comp (algebraMap k (MvPolynomial (Fin m) k))
  MvPolynomial.eval₂Hom coeff (fun i =>
    match i with
    | Sum.inl j => φ (MvPolynomial.X j)
    | Sum.inr j => δ j)

/-- The inverse image `r` of the target prime in the auxiliary polynomial
ring. -/
def resolutionPrimeIdeal
    {k Λ : Type u} [CommRing k] [CommRing Λ] {m d : ℕ}
    (φ : MvPolynomial (Fin m) k →+* Λ) (δ : Fin d → Λ)
    (q : Ideal Λ) : Ideal (ParameterPolynomial k m d) :=
  q.comap (parameterRingMap φ δ)

/-- The source's finite set `E` of target classes, retained as a named
source-facing piece of the numerical setup. -/
def ResolutionFiniteSet
    {Λ : Type u} [CommRing Λ] (q : PrimeSpectrum Λ) (n : ℕ) :
    Type u := Finset (LocalizedPowerQuotient Λ q.asIdeal n)

/-- The ideal generated by the `e`-th powers of the preceding members of a
finite sequence. -/
def prefixPowerIdealOfExponent
    {R : Type u} [CommRing R] {d : ℕ} (π : Fin d → R) (e : ℕ)
    (i : Fin d) : Ideal R :=
  Ideal.span {x | ∃ j : Fin d, j.val < i.val ∧ x = π j ^ e}

/-- The source's annihilator equality after quotienting by preceding powers. -/
def PrefixAnnihilatorEqualityAtExponent
    {R : Type u} [CommRing R] {d : ℕ} (π : Fin d → R) (e : ℕ)
    (i : Fin d) : Prop :=
  let Q := R ⧸ prefixPowerIdealOfExponent π e i
  let x : Q := Ideal.Quotient.mk _ (π i)
  annihilatorOf (R := Q) (M := Q) x =
    annihilatorOf (R := Q) (M := Q) (x ^ 2)

/-- The target version of the preceding annihilator equality. -/
def TargetPrefixAnnihilatorEqualityAtExponent
    {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    {d : ℕ} (π : Fin d → R) (e : ℕ) (i : Fin d) : Prop :=
  let Q := Λ ⧸ Ideal.map (algebraMap R Λ)
      (prefixPowerIdealOfExponent π e i)
  let x : Q := Ideal.Quotient.mk _ (algebraMap R Λ (π i))
  annihilatorOf (R := Q) (M := Q) x =
    annihilatorOf (R := Q) (M := Q) (x ^ 2)

/-- The three conclusions attached to the source's recursively chosen
`δ_i`, including the relation, annihilator, and membership in the enlarged
Artinian stage. -/
structure DeltaWitness
    {A Λ : Type u} [CommRing A] [CommRing Λ]
    {t d : ℕ} (a : Fin t → A) (f : A →+* Λ)
    (q : PrimeSpectrum Λ) (N e n : ℕ) (π : Fin d → Λ)
    (D' : Type u) [CommRing D'] where
  localArtinianD' : IsLocalArtinianRing D'
  stageMap : D' →+* LocalizedPowerQuotient Λ q.asIdeal n
  stageMap_local : IsLocalHom stageMap
  stageMap_flat : RingHom.Flat stageMap
  δ : Fin d → Λ
  lambda : Fin d → Fin t → Λ
  δ_not_mem : ∀ i, δ i ∉ q.asIdeal
  relation : ∀ i,
    (δ i * π i) ^ (2 * N) = ∑ j, f (a j) * lambda i j
  annihilator : ∀ i,
    TargetPrefixAnnihilatorEqualityAtExponent
      (R := Λ) (Λ := Λ) (fun j => δ j * π j) e i
  stage_contains_lambda : ∀ i j, ∃ x : D',
    stageMap x = localizedPowerClass q n (lambda i j)
  stage_contains_delta : ∀ i, ∃ x : D',
    stageMap x = localizedPowerClass q n (δ i)

/-- The source's final local resolution theorem in the inseparable case. -/
theorem resolve_general
    {k A Λ : Type u} [Field k] [CommRing A] [CommRing Λ]
    [Algebra k A] [Algebra k Λ] [IsNoetherianRing Λ]
    (s : LocalSituation k A Λ) (p : ℕ)
    (hp : IsPositiveCharacteristic k p)
    (hΛ : IsGeometricallyRegular k Λ)
    (hq : Ideal.IsMinimalPrime (localDefect s) s.q.asIdeal) :
    CanBeResolved s := by
  sorry

end
end Formalization.Books.Smoothing.Unit11
