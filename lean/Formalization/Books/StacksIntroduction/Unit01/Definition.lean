import Formalization.Books.StacksIntroduction.Unit01.FibreProducts
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Etale.Field

/-!
# Introducing Algebraic Stacks, Chapter 1: the definition

This file spells out the descent, representability, and smooth-cover clauses
in the source definition.  Descent data are indexed by an actual Mathlib
étale cover; the overlap witnesses and their cocycle are kept as explicit
isomorphisms of the family interface from the preceding sections.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

namespace Formalization.Books.StacksIntroduction.Unit01

/-! ### Étale descent data -/

/-- Local elliptic curves and overlap witnesses for an étale cover. -/
structure EtaleEllipticDescentData {S : Scheme.{u}}
    (𝒰 : S.Cover.{u} Scheme.etalePrecoverage) where
  localCurve : ∀ i : 𝒰.I₀, ModuliPoint (𝒰.X i)
  witness : ∀ {T : Scheme.{u}} (i j : 𝒰.I₀)
    (p_i : T ⟶ 𝒰.X i) (p_j : T ⟶ 𝒰.X j),
      p_i ≫ 𝒰.f i = p_j ≫ 𝒰.f j →
      EllipticCurveIso ((localCurve i).baseChange p_i)
        ((localCurve j).baseChange p_j)
  /-- Overlap witnesses are stable under pullback along test-scheme maps. -/
  witness_natural : ∀ {T T' : Scheme.{u}} (i j : 𝒰.I₀)
    (p_i : T ⟶ 𝒰.X i) (p_j : T ⟶ 𝒰.X j) (q : T' ⟶ T)
    (h_ij : p_i ≫ 𝒰.f i = p_j ≫ 𝒰.f j)
    (h_ij' : (q ≫ p_i) ≫ 𝒰.f i = (q ≫ p_j) ≫ 𝒰.f j),
    (EllipticCurveIso.baseChange_assoc (localCurve i) p_i q).trans
      (((witness i j p_i p_j h_ij).baseChange q).trans
        (EllipticCurveIso.baseChange_assoc (localCurve j) p_j q).symm) =
      witness i j (q ≫ p_i) (q ≫ p_j) h_ij'
  cocycle : ∀ {T : Scheme.{u}} (i j k : 𝒰.I₀)
    (p_i : T ⟶ 𝒰.X i) (p_j : T ⟶ 𝒰.X j) (p_k : T ⟶ 𝒰.X k)
    (h_ij : p_i ≫ 𝒰.f i = p_j ≫ 𝒰.f j)
    (h_jk : p_j ≫ 𝒰.f j = p_k ≫ 𝒰.f k)
    (h_ik : p_i ≫ 𝒰.f i = p_k ≫ 𝒰.f k),
    (witness i j p_i p_j h_ij).trans (witness j k p_j p_k h_jk) =
      witness i k p_i p_k h_ik

/-- Compare a pulled-back global family with a local family on a cover member. -/
noncomputable def descentComparison {S : Scheme.{u}}
    {𝒰 : S.Cover.{u} Scheme.etalePrecoverage}
    (D : EtaleEllipticDescentData 𝒰) (curve : ModuliPoint S)
    (local_iso : ∀ i : 𝒰.I₀,
      EllipticCurveIso (curve.baseChange (𝒰.f i)) (D.localCurve i))
    {T : Scheme.{u}} (i : 𝒰.I₀) (p_i : T ⟶ 𝒰.X i) :
    EllipticCurveIso (curve.baseChange (p_i ≫ 𝒰.f i))
      ((D.localCurve i).baseChange p_i) :=
  (EllipticCurveIso.baseChange_assoc curve (𝒰.f i) p_i).trans
    ((local_iso i).baseChange p_i)

/-- The overlap witness induced by a global family and its local identifications. -/
noncomputable def descentInducedWitness {S : Scheme.{u}}
    {𝒰 : S.Cover.{u} Scheme.etalePrecoverage}
    (D : EtaleEllipticDescentData 𝒰) (curve : ModuliPoint S)
    (local_iso : ∀ i : 𝒰.I₀,
      EllipticCurveIso (curve.baseChange (𝒰.f i)) (D.localCurve i))
    {T : Scheme.{u}} (i j : 𝒰.I₀)
    (p_i : T ⟶ 𝒰.X i) (p_j : T ⟶ 𝒰.X j)
    (h_ij : p_i ≫ 𝒰.f i = p_j ≫ 𝒰.f j) :
    EllipticCurveIso ((D.localCurve i).baseChange p_i)
      ((D.localCurve j).baseChange p_j) :=
  (descentComparison D curve local_iso i p_i).symm.trans
    ((EllipticCurveIso.baseChange_eq curve h_ij).trans
      (descentComparison D curve local_iso j p_j))

/-- A global family and its local identifications. -/
structure EtaleEllipticDescentRealization {S : Scheme.{u}}
    {𝒰 : S.Cover.{u} Scheme.etalePrecoverage}
    (D : EtaleEllipticDescentData 𝒰) where
  curve : ModuliPoint S
  local_iso : ∀ i : 𝒰.I₀,
    EllipticCurveIso (curve.baseChange (𝒰.f i)) (D.localCurve i)
  recovery : ∀ {T : Scheme.{u}} (i j : 𝒰.I₀)
    (p_i : T ⟶ 𝒰.X i) (p_j : T ⟶ 𝒰.X j)
    (h_ij : p_i ≫ 𝒰.f i = p_j ≫ 𝒰.f j),
    descentInducedWitness D curve local_iso i j p_i p_j h_ij =
      D.witness i j p_i p_j h_ij

/-- An isomorphism between two realizations compatible with their local identifications. -/
structure EtaleEllipticDescentIso {S : Scheme.{u}}
    {𝒰 : S.Cover.{u} Scheme.etalePrecoverage}
    {D : EtaleEllipticDescentData 𝒰}
    (R R' : EtaleEllipticDescentRealization D) where
  underlying : EllipticCurveIso R.curve R'.curve
  compatible : ∀ i : 𝒰.I₀,
    (R.local_iso i).symm.trans
        ((underlying.baseChange (𝒰.f i)).trans (R'.local_iso i)) =
      EllipticCurveIso.refl (D.localCurve i)

/-- Existence of exactly one compatible isomorphism between realizations. -/
def UniqueUpToUniqueIso {S : Scheme.{u}}
    {𝒰 : S.Cover.{u} Scheme.etalePrecoverage}
    {D : EtaleEllipticDescentData 𝒰}
    (R R' : EtaleEllipticDescentRealization D) : Prop :=
  ∃ φ : EtaleEllipticDescentIso R R',
    ∀ ψ : EtaleEllipticDescentIso R R', ψ = φ

/-- The source's sheaf/descent condition for elliptic-curve objects. -/
def HasEtaleDescentForObjects : Prop :=
  ∀ {S : Scheme.{u}} (𝒰 : S.Cover.{u} Scheme.etalePrecoverage)
    (D : EtaleEllipticDescentData 𝒰),
    Nonempty (EtaleEllipticDescentRealization D) ∧
      ∀ R R' : EtaleEllipticDescentRealization D, UniqueUpToUniqueIso R R'

/-! ### The three clauses of algebraicity -/

/-- The representability/key-fact clause of the source definition. -/
def HasEllipticModuliKeyFact : Prop :=
  ∀ {S S' : Scheme.{u}} (E : ModuliPoint S) (E' : ModuliPoint S'),
    Nonempty (FiberProductPresentation E E')

/-- The key fact is exactly the representability theorem from the preceding section. -/
theorem ellipticModuli_keyFact : HasEllipticModuliKeyFact := by
  intro S S' E E'
  exact exists_fiberProductPresentation E E'

/-- The definition of an algebraic moduli object in the source. -/
def IsAlgebraicEllipticModuli : Prop :=
  HasEtaleDescentForObjects.{u} ∧
    HasEllipticModuliKeyFact.{u} ∧
      ∃ (S : Scheme.{u}) (E : ModuliPoint S),
        IsSmoothModuliMorphism E ∧ IsSurjectiveModuliMorphism E

/-- The chapter's algebraicity assertion, with all three clauses visible. -/
theorem ellipticModuli_isAlgebraicStack : IsAlgebraicEllipticModuli := by
  sorry

/-! ### The finite Galois descent example -/

/-- The Galois group in Mathlib's `AlgEquiv` form. -/
abbrev GaloisGroup (K L : Type u) [Field K] [Field L] [Algebra K L] :=
  L ≃ₐ[K] L

/-- The map `Spec L ⟶ Spec K` attached to a finite Galois extension. -/
def galoisCover {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Scheme.Spec.obj (Opposite.op (CommRingCat.of L)) ⟶
      Scheme.Spec.obj (Opposite.op (CommRingCat.of K)) :=
  Scheme.Spec.map (CommRingCat.ofHom (algebraMap K L)).op

/-- A finite Galois field extension gives an étale cover of schemes. -/
theorem galoisCover_is_etale {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Etale (galoisCover (K := K) (L := L)) ∧
      Surjective (galoisCover (K := K) (L := L)) := by
  dsimp [galoisCover]
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  constructor
  · rw [CommRingCat.hom_ofHom]
    rw [RingHom.etale_algebraMap]
    exact ⟨Algebra.FormallyEtale.of_isSeparable K L,
      (Algebra.FinitePresentation.of_finiteType (R := K) (A := L)).mp inferInstance⟩
  · rw [surjective_iff]
    change ∀ x : PrimeSpectrum K, ∃ y : PrimeSpectrum L,
      PrimeSpectrum.comap (algebraMap K L) y = x
    exact (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp
      ((RingHom.faithfullyFlat_algebraMap_iff).2 inferInstance)).2

/-- Applying a field automorphism to the coefficients of a Weierstrass curve. -/
def galoisTwist {K L : Type u} [Field K] [Field L] [Algebra K L]
    (W : WeierstrassCurve L) (σ : GaloisGroup K L) : WeierstrassCurve L :=
  W.map σ.toRingHom

/-- Weierstrass-equation data carrying the Galois descent cocycle. -/
structure WeierstrassGaloisDescentData {K L : Type u}
    [Field K] [Field L] [Algebra K L]
    (W : WeierstrassCurve L) where
  coordinate : GaloisGroup K L → WeierstrassCurve.VariableChange L
  identifies : ∀ σ : GaloisGroup K L,
    coordinate σ • W = galoisTwist W σ
  cocycle : ∀ σ τ : GaloisGroup K L,
    (coordinate τ).map σ.toRingHom * coordinate σ = coordinate (τ * σ)

/-- Descent of a Weierstrass curve to the ground field, up to a coordinate change. -/
def WeierstrassCurveDescends {K L : Type u} [Field K] [Field L] [Algebra K L]
    (W : WeierstrassCurve L) : Prop :=
  ∃ W₀ : WeierstrassCurve K, ∃ C : WeierstrassCurve.VariableChange L,
    C • W₀.baseChange L = W

/-- The finite Galois descent conclusion in the Weierstrass presentation. -/
theorem weierstrass_galois_descent
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {W : WeierstrassCurve L}
    (D : WeierstrassGaloisDescentData (K := K) W) :
    WeierstrassCurveDescends (K := K) W := by
  sorry

/-!
The source explicitly raises the `σ` versus `σ⁻¹` convention when describing
coefficient twisting.  The definition above fixes the convention by using
the ring homomorphism `σ.toRingHom`; changing conventions produces the
equivalent inverse-indexed cocycle.
-/

end Formalization.Books.StacksIntroduction.Unit01
