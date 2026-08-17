import Formalization.Books.Algebra.Unit20.Nakayama
import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.Algebra.Unit75.TorGroups
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Commutative Algebra, Chapter 101: Flatness criteria over Artinian rings

The statements in this section use Mathlib's canonical flat, free, projective,
basis, quotient-module, residue-field, localization, and ring-hom flatness
interfaces.  Tor is the canonical construction recorded in Chapter 75.

The short exact sequences and tensor-product maps displayed inside the source
proofs are proof scaffolding for the theorem interfaces below, so they are not
duplicated as unreferenced declarations.
-/

namespace Formalization.Books.Algebra.Unit101

open CategoryTheory
open CategoryTheory.Limits
open Function
open scoped TensorProduct

noncomputable section

universe u

/-! ## Nilpotent local criteria -/

/-- An Artinian local ring has a nilpotent maximal ideal. -/
theorem artinian_local_maximalIdeal_isNilpotent
    {R : Type u} [CommRing R] [IsArtinianRing R] [IsLocalRing R] :
    IsNilpotent (IsLocalRing.maximalIdeal R) :=
  (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance

/- The ideal used in the preparation lemma is the contraction of the extension
   of `I ^ 2` along the given ring map. -/
def prepareIdeal {R R' : Type u} [CommRing R] [CommRing R']
    (φ : R →+* R') (I : Ideal R) : Ideal R :=
  Ideal.comap φ (Ideal.map φ (I ^ 2))

/- Mathlib packages a basis as a structure and does not take its vector
   family as a type parameter.  This predicate records the source's phrase
   that a specified family forms a basis. -/
def IsBasisFamily {R M A : Type u} [Semiring R] [AddCommMonoid M]
    [Module R M] (x : A → M) : Prop :=
  ∃ b : Module.Basis A R M, (b : A → M) = x

/- The source's residue vectors are the images under the canonical quotient
   map of the maximal-ideal multiple of the module. -/
theorem local_artinian_basis_when_flat
    {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [IsLocalRing R] (hmax : IsNilpotent (IsLocalRing.maximalIdeal R))
    (hflat : Module.Flat R M) (x : A → M) :
    IsBasisFamily
        (R := R ⧸ IsLocalRing.maximalIdeal R)
        (M := M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)))
        (fun a =>
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mkQ (x a)) ↔
      IsBasisFamily (R := R) (M := M) x := by
  sorry

theorem local_artinian_characterize_flat
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [IsLocalRing R]
    (hmax : IsNilpotent (IsLocalRing.maximalIdeal R)) :
    List.TFAE [Module.Flat R M, Module.Free R M, Module.Projective R M] := by
  sorry

theorem lift_basis
    {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : IsNilpotent I) (x : A → M)
    (hbasis :
      IsBasisFamily
        (R := R ⧸ I) (M := M ⧸ (I • (⊤ : Submodule R M)))
        (fun a => (I • (⊤ : Submodule R M)).mkQ (x a)))
    (hTor : IsZero
      (Formalization.Books.Algebra.Unit75.Tor
        (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R M) 1)) :
    IsBasisFamily (R := R) (M := M) x := by
  sorry

theorem prepare_lift_flatness
    {R R' M : Type u} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] (φ : R →+* R') (I : Ideal R)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hbase :
      letI : Algebra R R' := φ.toAlgebra
      Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat (R ⧸ prepareIdeal φ I)
      (M ⧸ (prepareIdeal φ I • (⊤ : Submodule R M))) := by
  sorry

theorem lift_flatness
    {R R' M : Type u} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] (φ : R →+* R') (I : Ideal R)
    (hI : IsNilpotent I) (hφ : Injective φ)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hbase :
      letI : Algebra R R' := φ.toAlgebra
      Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat R M := by
  sorry

theorem artinian_variant_local_criterion_flatness
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    Module.Flat R M ↔
      Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) ∧
        IsZero
          (Formalization.Books.Algebra.Unit75.Tor
            (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R M) 1) := by
  sorry

theorem descent_flatness_injective_map_artinian_rings
    {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] [IsArtinianRing R] (φ : R →+* S) (hφ : Injective φ)
    (hflat :
      letI : Algebra R S := φ.toAlgebra
      Module.Flat S (S ⊗[R] M)) :
    Module.Flat R M := by
  sorry

/- The condition in the fibre criterion is the source's assertion that the
   fibre of `M` at `q` is nonzero, with the `S`-action restricted from `S'`. -/
def nontrivialFibreAt
    {S S' M : Type u} [CommRing S] [CommRing S'] [AddCommGroup M]
    [Module S' M] (g : S →+* S') (q : PrimeSpectrum S) : Prop :=
  letI : Module S M := Module.compHom M g
  Nontrivial (M ⊗[S] q.asIdeal.ResidueField)

/- This is the nilpotent fibre criterion.  The comparison warning in the
   source points to the Noetherian, finitely presented, and locally nilpotent
   fibre criteria formalized in the preceding chapter. -/
theorem criterion_flatness_fibre_nilpotent
    {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S']
    [AddCommGroup M] [Module S' M]
    (f : R →+* S) (g : S →+* S') (h : R →+* S')
    (comm : g.comp f = h) (I : Ideal R) (hI : IsNilpotent I)
    (hflat_fibre :
      letI : Module S M := Module.compHom M g
      Module.Flat (S ⧸ (I.map f))
        (M ⧸ ((I.map f) • (⊤ : Submodule S M))))
    (hflat_base :
      letI : Module R M := Module.compHom M h
      Module.Flat R M) :
    (letI : Module S M := Module.compHom M g
     Module.Flat S M) ∧
      ∀ q : PrimeSpectrum S,
        nontrivialFibreAt (M := M) g q →
          RingHom.Flat
            ((algebraMap S (Localization.AtPrime q.asIdeal)).comp f) := by
  sorry

end

end Formalization.Books.Algebra.Unit101
