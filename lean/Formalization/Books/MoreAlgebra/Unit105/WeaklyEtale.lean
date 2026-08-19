import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.Algebra.Unit75.TorGroups
import Formalization.Books.Algebra.Unit153
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.PurelyInseparable
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
This file records the definitions and theorem interfaces in the source section.
The weakly étale predicate itself is Mathlib's canonical `Algebra.WeaklyEtale`
class.  The two source predicates that do not have a canonical project API,
weak dimension and absolute flatness of a ring, are defined below.
-/

namespace Formalization.Books.MoreAlgebra.Unit105

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u v

/-! ## Definitions -/

/- The source quantifies over all modules.  As usual for a fixed Lean universe,
  this records the equivalent property for modules in the ambient universe. -/
def AbsolutelyFlatRing (A : Type u) [CommRing A] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M], Module.Flat A M

/- Tor is the canonical construction from the preceding Tor formalization. -/
def HasTorDimensionLE {A : Type u} [CommRing A]
    (M : ModuleCat.{u} A) (d : ℕ) : Prop :=
  ∀ (N : ModuleCat.{u} A) (n : ℕ), d < n →
    IsZero (Formalization.Books.Algebra.Unit75.Tor M N n)

def WeakDimensionLE (A : Type u) [CommRing A] (d : ℕ) : Prop :=
  ∀ (M : ModuleCat.{u} A), HasTorDimensionLE M d

/- A filtered-colimit presentation is used for the two source statements about
  filtered colimits.  The target is allowed to be isomorphic to the colimit,
  which is the invariant formulation in `AlgCat`. -/
structure FilteredColimitPresentation
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Type v} [Category J] [IsFiltered J]
    (F : J ⥤ CommAlgCat A) (c : Cocone F) (P : J → Prop) : Prop where
  isColimit : Nonempty (IsColimit c)
  stage : ∀ j : J, P j
  targetIso : Nonempty (c.pt ≅ CommAlgCat.of A B)

def IsFilteredColimitOfWeaklyEtale
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Type v} [Category J] [IsFiltered J]
    (F : J ⥤ CommAlgCat A) (c : Cocone F) : Prop :=
  FilteredColimitPresentation A B F c (fun j => Algebra.WeaklyEtale A (F.obj j))

def IsFilteredColimitOfEtale
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Type v} [Category J] [IsFiltered J]
    (F : J ⥤ CommAlgCat A) (c : Cocone F) : Prop :=
  FilteredColimitPresentation A B F c (fun j => Algebra.Etale A (F.obj j))

/- A ring-theoretic form of the cartesian square in the valuation-ring lemma. -/
structure RingPullbackSquare (A K V L : Type u)
    [CommRing A] [CommRing K] [CommRing V] [CommRing L] where
  aK : A →+* K
  aV : A →+* V
  KL : K →+* L
  VL : V →+* L
  isPullback : CategoryTheory.IsPullback
    (CommRingCat.ofHom aK) (CommRingCat.ofHom aV)
    (CommRingCat.ofHom KL) (CommRingCat.ofHom VL)

/- Residue-field maps are canonical once the prime is known to lie over the
  source prime. -/
noncomputable def residueFieldMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : p.asIdeal = q.asIdeal.comap (algebraMap A B)) :
    p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
  Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap A B) hq

def ResidueFieldExtensionIsSeparableAlgebraic
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : p.asIdeal = q.asIdeal.comap (algebraMap A B)) : Prop :=
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (residueFieldMap p q hq).toAlgebra
  Algebra.IsAlgebraic p.asIdeal.ResidueField q.asIdeal.ResidueField ∧
    Algebra.IsSeparable p.asIdeal.ResidueField q.asIdeal.ResidueField

/-! ## Basic flatness and weakly étale properties -/

theorem localization_isWeaklyEtale
    (A : Type u) [CommRing A] (S : Submonoid A) :
    Algebra.WeaklyEtale A (Localization S) := by
  sorry

theorem etale_isWeaklyEtale
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] : Algebra.WeaklyEtale A B := by
  infer_instance

theorem weaklyEtale_key
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hflat : RingHom.Flat
      (Algebra.TensorProduct.lmul' A (S := B)).toRingHom)
    {N : Type u} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] (hN : Module.Flat A N) : Module.Flat B N := by
  sorry

theorem weakDimensionLE_of_weaklyEtale
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.WeaklyEtale A B] (d : ℕ)
    (hA : WeakDimensionLE A d) : WeakDimensionLE B d := by
  sorry

theorem absolutelyFlat_iff_weakDimensionLE_zero
    (A : Type u) [CommRing A] :
    WeakDimensionLE A 0 ↔ AbsolutelyFlatRing A := by
  sorry

theorem absolutelyFlat_iff_reduced_and_maximal_primes
    (A : Type u) [CommRing A] :
    AbsolutelyFlatRing A ↔
      IsReduced A ∧ ∀ p : PrimeSpectrum A, Ideal.IsMaximal p.asIdeal := by
  sorry

theorem absolutelyFlat_iff_localizations_are_fields
    (A : Type u) [CommRing A] :
    AbsolutelyFlatRing A ↔
      ∀ p : PrimeSpectrum A, IsField (Localization.AtPrime p.asIdeal) := by
  sorry

theorem product_fields_isAbsolutelyFlat
    (ι : Type u) (K : ι → Type u) [∀ i, Field (K i)] :
    AbsolutelyFlatRing (∀ i, K i) := by
  sorry

theorem weaklyEtale_baseChange_lmul
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A']
    (hflat : RingHom.Flat
      (Algebra.TensorProduct.lmul' A (S := B)).toRingHom) :
    RingHom.Flat
      (Algebra.TensorProduct.lmul' A' (S := A' ⊗[A] B)).toRingHom := by
  sorry

theorem weaklyEtale_baseChange
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] [Algebra.WeaklyEtale A B] :
    Algebra.WeaklyEtale A' (A' ⊗[A] B) := by
  sorry

theorem absolutelyFlat_of_flat_lmul
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hflat : RingHom.Flat
      (Algebra.TensorProduct.lmul' A (S := B)).toRingHom)
    (hA : AbsolutelyFlatRing A) : AbsolutelyFlatRing B := by
  sorry

theorem reduced_of_weaklyEtale_of_reduced
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.WeaklyEtale A B] (hA : IsReduced A) : IsReduced B := by
  sorry

theorem weaklyEtale_composition_lmul
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : RingHom.Flat
      (Algebra.TensorProduct.lmul' A (S := B)).toRingHom)
    (hBC : RingHom.Flat
      (Algebra.TensorProduct.lmul' B (S := C)).toRingHom) :
    RingHom.Flat
      (Algebra.TensorProduct.lmul' A (S := C)).toRingHom := by
  sorry

theorem weaklyEtale_composition
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra.WeaklyEtale A B] [Algebra.WeaklyEtale B C] :
    Algebra.WeaklyEtale A C := by
  sorry

theorem weaklyEtale_goDown_lmul
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hBC : RingHom.FaithfullyFlat (algebraMap B C))
    (hC : RingHom.Flat
      (Algebra.TensorProduct.lmul' A (S := C)).toRingHom) :
    RingHom.Flat
      (Algebra.TensorProduct.lmul' A (S := B)).toRingHom := by
  sorry

theorem weaklyEtale_goDown
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hBC : RingHom.FaithfullyFlat (algebraMap B C))
    [Algebra.WeaklyEtale A C] : Algebra.WeaklyEtale A B := by
  sorry

theorem weaklyEtale_permanence
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [Algebra.WeaklyEtale A B] [Algebra.WeaklyEtale A C]
    (f : B →ₐ[A] C) :
    (letI : Algebra B C := f.toRingHom.toAlgebra;
      Algebra.WeaklyEtale B C) := by
  sorry

theorem weaklyEtale_formallyUnramified
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hflat : RingHom.Flat
      (Algebra.TensorProduct.lmul' A (S := B)).toRingHom) :
    RingHom.FormallyUnramified (algebraMap A B) := by
  sorry

theorem weaklyEtale_finiteType_unramified
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hflat : RingHom.Flat
      (Algebra.TensorProduct.lmul' A (S := B)).toRingHom)
    [Algebra.FiniteType A B] : Algebra.Unramified A B := by
  sorry

theorem weaklyEtale_finitePresentation_etale
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.WeaklyEtale A B] [Algebra.FinitePresentation A B] :
    Algebra.Etale A B := by
  sorry

theorem weaklyEtale_of_filteredColimit
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {J : Type v} [Category J] [IsFiltered J]
    (F : J ⥤ CommAlgCat A) (c : Cocone F)
    (h : IsFilteredColimitOfWeaklyEtale A B F c) :
    Algebra.WeaklyEtale A B := by
  sorry

theorem when_weaklyEtale_localization
    (A : Type u) [CommRing A] (S : Submonoid A) :
    Algebra.WeaklyEtale A (Localization S) :=
  localization_isWeaklyEtale A S

/-! ## Weakly étale algebras over fields -/

theorem absolutelyFlat_fields
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (hflat : RingHom.Flat
      (Algebra.TensorProduct.lmul' K (S := L)).toRingHom) :
    Algebra.IsAlgebraic K L ∧ Algebra.IsSeparable K L := by
  sorry

theorem absolutelyFlat_over_field_iff
    {K B : Type u} [Field K] [CommRing B] [Algebra K B] :
    RingHom.Flat
        (Algebra.TensorProduct.lmul' K (S := B)).toRingHom ↔
      Algebra.WeaklyEtale K B := by
  sorry

theorem absolutelyFlat_over_field_iff_filteredColimit_etale
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    {J : Type v} [Category J] [IsFiltered J]
    (F : J ⥤ CommAlgCat K) (c : Cocone F) :
    Algebra.WeaklyEtale K B ↔
      IsFilteredColimitOfEtale K B F c := by
  sorry

theorem finitelyGenerated_subalgebra_etale
    {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    (hflat : RingHom.Flat
      (Algebra.TensorProduct.lmul' K (S := B)).toRingHom)
    (S : Subalgebra K B) [Algebra.FiniteType K S] :
    Algebra.Etale K S := by
  sorry

theorem weaklyEtale_residueFieldExtensions
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.WeaklyEtale A B] :
    ∀ (p : PrimeSpectrum A) (q : PrimeSpectrum B)
      (hq : p.asIdeal = q.asIdeal.comap (algebraMap A B)),
        ResidueFieldExtensionIsSeparableAlgebraic p q hq := by
  sorry

/-! ## Weak dimension at most one -/

theorem weakDimensionLE_one_iff
    (A : Type u) [CommRing A] :
    WeakDimensionLE A 1 ↔
      (∀ I : Ideal A, Module.Flat A I) ∧
      (∀ I : Ideal A, I.FG → Module.Flat A I) ∧
      (∀ (M : Type u) [AddCommGroup M] [Module A M], Module.Flat A M →
        ∀ N : Submodule A M, Module.Flat A N) ∧
      (∀ p : PrimeSpectrum A,
        ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
          ValuationRing (Localization.AtPrime p.asIdeal)) := by
  sorry

theorem product_valuationRings_weakDimensionLE_one
    (ι : Type u) (A K : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)]
    [∀ i, ValuationRing (A i)] [∀ i, Field (K i)]
    [∀ i, Algebra (A i) (K i)] [∀ i, IsFractionRing (A i) (K i)] :
    WeakDimensionLE (∀ i, A i) 1 ∧
      ∃ S : Submonoid (∀ i, A i), IsLocalization S (∀ i, K i) := by
  sorry

theorem exists_product_found_valuation_rings
    {A K : Type u} [CommRing A] [CommRing K] [Algebra A K]
    [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosedIn A K] :
    ∃ (V L : Type u) (_ : CommRing V) (_ : CommRing L),
      ∃ (sq : RingPullbackSquare A K V L),
      WeakDimensionLE V 1 ∧
      RingHom.Flat sq.VL ∧ Function.Injective sq.VL ∧
        Epi (CommRingCat.ofHom sq.VL) := by
  sorry

theorem weakDimensionLE_one_integrallyClosedIn
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (hA : WeakDimensionLE A 1)
    (hflat : RingHom.Flat (algebraMap A B))
    (hinj : Function.Injective (algebraMap A B))
    (hepi : Epi (CommRingCat.ofHom (algebraMap A B))) :
    IsIntegrallyClosedIn A B := by
  sorry

theorem normality_goes_up_weaklyEtale
    {A B K : Type u} [CommRing A] [CommRing B] [CommRing K]
    [Algebra A B] [Algebra A K] [Algebra B (B ⊗[A] K)]
    [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosedIn A K]
    [Algebra.WeaklyEtale A B] :
    IsIntegrallyClosedIn B (B ⊗[A] K) := by
  sorry

/-! ## Henselian local rings -/

theorem integral_domain_over_henselian
    {A B : Type u} [CommRing A] [CommRing B]
    [HenselianLocalRing A] (f : A →+* B)
    (hf : RingHom.IsIntegral f) [IsDomain B] :
    ∃ (_ : IsLocalRing B), IsLocalHom f ∧ HenselianLocalRing B := by
  sorry

theorem integral_domain_over_strictlyHenselian
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : RingHom.IsIntegral f) [IsDomain B]
    [Formalization.Books.Algebra.Unit153.StrictlyHenselianLocalRing A] :
    ∃ (hB : IsLocalRing B),
      letI : IsLocalRing B := hB
      Formalization.Books.Algebra.Unit153.StrictlyHenselianLocalRing B ∧
        IsLocalHom f ∧
        ∃ (hmax : IsLocalRing.maximalIdeal A =
          (IsLocalRing.maximalIdeal B).comap f),
          RingHom.IsPurelyInseparable
            (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A)
              (IsLocalRing.maximalIdeal B) f hmax) := by
  sorry

theorem olivier
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing B]
    [Formalization.Books.Algebra.Unit153.StrictlyHenselianLocalRing A]
    (f : A →+* B) [IsLocalHom f]
    (hweak : letI : Algebra A B := f.toAlgebra; Algebra.WeaklyEtale A B) :
    Function.Bijective f := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit105
