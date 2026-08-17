import Formalization.Books.Algebra.Unit137.SmoothRingMaps
import Formalization.Books.Algebra.Unit138.FormallySmoothMaps
import Formalization.Books.Algebra.Unit140.SmoothAlgebrasOverFields
import Formalization.Books.Algebra.Unit141.SmoothRingMapsNoetherian

/-!
# Commutative Algebra, Chapter 142: Overview of results on smooth ring maps

This chapter gathers the smoothness results proved in Chapters 137--141.
The canonical Mathlib predicates and the source-facing pointwise predicates
from those chapters are used directly; the declarations below preserve the
order and hypotheses of the overview list.
-/

namespace Formalization.Books.Algebra.Unit142

open scoped TensorProduct

noncomputable section

universe u v

/-! ## The cotangent definition and finite projective differentials -/

/- The source's cotangent-complex definition is represented by Mathlib's
   presentation-independent `Algebra.Smooth` class.  Its defining criterion
   is formal smoothness plus finite presentation, and formal smoothness is
   the projective Kähler-differential/vanishing-H¹ criterion. -/
theorem smooth_iff_cotangent_criterion
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.Smooth R S ↔
      Algebra.FinitePresentation R S ∧
        Module.Projective S
          (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) ∧
        Subsingleton (Algebra.H1Cotangent R S) := by
  rw [Formalization.Books.Algebra.Unit137.smooth_iff_formallySmooth_and_finitePresentation,
    Algebra.formallySmooth_iff]
  constructor
  · rintro ⟨⟨hprojective, hH1⟩, hfinite⟩
    exact ⟨hfinite, hprojective, hH1⟩
  · rintro ⟨hfinite, hprojective, hH1⟩
    exact ⟨⟨hprojective, hH1⟩, hfinite⟩

theorem smooth_differentials_finite_projective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] :
    Module.Finite S
        (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) ∧
      Module.Projective S
        (Formalization.Books.Algebra.Unit131.ModuleOfDifferentials R S) := by
  exact ⟨inferInstance, inferInstance⟩

/-! ## Locality and permanence -/

theorem smooth_local_on_target
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.Smooth R S ↔
      ∀ q : PrimeSpectrum S,
        Formalization.Books.Algebra.Unit137.IsSmoothAt R S q :=
  Formalization.Books.Algebra.Unit137.smooth_iff_smooth_at_all_primes

theorem smooth_base_change_over
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.Smooth R S] :
    Algebra.Smooth R' (R' ⊗[R] S) := by
  exact Formalization.Books.Algebra.Unit137.smooth_base_change

theorem smooth_composition
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Algebra.Smooth R S] [Algebra.Smooth S T] :
    Algebra.Smooth R T := by
  exact Formalization.Books.Algebra.Unit137.smooth_comp
    (R := R) (S := S) (T := T)

/- A syntomic map is flat by definition in Chapter 136, so the first
   component of the canonical syntomic conclusion records the source's
   “in particular flat” clause. -/
theorem smooth_is_syntomic_and_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] :
    Formalization.Books.Algebra.Unit136.IsSyntomic (algebraMap R S) ∧
      RingHom.Flat (algebraMap R S) := by
  have h := Formalization.Books.Algebra.Unit137.smooth_is_syntomic
    (R := R) (S := S)
  exact ⟨h, h.1⟩

/-! ## Smooth fibres and formal smoothness -/

/- This is the global form of the fibre criterion.  The Mathlib theorem only
   asks for formal smoothness of each fibre; smooth fibres supply that
   hypothesis through their `formallySmooth` field. -/
theorem smooth_of_flat_finitePresentation_smooth_fibres
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (hfibre : ∀ p : PrimeSpectrum R,
      letI : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
        Algebra.TensorProduct.leftAlgebra
      Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S)) :
    Algebra.Smooth R S := by
  apply Algebra.Smooth.of_formallySmooth_fiber
  intro I hI
  let _ : Algebra I.ResidueField (I.Fiber S) :=
    Algebra.TensorProduct.leftAlgebra
  exact (hfibre ⟨I, hI⟩).formallySmooth

theorem smooth_iff_formallySmooth_and_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) :
    f.Smooth ↔ f.FormallySmooth ∧ f.FinitePresentation := by
  exact Formalization.Books.Algebra.Unit138.smooth_iff_formallySmooth_and_finitePresentation f

/- The Noetherian Artinian test is most precise pointwise: the preceding
   chapter's TFAE records square-zero lifting, small-extension lifting, and
   the residue-field-restricted version together. -/
theorem smooth_test_artinian_overview
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hpq : p.asIdeal = q.asIdeal.comap f)
    [IsNoetherianRing R] (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    List.TFAE
      [ Formalization.Books.Algebra.Unit137.IsSmoothAt R S q,
        Formalization.Books.Algebra.Unit141.squareZeroLiftingAt R S q,
        Formalization.Books.Algebra.Unit141.smallExtensionLiftingAt R S q,
        Formalization.Books.Algebra.Unit141.smallExtensionResidueFieldLiftingAt
          R S q ] := by
  exact Formalization.Books.Algebra.Unit141.smooth_test_artinian f p q hpq hfinite

/-! ## Finite-type models and smooth loci -/

theorem smooth_has_finiteType_model
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.Smooth) :
    letI : Algebra R S := f.toAlgebra
    ∃ (R₀ : Type u) (S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
      (_ : Algebra ℤ R₀) (_ : Algebra R₀ R) (_ : Algebra R₀ S₀),
      Function.Injective (algebraMap R₀ R) ∧
        Algebra.FiniteType ℤ R₀ ∧ Algebra.Smooth R₀ S₀ ∧
          Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀) := by
  exact Formalization.Books.Algebra.Unit138.smooth_finite_type_descent f hf

theorem smooth_locus_commutes_with_flat_base_change
    {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Algebra.FinitePresentation R S]
    [Module.Flat R R'] :
    Formalization.Books.Algebra.Unit137.SmoothLocus R'
        (R' ⊗[R] S) =
      (PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight :
          S →ₐ[R] (R' ⊗[R] S)).toRingHom) ⁻¹'
        Formalization.Books.Algebra.Unit137.SmoothLocus R S := by
  exact Formalization.Books.Algebra.Unit137.flat_base_change_smooth_locus

/-! ## Smooth algebras over fields -/

/- `DifferentialFiber` is the canonical localized presentation of
   Ω[S/k] ⊗[S] κ(m); it is the representation used by Chapter 140. -/
theorem characterize_smooth_kbar_overview
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsAlgClosed k]
    (m : MaximalSpectrum S) :
    List.TFAE
      [ Formalization.Books.Algebra.Unit137.IsSmoothAt k S
          (MaximalSpectrum.toPrimeSpectrum m),
        IsRegularLocalRing (Localization.AtPrime m.asIdeal),
        ((Module.finrank
            (MaximalSpectrum.toPrimeSpectrum m).asIdeal.ResidueField
            (Formalization.Books.Algebra.Unit140.DifferentialFiber k S
              (MaximalSpectrum.toPrimeSpectrum m)) : ℕ∞) : WithBot ℕ∞) =
          ringKrullDim (Localization.AtPrime m.asIdeal) ] := by
  sorry

theorem characterize_smooth_over_field_overview
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    List.TFAE
      [ Formalization.Books.Algebra.Unit137.IsSmoothAt k S q,
        ((Module.finrank q.asIdeal.ResidueField
            (Formalization.Books.Algebra.Unit140.DifferentialFiber k S q) : ℕ∞) :
          WithBot ℕ∞) =
          Formalization.Books.Topology.Unit10.krullDimensionAt q ] := by
  sorry

theorem smooth_over_field_regular_localizations
    {k S : Type*} [Field k] [CommRing S] [Algebra k S]
    [Algebra.Smooth k S] :
    ∀ q : PrimeSpectrum S,
      IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
  sorry

theorem smooth_at_of_separable_and_regular
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : PrimeSpectrum S)
    [Algebra.IsSeparable k q.asIdeal.ResidueField]
    (hregular : IsRegularLocalRing (Localization.AtPrime q.asIdeal)) :
    Formalization.Books.Algebra.Unit137.IsSmoothAt k S q := by
  exact (Formalization.Books.Algebra.Unit140.separable_smooth q).mpr hregular

theorem smooth_at_of_characteristic_zero_differentials_free
    {k S : Type u} [Field k] [CharZero k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : PrimeSpectrum S)
    (hΩ : Formalization.Books.Algebra.Unit137.DifferentialsFiniteFreeAt k S q) :
    Formalization.Books.Algebra.Unit137.IsSmoothAt k S q := by
  exact
    ((Formalization.Books.Algebra.Unit140.characteristic_zero_local_smooth q).out
      1 0 rfl rfl).mp hΩ

/- The closing standard-smooth paragraph is already represented by
   `Algebra.IsStandardSmooth`, its permanence results, and the relative
   global complete-intersection interface in Chapter 137.  It is explanatory
   rather than another independent theorem in this overview. -/

end

end Formalization.Books.Algebra.Unit142
