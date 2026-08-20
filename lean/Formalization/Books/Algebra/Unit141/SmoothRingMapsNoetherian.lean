import Formalization.Books.Algebra.Unit137.SmoothRingMaps
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Commutative Algebra, Chapter 141: Smooth ring maps in the Noetherian case

This chapter records the small-extension lifting test for smoothness at a
prime.  Local algebra diagrams are expressed with Mathlib's canonical
`AlgHom`s, and residue fields use `Ideal.ResidueField`.
-/

namespace Formalization.Books.Algebra.Unit141

noncomputable section

universe u v

/-! ## Small extensions -/

/-- A small extension is a surjection of local Artinian rings whose kernel
has module length one over the source. -/
def IsSmallExtension
    {B' B : Type*} [CommRing B'] [CommRing B]
    (φ : B' →+* B) : Prop :=
  IsLocalRing B' ∧ IsArtinianRing B' ∧
    IsLocalRing B ∧ IsArtinianRing B ∧
      Function.Surjective φ ∧
        Module.length B' (RingHom.ker φ) = 1

/-- The kernel of a small extension is square-zero. -/
theorem smallExtension_kernel_square_zero
    {B' B : Type*} [CommRing B'] [CommRing B]
    (φ : B' →+* B) (hφ : IsSmallExtension φ) :
    (RingHom.ker φ) ^ 2 = ⊥ := by
  let _ : IsLocalRing B' := hφ.1
  let _ : IsLocalRing B := hφ.2.2.1
  have hker_ne_top : RingHom.ker φ ≠ ⊤ := by
    intro htop
    have h1 : (1 : B') ∈ RingHom.ker φ := by
      rw [htop]
      trivial
    have hzero : (1 : B) = 0 := by
      simp [RingHom.mem_ker] at h1
    exact one_ne_zero hzero
  have hsimple : IsSimpleModule B' (RingHom.ker φ) :=
    (Module.length_eq_one_iff).mp hφ.2.2.2.2.2
  let _ : IsSimpleModule B' (RingHom.ker φ) := hsimple
  have hann :
      Module.annihilator B' (RingHom.ker φ) =
        IsLocalRing.maximalIdeal B' := by
    exact IsLocalRing.eq_maximalIdeal IsSimpleModule.annihilator_isMaximal
  rw [pow_two]
  apply le_antisymm
  · apply Ideal.mul_le.2
    intro a ha b hb
    have ha_max : a ∈ IsLocalRing.maximalIdeal B' :=
      IsLocalRing.le_maximalIdeal hker_ne_top ha
    have ha_ann : a ∈ Module.annihilator B' (RingHom.ker φ) := by
      rw [hann]
      exact ha_max
    have hab := Module.mem_annihilator.mp ha_ann (⟨b, hb⟩ : RingHom.ker φ)
    change a * b = 0
    simpa [smul_eq_mul] using congrArg Subtype.val hab
  · exact bot_le

/-- The kernel of a small extension is principal and is annihilated by the
maximal ideal of the source. -/
theorem smallExtension_kernel_principal
    {B' B : Type*} [CommRing B'] [CommRing B] [IsLocalRing B']
    (φ : B' →+* B) (hφ : IsSmallExtension φ) :
    ∃ x : B',
      RingHom.ker φ = Ideal.span ({x} : Set B') ∧
        ∀ y : B', y ∈ IsLocalRing.maximalIdeal B' → y * x = 0 := by
  have hsimple : IsSimpleModule B' (RingHom.ker φ) :=
    (Module.length_eq_one_iff).mp hφ.2.2.2.2.2
  let _ : IsSimpleModule B' (RingHom.ker φ) := hsimple
  have hmodprin : Module.IsPrincipal B' (RingHom.ker φ) := by
    infer_instance
  have hprincipal : (RingHom.ker φ : Submodule B' B').IsPrincipal :=
    Module.isPrincipal_submodule_iff.mp hmodprin
  obtain ⟨x, hx⟩ := hprincipal.principal
  have hxmem : x ∈ RingHom.ker φ := by
    rw [hx]
    exact Submodule.mem_span_singleton_self x
  refine ⟨x, ?_, ?_⟩
  · simpa only [Ideal.submodule_span_eq] using hx
  · intro y hy
    have hann :
        Module.annihilator B' (RingHom.ker φ) =
          IsLocalRing.maximalIdeal B' := by
      exact IsLocalRing.eq_maximalIdeal IsSimpleModule.annihilator_isMaximal
    have hy_ann : y ∈ Module.annihilator B' (RingHom.ker φ) := by
      rw [hann]
      exact hy
    have hyx := Module.mem_annihilator.mp hy_ann (⟨x, hxmem⟩ : RingHom.ker φ)
    simpa [smul_eq_mul] using congrArg Subtype.val hyx

/-! ## Lifting conditions -/

/-- The square-zero lifting condition at a prime, with all solid diagrams
encoded by `R`-algebra homomorphisms. -/
def squareZeroLiftingAt
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∀ {B' B : Type max u v} [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B]
    [IsLocalRing B'] [IsLocalRing B]
    (e : B' →ₐ[R] B),
    Function.Surjective e →
      (RingHom.ker e.toRingHom) ^ 2 = ⊥ →
        ∀ (g : S →ₐ[R] B),
          q.asIdeal = (IsLocalRing.maximalIdeal B).comap g.toRingHom →
            ∃ lift : S →ₐ[R] B', e.comp lift = g

/-- The lifting condition restricted to small extensions. -/
def smallExtensionLiftingAt
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∀ {B' B : Type max u v} [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B]
    [IsLocalRing B'] [IsLocalRing B]
    (e : B' →ₐ[R] B),
    IsSmallExtension e.toRingHom →
      ∀ (g : S →ₐ[R] B),
        q.asIdeal = (IsLocalRing.maximalIdeal B).comap g.toRingHom →
          ∃ lift : S →ₐ[R] B', e.comp lift = g

/-- The canonical map on residue fields induced by a map to a local ring is
bijective precisely when the map induces an isomorphism of residue fields. -/
def residueFieldMapIsBijective
    {S B : Type*} [CommRing S] [CommRing B] [IsLocalRing B]
    (q : PrimeSpectrum S) (g : S →+* B)
    (hq : q.asIdeal = (IsLocalRing.maximalIdeal B).comap g) : Prop :=
  Function.Bijective
    (Ideal.ResidueField.map q.asIdeal (IsLocalRing.maximalIdeal B) g hq)

/-- The small-extension lifting condition with the additional residue-field
isomorphism required in the final condition of the source lemma. -/
def smallExtensionResidueFieldLiftingAt
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∀ {B' B : Type max u v} [CommRing B'] [CommRing B]
    [Algebra R B'] [Algebra R B]
    [IsLocalRing B'] [IsLocalRing B]
    (e : B' →ₐ[R] B),
    IsSmallExtension e.toRingHom →
      ∀ (g : S →ₐ[R] B),
        (hq : q.asIdeal = (IsLocalRing.maximalIdeal B).comap g.toRingHom) →
          residueFieldMapIsBijective q g.toRingHom hq →
            ∃ lift : S →ₐ[R] B', e.comp lift = g

/-- The square-zero lifting condition implies the small-extension lifting
condition.  The only input is that a small extension has square-zero kernel. -/
theorem smallExtensionLiftingAt_of_squareZeroLiftingAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {q : PrimeSpectrum S} (h : squareZeroLiftingAt R S q) :
    smallExtensionLiftingAt R S q := by
  intro B' B _ _ _ _ _ _ e he g hq
  exact h (B' := B') (B := B) e he.2.2.2.2.1
    (smallExtension_kernel_square_zero e.toRingHom he) g hq

/-- The unrestricted small-extension lifting condition implies the version
where the residue-field map is required to be an isomorphism. -/
theorem smallExtensionResidueFieldLiftingAt_of_smallExtensionLiftingAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {q : PrimeSpectrum S} (h : smallExtensionLiftingAt R S q) :
    smallExtensionResidueFieldLiftingAt R S q := by
  intro B' B _ _ _ _ _ _ e he g hq _
  exact h (B' := B') (B := B) e he g hq

/-! ## The Noetherian smoothness test -/

/-- For a finite-type map from a Noetherian ring, smoothness at a prime is
equivalent to the square-zero, small-extension, and residue-field-restricted
lifting conditions. -/
theorem smooth_test_artinian
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hpq : p.asIdeal = q.asIdeal.comap f)
    [IsNoetherianRing R] (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    List.TFAE
      [ Formalization.Books.Algebra.Unit137.IsSmoothAt R S q,
        squareZeroLiftingAt R S q,
        smallExtensionLiftingAt R S q,
        smallExtensionResidueFieldLiftingAt R S q ] := by
  sorry

end

end Formalization.Books.Algebra.Unit141
