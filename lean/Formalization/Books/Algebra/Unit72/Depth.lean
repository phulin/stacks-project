import Formalization.Books.Algebra.Unit60
import Formalization.Books.Algebra.Unit63
import Formalization.Books.Algebra.Unit68
import Formalization.Books.Algebra.Unit71
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Commutative Algebra, Chapter 72: Depth

The source defines depth as a supremum of lengths of regular sequences.  The
value is represented by `ℕ∞`, so the convention that the zero module has
infinite depth and the possibility of an unbounded supremum are both visible
in the interface.  Regular and weakly regular sequences, associated primes,
support dimension, localization, finite ring maps, and Ext are the canonical
interfaces from Mathlib and earlier chapters.
-/

namespace Formalization.Books.Algebra.Unit72

open Set
open scoped Pointwise

universe u v

noncomputable section

/-! ## Definition and immediate consequences -/

/-- The `I`-depth of a finite `R`-module, with `⊤` standing for `∞`.

The membership conditions on the list record that the regular sequence lies
in `I`; `RingTheory.Sequence.IsRegular` supplies the successive
nonzerodivisor conditions and the nonzero final quotient convention. -/
noncomputable def depth
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] : ℕ∞ :=
  if _ : I • (⊤ : Submodule R M) = ⊤ then
    ⊤
  else
    sSup {n : ℕ∞ | ∃ rs : List R,
      n = (rs.length : ℕ∞) ∧
        (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs}

/-- Depth at the maximal ideal of a local ring. -/
abbrev localDepth
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : ℕ∞ :=
  depth (IsLocalRing.maximalIdeal R) M

/-- The zero-module convention for depth. -/
theorem depth_eq_top_of_subsingleton
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Subsingleton M] :
    depth I M = ⊤ := by
  simp [depth, Subsingleton.elim (I • (⊤ : Submodule R M)) (⊤ : Submodule R M)]

/-- If the ideal is the whole ring, every finite module has infinite depth. -/
theorem depth_top_ideal
    {R : Type u} (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    depth (⊤ : Ideal R) M = ⊤ := by
  simp [depth]

/-- Nakayama's consequence used in the source's explanation of the definition. -/
theorem smul_top_ne_top_of_le_ring_jacobson
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) :
    I • (⊤ : Submodule R M) ≠ ⊤ := by
  intro htop
  have htopbot : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I (⊤ : Submodule R M)
      Module.Finite.fg_top htop.symm.le hI
  have hsub : Subsingleton M := by
    constructor
    intro x y
    have hx : x ∈ (⊥ : Submodule R M) := htopbot ▸ Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule R M) := htopbot ▸ Submodule.mem_top
    have hx0 : x = 0 := by simpa using hx
    have hy0 : y = 0 := by simpa using hy
    exact hx0.trans hy0.symm
  exact (not_nontrivial_iff_subsingleton.mpr hsub) (inferInstance : Nontrivial M)

/-- A module has `I`-depth zero exactly when it is nonzero and `I` contains
no module nonzerodivisor. -/
theorem depth_eq_zero_iff
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    depth I M = 0 ↔
      Nontrivial M ∧ ¬ ∃ f : R, f ∈ I ∧ IsSMulRegular M f := by
  classical
  by_cases htop : I • (⊤ : Submodule R M) = ⊤
  · simp only [depth, dif_pos htop]
    constructor
    · intro hzero
      exact (ENat.top_ne_zero hzero).elim
    · rintro ⟨_, hno⟩
      obtain ⟨f, hf, hfm⟩ :=
        Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
          (⊤ : Submodule R M) Module.Finite.fg_top htop.symm.le
      have hg : 1 - f ∈ I := by
        simpa only [neg_sub] using I.neg_mem hf
      have hreg : IsSMulRegular M (1 - f) := by
        intro x y hxy
        simpa [sub_smul, hfm] using hxy
      exact (hno ⟨1 - f, hg, hreg⟩).elim
  · simp only [depth, dif_neg htop]
    rw [ENat.sSup_eq_zero]
    constructor
    · intro hzero
      have hnontr : Nontrivial M := by
        by_contra h
        have hsub : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
        have heq : I • (⊤ : Submodule R M) = ⊤ := by
          apply le_antisymm le_top
          intro x hx
          have hx0 : x = 0 := hsub.elim x 0
          rw [hx0]
          exact (I • (⊤ : Submodule R M)).zero_mem
        exact htop heq
      refine ⟨hnontr, ?_⟩
      rintro ⟨f, hf, hreg⟩
      have hspan : Ideal.span ({f} : Set R) ≤ I :=
        (Ideal.span_singleton_le_iff_mem (I := I)).mpr hf
      have hfle' : Ideal.span ({f} : Set R) • (⊤ : Submodule R M) ≤
          I • (⊤ : Submodule R M) := Submodule.smul_mono_left hspan
      have hfle : f • (⊤ : Submodule R M) ≤ I • (⊤ : Submodule R M) := by
        simpa only [Submodule.ideal_span_singleton_smul] using hfle'
      have hfne : f • (⊤ : Submodule R M) ≠ ⊤ := by
        intro hftop
        apply htop
        have htop_le : (⊤ : Submodule R M) ≤ I • (⊤ : Submodule R M) := by
          calc
            (⊤ : Submodule R M) = f • (⊤ : Submodule R M) := hftop.symm
            _ ≤ I • (⊤ : Submodule R M) := hfle
        exact top_unique htop_le
      have hq : Nontrivial (QuotSMulTop f M) :=
        Submodule.Quotient.nontrivial_iff.mpr hfne
      have hseq : RingTheory.Sequence.IsRegular M [f] :=
        RingTheory.Sequence.IsRegular.cons hreg
          (RingTheory.Sequence.IsRegular.nil R (QuotSMulTop f M))
      have hmem : (1 : ℕ∞) ∈ {n : ℕ∞ | ∃ rs : List R,
          n = (rs.length : ℕ∞) ∧
            (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs} := by
        exact ⟨[f], by simp, by simp [hf], hseq⟩
      have hone := hzero 1 hmem
      exact one_ne_zero hone
    · rintro ⟨hnontr, hno⟩ a ha
      rcases ha with ⟨rs, hlen, hmem, hreg⟩
      cases rs with
      | nil => simpa using hlen
      | cons f rs =>
          have hparts :=
            (RingTheory.Sequence.isRegular_cons_iff M f rs).mp hreg
          have hregf : IsSMulRegular M f := hparts.1
          exact (hno ⟨f, hmem f (by simp), hregf⟩).elim

/-! ## Basic properties -/

/-- Depth can be computed using weakly regular sequences, including the case
where the ideal acts surjectively on the module. -/
theorem depth_eq_sSup_weaklyRegular
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    depth I M =
      sSup {n : ℕ∞ | ∃ rs : List R,
        n = (rs.length : ℕ∞) ∧
          (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsWeaklyRegular M rs} := by
  sorry

/-- Over a Noetherian local ring, support dimension bounds depth. -/
theorem supportDim_ge_localDepth
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    ((localDepth R M : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim R M := by
  sorry

/-- A nonzero finite module over a Noetherian ring has finite `I`-depth when
`I` does not generate the whole module. -/
theorem depth_lt_top_of_noetherian
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type v)
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) :
    depth I M < ⊤ := by
  sorry

/-! ## Ext characterization -/

/-- The Ext groups used to detect local depth, together with the literal
"smallest integer" condition from the source.  The displayed long exact
Ext segment in the source is the canonical `extCovariantSequence` and its
exactness theorem from Chapter 71. -/
theorem localDepth_eq_min_ext
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    ∃ i : ℕ,
      localDepth R M = (i : ℕ∞) ∧
        Nontrivial
          (Formalization.Books.Algebra.Unit71.ExtGroup
            (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
            (ModuleCat.of R M) i) ∧
        ∀ j : ℕ, j < i →
          ¬ Nontrivial
            (Formalization.Books.Algebra.Unit71.ExtGroup
              (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
              (ModuleCat.of R M) j) := by
  sorry

/-! ## Depth in a short exact sequence -/

/-- The three standard depth inequalities for a short exact sequence of
nonzero finite modules over a local Noetherian ring.  The displayed Ext
sequence is likewise supplied by Chapter 71's generic long exact sequence;
the scalar short exact sequence used in the proof is Mathlib's canonical
`IsSMulRegular.smulShortComplex_shortExact`. -/
theorem localDepth_shortExact
    {R N₁ N₂ N₃ : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁] [Nontrivial N₁]
    [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂] [Nontrivial N₂]
    [AddCommGroup N₃] [Module R N₃] [Module.Finite R N₃] [Nontrivial N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    localDepth R N₂ ≥ min (localDepth R N₁) (localDepth R N₃) ∧
      localDepth R N₃ ≥ min (localDepth R N₂) (localDepth R N₁ - 1) ∧
      localDepth R N₁ ≥ min (localDepth R N₂) (localDepth R N₃ + 1) := by
  sorry

/-! ## Regular elements and depth drops -/

/-- A nonzerodivisor in the maximal ideal lowers local depth by one. -/
theorem localDepth_drops_by_one
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M x) :
    localDepth R (QuotSMulTop x M) = localDepth R M - 1 := by
  sorry

/-- Every regular sequence can be extended to one of maximal local depth. -/
theorem regular_sequence_extend_to_localDepth
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    ∀ xs : List R, RingTheory.Sequence.IsRegular M xs →
      ∃ ys : List R,
        RingTheory.Sequence.IsRegular M (xs ++ ys) ∧
          localDepth R M = ((xs ++ ys).length : ℕ∞) := by
  sorry

/-! ## Associated primes and localization -/

/-- An associated prime survives in a suitable power quotient after adjoining
an element and taking a minimal prime. -/
theorem associatedPrime_inherit_minimal_prime
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (p q : PrimeSpectrum R)
    (hp : p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M)
    (hq : q.asIdeal ∈ (p.asIdeal ⊔ Ideal.span ({x} : Set R)).minimalPrimes) :
    ∃ n : ℕ, 1 ≤ n ∧
      q ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R
        (QuotSMulTop (x ^ n) M) := by
  sorry

/-- Every associated prime gives a quotient whose dimension bounds local
depth. -/
theorem localDepth_le_dim_of_associatedPrime
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (p : PrimeSpectrum R)
    (hp : p ∈ Formalization.Books.Algebra.Unit63.associatedPrimes R M) :
    ((localDepth R M : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (R ⧸ p.asIdeal) := by
  sorry

/-- Localizing at a prime cannot reduce the sum of local depth and quotient
dimension below the original local depth. -/
theorem localDepth_localization_add_dim
    {R M : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (p : Ideal R) [p.IsPrime] :
    ((localDepth (Localization.AtPrime p)
        (LocalizedModule.AtPrime p M) : ℕ∞) : WithBot ℕ∞) +
        ringKrullDim (R ⧸ p) ≥
      ((localDepth R M : ℕ∞) : WithBot ℕ∞) := by
  sorry

/-! ## Finite ring extensions -/

/-- The minimum of the depths at all maximal localizations of a finite
`S`-module.  Using `MaximalSpectrum` is the canonical enumeration of maximal
ideals; `sInf` agrees with the finite minimum in the source and is also
well-defined for the subsingleton ring. -/
noncomputable def finiteExtensionMaximalDepth
    (S : Type u) (N : Type v) [CommRing S] [AddCommGroup N]
    [Module S N] [Module.Finite S N] : ℕ∞ :=
  sInf (Set.range fun m : MaximalSpectrum S =>
    localDepth (Localization.AtPrime m.asIdeal)
      (LocalizedModule.AtPrime m.asIdeal N))

/-- Finite descent of depth from a local Noetherian ring to a finite ring
extension. -/
theorem depth_goes_down_finite
    {R S N : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup N] [Module S N]
    [Module.Finite S N] (f : R →+* S) (hf : RingHom.Finite f) :
    finiteExtensionMaximalDepth S N =
      (letI : Algebra R S := f.toAlgebra
       letI : Module.Finite R S := hf
       letI : Module R N := Module.compHom N f
       letI : IsScalarTower R S N := SMul.comp.isScalarTower f
       letI : Module.Finite R N := Module.Finite.trans S N
       localDepth R N) := by
  sorry

end

end Formalization.Books.Algebra.Unit72
