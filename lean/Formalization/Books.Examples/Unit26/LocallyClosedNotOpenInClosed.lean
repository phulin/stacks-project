import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Data.PNat.Notation
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Examples, Chapter 26: A locally closed subscheme which is not open in closed

This file formalizes the affine and scheme-theoretic interfaces in the source
example.  The nontrivial algebraic calculations and the gluing construction
are theorem interfaces for the proof stage; the rings, localizations, opens,
ideal sheaf, subscheme, and scheme-theoretic images use Mathlib's canonical
definitions.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

namespace Formalization.«Books.Examples».Unit26

/-! ## The countable affine scheme and its open cover -/

/-- The polynomial ring `k[x₁, x₂, ...]`, indexed by positive naturals. -/
abbrev locallyClosedExampleRing (k : Type u) [Field k] := MvPolynomial ℕ+ k

/-- The variable `xₙ` in the countable polynomial ring. -/
def locallyClosedExampleVariable (k : Type u) [Field k] (n : ℕ+) :
    locallyClosedExampleRing k :=
  MvPolynomial.X n

/-- The affine scheme `X = Spec(k[x₁, x₂, ...])`. -/
abbrev locallyClosedExampleScheme (k : Type u) [Field k] : Scheme :=
  Spec (.of (locallyClosedExampleRing k))

/-- The basic open `D(xₙ) ⊆ X`. -/
def locallyClosedExampleBasicOpen (k : Type u) [Field k] (n : ℕ+) :
    (locallyClosedExampleScheme k).Opens :=
  PrimeSpectrum.basicOpen (locallyClosedExampleVariable k n)

/-- The open subset `U = ⋃ₙ D(xₙ)`. -/
def locallyClosedExampleOpen (k : Type u) [Field k] :
    (locallyClosedExampleScheme k).Opens :=
  ⨆ n : ℕ+, locallyClosedExampleBasicOpen k n

/-- The canonical open immersion `U ⟶ X`. -/
noncomputable def locallyClosedExampleOpenImmersion (k : Type u) [Field k] :
    (locallyClosedExampleOpen k).toScheme ⟶ locallyClosedExampleScheme k :=
  (locallyClosedExampleOpen k).ι

instance locallyClosedExampleOpenImmersion_isOpenImmersion
    (k : Type u) [Field k] :
    IsOpenImmersion (locallyClosedExampleOpenImmersion k) := by
  dsimp [locallyClosedExampleOpenImmersion]
  infer_instance

/-! ## The local ideals and their overlap calculation -/

/-- The generators displayed in the source for the ideal `Iₙ`. -/
def locallyClosedExampleIdealGenerators (k : Type u) [Field k] (n : ℕ+) :
    Set (locallyClosedExampleRing k) :=
  Set.range (fun i : {i : ℕ+ // i < n} =>
      locallyClosedExampleVariable k i.1 ^ (n : ℕ)) ∪
    {locallyClosedExampleVariable k n - 1} ∪
    Set.range (fun i : {i : ℕ+ // n < i} =>
      locallyClosedExampleVariable k i.1)

/-- The localization `k[x₁, x₂, ...][1/xₙ]`. -/
abbrev locallyClosedExampleLocalization (k : Type u) [Field k] (n : ℕ+) :=
  Localization.Away (locallyClosedExampleVariable k n)

/-- The ideal `Iₙ` in the `n`-th localization. -/
def locallyClosedExampleIdeal (k : Type u) [Field k] (n : ℕ+) :
    Ideal (locallyClosedExampleLocalization k n) :=
  (Ideal.span (locallyClosedExampleIdealGenerators k n)).map
    (algebraMap (locallyClosedExampleRing k)
      (locallyClosedExampleLocalization k n))

/-- The localization of `Iₙ` after also inverting `xₘ`. -/
noncomputable def locallyClosedExampleIdealAfterInverting
    (k : Type u) [Field k] (n m : ℕ+) :
    Ideal (Localization.Away
      (locallyClosedExampleVariable k n * locallyClosedExampleVariable k m)) :=
  (locallyClosedExampleIdeal k n).map
    (IsLocalization.Away.awayToAwayRight
      (locallyClosedExampleVariable k n)
      (locallyClosedExampleVariable k m))

/-- The restriction of `Iₘ` to the same overlap `D(xₙxₘ)`. -/
noncomputable def locallyClosedExampleOtherIdealAfterInverting
    (k : Type u) [Field k] (n m : ℕ+) :
    Ideal (Localization.Away
      (locallyClosedExampleVariable k n * locallyClosedExampleVariable k m)) :=
  (locallyClosedExampleIdeal k m).map
    (IsLocalization.Away.awayToAwayLeft
      (locallyClosedExampleVariable k m)
      (locallyClosedExampleVariable k n))

/-- If `m ≠ n`, the restriction of `Iₙ` to `D(xₙxₘ)` is the unit ideal. -/
theorem locallyClosedExampleIdealAfterInverting_eq_top
    (k : Type u) [Field k] (n m : ℕ+) (h : n ≠ m) :
    locallyClosedExampleIdealAfterInverting k n m = ⊤ := by
  sorry

/-- The restriction of `Iₘ` to `D(xₙxₘ)` is also the unit ideal when `m ≠ n`. -/
theorem locallyClosedExampleOtherIdealAfterInverting_eq_top
    (k : Type u) [Field k] (n m : ℕ+) (h : n ≠ m) :
    locallyClosedExampleOtherIdealAfterInverting k n m = ⊤ := by
  sorry

/-- The two local ideals have equal restrictions on the common overlap. -/
theorem locallyClosedExampleIdeal_restrictions_agree
    (k : Type u) [Field k] (n m : ℕ+) (h : n ≠ m) :
    locallyClosedExampleIdealAfterInverting k n m =
      locallyClosedExampleOtherIdealAfterInverting k n m := by
  rw [locallyClosedExampleIdealAfterInverting_eq_top k n m h,
    locallyClosedExampleOtherIdealAfterInverting_eq_top k n m h]

/-- The local ideals agree on every overlap `D(xₙxₘ)` with `m ≠ n`. -/
theorem locallyClosedExampleIdeal_overlap_agreement
    (k : Type u) [Field k] (n m : ℕ+) (h : n ≠ m) :
    locallyClosedExampleIdealAfterInverting k n m = ⊤ ∧
      locallyClosedExampleIdealAfterInverting k m n = ⊤ := by
  exact ⟨locallyClosedExampleIdealAfterInverting_eq_top k n m h,
    locallyClosedExampleIdealAfterInverting_eq_top k m n h.symm⟩

/-! ## The gluing datum and the resulting closed subscheme -/

/-- The open of `U` corresponding to the chart `D(xₙ)`. -/
def locallyClosedExampleChart (k : Type u) [Field k] (n : ℕ+) :
    (locallyClosedExampleOpen k).toScheme.Opens :=
  (locallyClosedExampleOpenImmersion k) ⁻¹ᵁ
    locallyClosedExampleBasicOpen k n

/-- Each chart `D(xₙ) ⊆ U` is affine. -/
theorem locallyClosedExampleChart_isAffineOpen
    (k : Type u) [Field k] (n : ℕ+) :
    IsAffineOpen (locallyClosedExampleChart k n) := by
  sorry

/-- The affine-open subtype used to evaluate the glued ideal sheaf. -/
noncomputable def locallyClosedExampleChartAffineOpen
    (k : Type u) [Field k] (n : ℕ+) :
    (locallyClosedExampleOpen k).toScheme.affineOpens :=
  ⟨locallyClosedExampleChart k n,
    locallyClosedExampleChart_isAffineOpen k n⟩

/-- Sections on the `n`-th affine chart of `U`. -/
abbrev locallyClosedExampleChartSections
    (k : Type u) [Field k] (n : ℕ+) :=
  Γ((locallyClosedExampleOpen k).toScheme,
    locallyClosedExampleChartAffineOpen k n)

/--
The compatible local ideals glue to a quasi-coherent ideal sheaf on `U`.

The ring equivalence in the conclusion records the canonical affine-chart
identification with `k[x₁, x₂, ...][1/xₙ]`, and transports the displayed
ideal `Iₙ` back to sections on that chart.
-/
theorem exists_locallyClosedExampleIdealSheaf
    (k : Type u) [Field k] :
    ∃ I : (locallyClosedExampleOpen k).toScheme.IdealSheafData,
      ∀ n : ℕ+, ∃ e : locallyClosedExampleChartSections k n ≃+*
          locallyClosedExampleLocalization k n,
        I.ideal (locallyClosedExampleChartAffineOpen k n) =
          (locallyClosedExampleIdeal k n).comap e.toRingHom := by
  sorry

/-- A chosen ideal sheaf produced by the gluing assertion. -/
noncomputable def locallyClosedExampleIdealSheaf
    (k : Type u) [Field k] :
    (locallyClosedExampleOpen k).toScheme.IdealSheafData :=
  Classical.choose (exists_locallyClosedExampleIdealSheaf k)

/-- The ideal-sheaf component on the chart `D(xₙ)`. -/
noncomputable def locallyClosedExampleChartIdeal
    (k : Type u) [Field k] (n : ℕ+) :
    Ideal (locallyClosedExampleChartSections k n) :=
  (locallyClosedExampleIdealSheaf k).ideal
    (locallyClosedExampleChartAffineOpen k n)

/-- The chosen ideal sheaf has the displayed local components. -/
theorem locallyClosedExampleIdealSheaf_local_component
    (k : Type u) [Field k] (n : ℕ+) :
    ∃ e : locallyClosedExampleChartSections k n ≃+*
        locallyClosedExampleLocalization k n,
      locallyClosedExampleChartIdeal k n =
        (locallyClosedExampleIdeal k n).comap e.toRingHom := by
  exact (Classical.choose_spec (exists_locallyClosedExampleIdealSheaf k)) n

/-- The closed subscheme `Z ⊆ U` defined by the glued ideal sheaf. -/
noncomputable def locallyClosedExampleSubscheme (k : Type u) [Field k] : Scheme :=
  (locallyClosedExampleIdealSheaf k).subscheme

/-- The closed immersion `Z ⟶ U`. -/
noncomputable def locallyClosedExampleSubschemeToOpen
    (k : Type u) [Field k] :
    locallyClosedExampleSubscheme k ⟶
      (locallyClosedExampleOpen k).toScheme :=
  (locallyClosedExampleIdealSheaf k).subschemeι

instance locallyClosedExampleSubschemeToOpen_isClosedImmersion
    (k : Type u) [Field k] :
    IsClosedImmersion (locallyClosedExampleSubschemeToOpen k) := by
  dsimp [locallyClosedExampleSubschemeToOpen, locallyClosedExampleSubscheme]
  infer_instance

/-- The immersion `Z ⟶ U ⟶ X` in the source example. -/
noncomputable def locallyClosedExampleImmersion
    (k : Type u) [Field k] :
    locallyClosedExampleSubscheme k ⟶ locallyClosedExampleScheme k :=
  locallyClosedExampleSubschemeToOpen k ≫
    locallyClosedExampleOpenImmersion k

instance locallyClosedExampleImmersion_isImmersion
    (k : Type u) [Field k] :
    IsImmersion (locallyClosedExampleImmersion k) := by
  dsimp [locallyClosedExampleImmersion]
  infer_instance

/-! ## The obstruction to an open-then-closed factorization -/

/-- A factorization of a morphism as an open immersion followed by a closed one. -/
def IsOpenThenClosedFactorization {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∃ (W : Scheme) (g₁ : X ⟶ W) (g₂ : W ⟶ Y),
    IsOpenImmersion g₁ ∧ IsClosedImmersion g₂ ∧ g₁ ≫ g₂ = f

/-- The ideal of elements of the base ring lying in every contracted `Iₙ`. -/
def locallyClosedExampleGlobalIdealCandidate
    (k : Type u) [Field k] : Ideal (locallyClosedExampleRing k) :=
  ⨅ n : ℕ+, (locallyClosedExampleIdeal k n).comap
    (algebraMap (locallyClosedExampleRing k)
      (locallyClosedExampleLocalization k n))

/-- Membership in the candidate is membership in every contracted local ideal. -/
theorem locallyClosedExample_mem_globalIdealCandidate_iff
    (k : Type u) [Field k] (f : locallyClosedExampleRing k) :
    f ∈ locallyClosedExampleGlobalIdealCandidate k ↔
      ∀ n : ℕ+,
        algebraMap (locallyClosedExampleRing k)
            (locallyClosedExampleLocalization k n) f ∈
          locallyClosedExampleIdeal k n := by
  simp [locallyClosedExampleGlobalIdealCandidate]

/-- The only element lying in all the local ideals is zero. -/
theorem locallyClosedExampleGlobalIdealCandidate_eq_bot
    (k : Type u) [Field k] :
    locallyClosedExampleGlobalIdealCandidate k = ⊥ := by
  sorry

/-- An element belongs to every contracted local ideal exactly when it is zero. -/
theorem locallyClosedExample_mem_all_localIdeals_iff_eq_zero
    (k : Type u) [Field k] (f : locallyClosedExampleRing k) :
    (∀ n : ℕ+,
        algebraMap (locallyClosedExampleRing k)
            (locallyClosedExampleLocalization k n) f ∈
          locallyClosedExampleIdeal k n) ↔ f = 0 := by
  constructor
  · intro hf
    have hf' : f ∈ locallyClosedExampleGlobalIdealCandidate k :=
      (locallyClosedExample_mem_globalIdealCandidate_iff k f).2 hf
    rw [locallyClosedExampleGlobalIdealCandidate_eq_bot k] at hf'
    exact Ideal.mem_bot.mp hf'
  · intro hf
    subst f
    intro n
    simp

/-- A base ideal realizes the displayed local ideals if all its localizations agree with them. -/
def locallyClosedExampleGlobalIdealRealizesComponents
    (k : Type u) [Field k] (I : Ideal (locallyClosedExampleRing k)) : Prop :=
  ∀ n : ℕ+,
    I.map (algebraMap (locallyClosedExampleRing k)
      (locallyClosedExampleLocalization k n)) =
      locallyClosedExampleIdeal k n

/-- No ideal of the base ring has the displayed localizations. -/
theorem locallyClosedExample_no_globalIdeal_realizesComponents
    (k : Type u) [Field k] :
    ¬ ∃ I : Ideal (locallyClosedExampleRing k),
      locallyClosedExampleGlobalIdealRealizesComponents k I := by
  sorry

/-- Any open-then-closed factorization would produce such a base ideal. -/
theorem locallyClosedExample_factorization_implies_globalIdeal
    (k : Type u) [Field k] :
    IsOpenThenClosedFactorization (locallyClosedExampleImmersion k) →
      ∃ I : Ideal (locallyClosedExampleRing k),
        locallyClosedExampleGlobalIdealRealizesComponents k I := by
  sorry

/-- The immersion is not an open immersion followed by a closed immersion. -/
theorem locallyClosedExample_no_openThenClosed_factorization
    (k : Type u) [Field k] :
    ¬ IsOpenThenClosedFactorization (locallyClosedExampleImmersion k) := by
  intro h
  exact locallyClosedExample_no_globalIdeal_realizesComponents k
    (locallyClosedExample_factorization_implies_globalIdeal k h)

/-! ## The two scheme-theoretic-image failures -/

/-- The scheme-theoretic image of `Z ⟶ X` is all of `X`. -/
theorem locallyClosedExample_schemeTheoreticImage_is_target
    (k : Type u) [Field k] :
    IsIso (locallyClosedExampleImmersion k).imageι := by
  sorry

/-- The underlying topological image of `Z ⟶ X` is not dense in `X`. -/
theorem locallyClosedExample_not_topologically_dense
    (k : Type u) [Field k] :
    ¬ DenseRange (locallyClosedExampleImmersion k) := by
  sorry

/-- The restriction of the immersion to the open `U ⊆ X`. -/
noncomputable def locallyClosedExampleRestrictedImmersion
    (k : Type u) [Field k] :
    ((locallyClosedExampleImmersion k) ⁻¹ᵁ locallyClosedExampleOpen k).toScheme ⟶
      (locallyClosedExampleOpen k).toScheme :=
  locallyClosedExampleImmersion k ∣_ locallyClosedExampleOpen k

/-- The preimage of `U` in `Z` is all of `Z`. -/
theorem locallyClosedExample_preimage_open_eq_top
    (k : Type u) [Field k] :
    (locallyClosedExampleImmersion k ⁻¹ᵁ locallyClosedExampleOpen k) = ⊤ := by
  sorry

/-- The restriction is the closed immersion `Z ⟶ U` from the source. -/
instance locallyClosedExampleRestrictedImmersion_isClosedImmersion
    (k : Type u) [Field k] :
    IsClosedImmersion (locallyClosedExampleRestrictedImmersion k) := by
  sorry

/-- The source of the restricted morphism is canonically the original `Z`. -/
noncomputable def locallyClosedExampleRestrictedSourceIso
    (k : Type u) [Field k] :
    ((locallyClosedExampleImmersion k ⁻¹ᵁ locallyClosedExampleOpen k).toScheme) ≅
      locallyClosedExampleSubscheme k :=
  Scheme.isoOfEq (locallyClosedExampleSubscheme k)
      (locallyClosedExample_preimage_open_eq_top k) ≪≫
    Scheme.topIso (locallyClosedExampleSubscheme k)

/-- The scheme-theoretic image of the restricted closed immersion is its source. -/
theorem locallyClosedExample_restricted_toImage_isIso
    (k : Type u) [Field k] :
    IsIso (locallyClosedExampleRestrictedImmersion k).toImage := by
  infer_instance

/-- The restricted scheme-theoretic image is isomorphic to the original `Z`. -/
theorem locallyClosedExample_restricted_image_is_original
    (k : Type u) [Field k] :
    Nonempty
      ((locallyClosedExampleRestrictedImmersion k).image ≅
        locallyClosedExampleSubscheme k) := by
  let h : IsIso (locallyClosedExampleRestrictedImmersion k).toImage :=
    locallyClosedExample_restricted_toImage_isIso k
  obtain ⟨g, hfg, hgf⟩ := h.out
  let e : (locallyClosedExampleRestrictedImmersion k).image ≅
      (locallyClosedExampleImmersion k ⁻¹ᵁ locallyClosedExampleOpen k).toScheme :=
    { hom := g
      inv := locallyClosedExampleRestrictedImmersion k |>.toImage
      hom_inv_id := hgf
      inv_hom_id := hfg }
  exact ⟨e ≪≫ locallyClosedExampleRestrictedSourceIso k⟩

/-- The scheme-theoretic image after restriction is not all of `U`. -/
theorem locallyClosedExample_restricted_image_not_target
    (k : Type u) [Field k] :
    ¬ IsIso (locallyClosedExampleRestrictedImmersion k).imageι := by
  sorry

/-- Formation of the scheme-theoretic image does not commute with restriction to `U`. -/
theorem locallyClosedExample_schemeTheoreticImage_not_commutes_with_open_restriction
    (k : Type u) [Field k] :
    ¬ IsIso (locallyClosedExampleRestrictedImmersion k).imageι :=
  locallyClosedExample_restricted_image_not_target k

end Formalization.«Books.Examples».Unit26
