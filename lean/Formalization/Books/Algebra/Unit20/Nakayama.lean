import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Commutative Algebra, Chapter 20: Nakayama's lemma

The source's finite modules, ideal actions, localizations, residue fields, and
cotangent spaces use Mathlib's canonical interfaces.  The declarations below
record the twelve numbered forms of Nakayama's lemma, its localization form
and stated special cases, and the final local-ring surjectivity criterion.
-/

namespace Formalization.Books.Algebra.Unit20

universe u v w

noncomputable section

open Set
open scoped Pointwise TensorProduct

/-! ## The twelve forms of Nakayama's lemma -/

/- The canonical normalization of ``f ∈ 1 + I`` is `f - 1 ∈ I`. -/

/-- Nakayama, part (1): a finite module satisfying `IM = M` has a scalar in
`1 + I` that annihilates it. -/
theorem nakayama_part_one
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) = ⊤) :
    ∃ f : R, f - 1 ∈ I ∧ ∀ m : M, f • m = 0 := by
  have hle : (⊤ : Submodule R M) ≤ I • (⊤ : Submodule R M) := by
    rw [hIM]
  obtain ⟨f, hf, hfm⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
      (⊤ : Submodule R M) Module.Finite.fg_top hle
  exact ⟨f, hf, fun m => hfm m Submodule.mem_top⟩

/-- Nakayama, part (2): the Jacobson-radical version of part (1). -/
theorem nakayama_part_two
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) [Module.Finite R M]
    (hIM : I • (⊤ : Submodule R M) = ⊤)
    (hI : I ≤ Ring.jacobson R) :
    Subsingleton M := by
  have hI' : I ≤ Ideal.jacobson (⊥ : Ideal R) := by
    simpa only [Ideal.jacobson_bot] using hI
  have htop : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I (⊤ : Submodule R M)
      Module.Finite.fg_top hIM.symm.le hI'
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ (⊥ : Submodule R M) := htop ▸ Submodule.mem_top
  have hy : y ∈ (⊥ : Submodule R M) := htop ▸ Submodule.mem_top
  have hx0 : x = 0 := by simpa using hx
  have hy0 : y = 0 := by simpa using hy
  exact hx0.trans hy0.symm

/-- Nakayama, part (3): after adding `IN'` to `N`, localization at a scalar
in `1 + I` makes `N` equal to the localized ambient module. -/
theorem nakayama_part_three
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (N N' : Submodule R M) [Module.Finite R N']
    (hM : (⊤ : Submodule R M) = N ⊔ I • N') :
    ∃ f : R, f - 1 ∈ I ∧
      f • (⊤ : Submodule R M) ≤ N ∧
      N.localized (Submonoid.powers f) = ⊤ := by
  obtain ⟨f, hf, hsmul⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
      (Submodule.FG.of_finite (N := N')) (le_top) (by rw [← hM])
  refine ⟨f, hf, hsmul, ?_⟩
  apply le_antisymm
  · exact le_top
  · simpa only [Submodule.localized, Submodule.localized'_top] using
      (Submodule.localized'_le_localized'_of_smul_le
        (Localization (Submonoid.powers f)) (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
        ⟨f, Submonoid.mem_powers f⟩ hsmul)

/-- Nakayama, part (4): the Jacobson-radical version of part (3). -/
theorem nakayama_part_four
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (N N' : Submodule R M) [Module.Finite R N']
    (hM : (⊤ : Submodule R M) = N ⊔ I • N')
    (hI : I ≤ Ring.jacobson R) :
    N = ⊤ := by
  have hI' : I ≤ Ideal.jacobson (⊥ : Ideal R) := by
    simpa only [Ideal.jacobson_bot] using hI
  have hNN' : N' ≤ N ⊔ I • N' := by
    rw [← hM]
    exact le_top
  have hsmul : I • N' ≤ N :=
    Submodule.smul_le_of_le_smul_of_le_jacobson_bot
      (Submodule.FG.of_finite (N := N')) hI' hNN'
  apply top_unique
  rw [hM]
  exact sup_le le_rfl hsmul

/-- Nakayama, part (5): surjectivity modulo `I` becomes surjectivity after
localizing at some scalar in `1 + I`. -/
theorem nakayama_part_five
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (I : Ideal R) (φ : N →ₗ[R] M) [Module.Finite R M]
    (hφ : Function.Surjective
      ((I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) φ
        (Submodule.smul_top_le_comap_smul_top I φ))) :
    ∃ f : R, f - 1 ∈ I ∧
      Function.Surjective (LocalizedModule.map (Submonoid.powers f) φ) := by
  have hM : (⊤ : Submodule R M) =
      LinearMap.range φ ⊔ I • (⊤ : Submodule R M) := by
    have hq : LinearMap.range
        ((I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) φ
          (Submodule.smul_top_le_comap_smul_top I φ)) = ⊤ :=
      LinearMap.range_eq_top.mpr hφ
    rw [Submodule.range_mapQ] at hq
    rw [Submodule.map_mkQ_eq_top] at hq
    have hq' : (⊤ : Submodule R M) = I • (⊤ : Submodule R M) ⊔ LinearMap.range φ :=
      hq.symm
    rw [sup_comm] at hq'
    exact hq'
  obtain ⟨f, hf, hsmul⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
      (I := I) (N := LinearMap.range φ) (N' := (⊤ : Submodule R M)) (P := ⊤)
      Module.Finite.fg_top le_top hM.le
  refine ⟨f, hf, ?_⟩
  rw [← IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective
    (LocalizedModule.mkLinearMap (Submonoid.powers f) N)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)]
  rw [← LinearMap.range_eq_top]
  rw [LinearMap.range_localizedMap_eq_localized₀_range
    (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) N)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M) φ]
  have hloc := Submodule.localized₀_le_localized₀_of_smul_le
    (Submonoid.powers f) (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    ⟨f, Submonoid.mem_powers f⟩ hsmul
  have htop :
      (⊤ : Submodule R (LocalizedModule (Submonoid.powers f) M)) ≤
        Submodule.localized₀ (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M) (LinearMap.range φ) := by
    simpa only [Submodule.localized₀_top] using hloc
  exact le_antisymm le_top htop

/-- Nakayama, part (6): the Jacobson-radical version of part (5). -/
theorem nakayama_part_six
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (I : Ideal R) (φ : N →ₗ[R] M) [Module.Finite R M]
    (hφ : Function.Surjective
      ((I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) φ
        (Submodule.smul_top_le_comap_smul_top I φ)))
    (hI : I ≤ Ring.jacobson R) :
    Function.Surjective φ := by
  have hM : (⊤ : Submodule R M) = LinearMap.range φ ⊔ I • (⊤ : Submodule R M) := by
    have hq : LinearMap.range
        ((I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) φ
          (Submodule.smul_top_le_comap_smul_top I φ)) = ⊤ :=
      LinearMap.range_eq_top.mpr hφ
    rw [Submodule.range_mapQ] at hq
    rw [Submodule.map_mkQ_eq_top] at hq
    have hq' : (⊤ : Submodule R M) = I • (⊤ : Submodule R M) ⊔ LinearMap.range φ :=
      hq.symm
    rw [sup_comm] at hq'
    exact hq'
  rw [← LinearMap.range_eq_top]
  exact nakayama_part_four I (LinearMap.range φ) (⊤ : Submodule R M) hM hI

/-- Nakayama, part (7): a finite generating family modulo `I` generates after
localization at a scalar in `1 + I`. -/
theorem nakayama_part_seven
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (n : ℕ) (x : Fin n → M)
    [Module.Finite R M]
    (hx : Submodule.span R
      (Set.range (fun i => (I • (⊤ : Submodule R M)).mkQ (x i))) = ⊤) :
    ∃ f : R, f - 1 ∈ I ∧
      Submodule.span (Localization.Away f)
        (Set.range (fun i =>
          LocalizedModule.mkLinearMap (Submonoid.powers f) M (x i))) = ⊤ := by
  let ψ : (Fin n →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
  have hq : LinearMap.range
      ((I • (⊤ : Submodule R (Fin n →₀ R))).mapQ
        (I • (⊤ : Submodule R M)) ψ
        (Submodule.smul_top_le_comap_smul_top I ψ)) = ⊤ := by
    rw [Submodule.range_mapQ, Finsupp.range_linearCombination]
    rw [Submodule.map_span]
    have himage :
        (I • (⊤ : Submodule R M)).mkQ '' Set.range x =
          Set.range (fun i => (I • (⊤ : Submodule R M)).mkQ (x i)) := by
      ext y
      constructor
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, rfl⟩
    rw [himage]
    exact hx
  have hφ : Function.Surjective
      ((I • (⊤ : Submodule R (Fin n →₀ R))).mapQ
        (I • (⊤ : Submodule R M)) ψ
        (Submodule.smul_top_le_comap_smul_top I ψ)) :=
    LinearMap.range_eq_top.mp hq
  obtain ⟨f, hf, hmap⟩ := nakayama_part_five I ψ hφ
  have hsource_id :
      Submodule.span R
        (Set.range (fun i : Fin n => Finsupp.single (id i) (1 : R))) = ⊤ := by
    rw [← Finsupp.range_lmapDomain]
    rw [Finsupp.lmapDomain_id]
    simp
  have hsource :
      Submodule.span R (Set.range (fun i : Fin n => Finsupp.single i (1 : R))) = ⊤ := by
    simpa only [id_eq] using hsource_id
  refine ⟨f, hf, ?_⟩
  have hsource_loc :
      Submodule.span (Localization (Submonoid.powers f))
        ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin n →₀ R)) ''
          Set.range (fun i : Fin n => Finsupp.single i (1 : R))) = ⊤ :=
    span_eq_top_of_isLocalizedModule (Localization (Submonoid.powers f))
      (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin n →₀ R)) hsource
  have hspan :
      Submodule.span (Localization (Submonoid.powers f))
        ((LocalizedModule.map (Submonoid.powers f) ψ) ''
          ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin n →₀ R)) ''
            Set.range (fun i => Finsupp.single i (1 : R)))) = ⊤ := by
    rw [Submodule.span_image, hsource_loc, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hmap
  have himage :
      (LocalizedModule.map (Submonoid.powers f) ψ) ''
          ((LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin n →₀ R)) ''
            Set.range (fun i => Finsupp.single i (1 : R))) =
        Set.range (fun i =>
          LocalizedModule.mkLinearMap (Submonoid.powers f) M (x i)) := by
    ext y
    constructor
    · rintro ⟨z, ⟨w, ⟨i, rfl⟩, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      simp [ψ]
    · rintro ⟨i, rfl⟩
      refine ⟨(LocalizedModule.mkLinearMap (Submonoid.powers f) (Fin n →₀ R))
          (Finsupp.single i 1), ⟨Finsupp.single i 1, ⟨i, rfl⟩, rfl⟩, ?_⟩
      change LocalizedModule.map (Submonoid.powers f) ψ
          (LocalizedModule.mk (Finsupp.single i 1) 1) =
        LocalizedModule.mk (x i) 1
      rw [LocalizedModule.map_mk]
      simp [ψ]
  change Submodule.span (Localization (Submonoid.powers f))
    (Set.range (fun i =>
      LocalizedModule.mkLinearMap (Submonoid.powers f) M (x i))) = ⊤
  rw [← himage]
  exact hspan

/-- Nakayama, part (8): the Jacobson-radical version of part (7). -/
theorem nakayama_part_eight
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (n : ℕ) (x : Fin n → M)
    [Module.Finite R M]
    (hx : Submodule.span R
      (Set.range (fun i => (I • (⊤ : Submodule R M)).mkQ (x i))) = ⊤)
    (hI : I ≤ Ring.jacobson R) :
    Submodule.span R (Set.range x) = ⊤ := by
  let ψ : (Fin n →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
  have hq : LinearMap.range
      ((I • (⊤ : Submodule R (Fin n →₀ R))).mapQ
        (I • (⊤ : Submodule R M)) ψ
        (Submodule.smul_top_le_comap_smul_top I ψ)) = ⊤ := by
    rw [Submodule.range_mapQ, Finsupp.range_linearCombination]
    rw [Submodule.map_span]
    have himage :
        (I • (⊤ : Submodule R M)).mkQ '' Set.range x =
          Set.range (fun i => (I • (⊤ : Submodule R M)).mkQ (x i)) := by
      ext y
      constructor
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, rfl⟩
    rw [himage]
    exact hx
  have hφ : Function.Surjective
      ((I • (⊤ : Submodule R (Fin n →₀ R))).mapQ
        (I • (⊤ : Submodule R M)) ψ
        (Submodule.smul_top_le_comap_smul_top I ψ)) :=
    LinearMap.range_eq_top.mp hq
  have hsurj : Function.Surjective ψ :=
    nakayama_part_six I ψ hφ hI
  rw [span_range_eq_top_iff_surjective_finsuppLinearCombination R]
  change Function.Surjective ψ
  exact hsurj

/-- Nakayama, part (9): finiteness is unnecessary when the ideal is nilpotent. -/
theorem nakayama_part_nine
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (hIM : I • (⊤ : Submodule R M) = ⊤) (hI : IsNilpotent I) :
    Subsingleton M := by
  obtain ⟨n, hn⟩ := hI
  have hpow : ∀ k : ℕ, I ^ k • (⊤ : Submodule R M) = ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Submodule.mul_smul, hIM, ih]
  have htop : (⊤ : Submodule R M) = ⊥ := by
    rw [← hpow n, hn]
    simp
  refine ⟨?_⟩
  intro x y
  have hx : x ∈ (⊥ : Submodule R M) := htop ▸ Submodule.mem_top
  have hy : y ∈ (⊥ : Submodule R M) := htop ▸ Submodule.mem_top
  have hx0 : x = 0 := by simpa using hx
  have hy0 : y = 0 := by simpa using hy
  exact hx0.trans hy0.symm

/-- Nakayama, part (10): the nilpotent version of part (4). -/
theorem nakayama_part_ten
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (N N' : Submodule R M)
    (hM : (⊤ : Submodule R M) = N ⊔ I • N') (hI : IsNilpotent I) :
    N = ⊤ := by
  have hsup : N ⊔ I • (⊤ : Submodule R M) = ⊤ := by
    apply le_antisymm le_top
    calc
      (⊤ : Submodule R M) = N ⊔ I • N' := hM
      _ ≤ N ⊔ I • (⊤ : Submodule R M) := by
        apply sup_le le_sup_left
        apply Submodule.smul_le.2
        intro r hr m hm
        apply Submodule.mem_sup_right
        exact Submodule.smul_mem_smul hr
          (show m ∈ (⊤ : Submodule R M) from Submodule.mem_top)
  have hq : I • (⊤ : Submodule R (M ⧸ N)) = ⊤ := by
    calc
      I • (⊤ : Submodule R (M ⧸ N)) =
          I • ((⊤ : Submodule R M).map N.mkQ) := by
        rw [Submodule.map_top, Submodule.range_mkQ]
      _ = (I • (⊤ : Submodule R M)).map N.mkQ :=
        (Submodule.map_smul'' (I := I) (N := (⊤ : Submodule R M)) N.mkQ).symm
      _ = ⊤ := (Submodule.map_mkQ_eq_top (p := N)
        (p' := I • (⊤ : Submodule R M))).mpr hsup
  have hzero : Subsingleton (M ⧸ N) := nakayama_part_nine I hq hI
  refine top_unique ?_
  intro x hx
  have hx0 : (Submodule.mkQ N) x = 0 := Subsingleton.elim _ _
  have hxN : x ∈ N := by simpa using hx0
  exact hxN

/-- Nakayama, part (11): the nilpotent version of part (6). -/
theorem nakayama_part_eleven
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (I : Ideal R) (φ : N →ₗ[R] M)
    (hφ : Function.Surjective
      ((I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) φ
        (Submodule.smul_top_le_comap_smul_top I φ)))
    (hI : IsNilpotent I) :
    Function.Surjective φ := by
  have hM : (⊤ : Submodule R M) = LinearMap.range φ ⊔ I • (⊤ : Submodule R M) := by
    have hq : LinearMap.range
        ((I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) φ
          (Submodule.smul_top_le_comap_smul_top I φ)) = ⊤ :=
      LinearMap.range_eq_top.mpr hφ
    rw [Submodule.range_mapQ] at hq
    rw [Submodule.map_mkQ_eq_top] at hq
    have hq' : (⊤ : Submodule R M) = I • (⊤ : Submodule R M) ⊔ LinearMap.range φ :=
      hq.symm
    rw [sup_comm] at hq'
    exact hq'
  rw [← LinearMap.range_eq_top]
  exact nakayama_part_ten I (LinearMap.range φ) (⊤ : Submodule R M) hM hI

/-- Nakayama, part (12): arbitrary generating families lift across a
nilpotent ideal. -/
theorem nakayama_part_twelve
    {R : Type u} {M : Type v} {A : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (x : A → M)
    (hx : Submodule.span R
      (Set.range (fun a => (I • (⊤ : Submodule R M)).mkQ (x a))) = ⊤)
    (hI : IsNilpotent I) :
    Submodule.span R (Set.range x) = ⊤ := by
  let ψ : (A →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
  have hq : LinearMap.range
      ((I • (⊤ : Submodule R (A →₀ R))).mapQ
        (I • (⊤ : Submodule R M)) ψ
        (Submodule.smul_top_le_comap_smul_top I ψ)) = ⊤ := by
    rw [Submodule.range_mapQ, Finsupp.range_linearCombination]
    rw [Submodule.map_span]
    have himage :
        (I • (⊤ : Submodule R M)).mkQ '' Set.range x =
          Set.range (fun a => (I • (⊤ : Submodule R M)).mkQ (x a)) := by
      ext y
      constructor
      · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨x a, ⟨a, rfl⟩, rfl⟩
    rw [himage]
    exact hx
  have hφ : Function.Surjective
      ((I • (⊤ : Submodule R (A →₀ R))).mapQ
        (I • (⊤ : Submodule R M)) ψ
        (Submodule.smul_top_le_comap_smul_top I ψ)) :=
    LinearMap.range_eq_top.mp hq
  have hsurj : Function.Surjective ψ :=
    nakayama_part_eleven I ψ hφ hI
  rw [span_range_eq_top_iff_surjective_finsuppLinearCombination R]
  change Function.Surjective ψ
  exact hsurj

/-! ## Localization form and the two stated special cases -/

/-- If the images of a finite family generate `S⁻¹(M/IM)`, they generate
`M_f` for some `f ∈ S + I`. -/
theorem nakayama_localization
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (S : Submonoid R) (I : Ideal R)
    [Module.Finite R M] (n : ℕ) (x : Fin n → M)
    (hx : Submodule.span (Localization (S.map (Ideal.Quotient.mk I).toMonoidHom))
      (Set.range (fun i =>
        LocalizedModule.mkLinearMap
          (S.map (Ideal.Quotient.mk I).toMonoidHom)
          (M ⧸ (I • (⊤ : Submodule R M)))
          ((I • (⊤ : Submodule R M)).mkQ (x i)))) = ⊤) :
    ∃ f : R, f ∈ (S : Set R) + (I : Set R) ∧
      Submodule.span (Localization.Away f)
        (Set.range (fun i =>
          LocalizedModule.mkLinearMap (Submonoid.powers f) M (x i))) = ⊤ := by
  let v : Fin n → (M ⧸ (I • (⊤ : Submodule R M))) :=
    fun i => (I • (⊤ : Submodule R M)).mkQ (x i)
  let T : Submonoid (R ⧸ I) :=
    S.map (Ideal.Quotient.mk I).toMonoidHom
  let fQ : (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I]
      LocalizedModule T (M ⧸ (I • (⊤ : Submodule R M))) :=
    LocalizedModule.mkLinearMap T (M ⧸ (I • (⊤ : Submodule R M)))
  let N : Submodule (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
    Submodule.span (R ⧸ I) (Set.range v)
  haveI instFinite : Module.Finite (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M)))
  let hfin :
      ∃ m : ℕ, ∃ y : Fin m → (M ⧸ (I • (⊤ : Submodule R M))),
        Submodule.span (R ⧸ I) (Set.range y) = ⊤ :=
    Module.Finite.exists_fin
  let m := hfin.choose
  let y := hfin.choose_spec.choose
  have hy : Submodule.span (R ⧸ I) (Set.range y) = ⊤ :=
    hfin.choose_spec.choose_spec
  have himage : fQ '' Set.range v = Set.range (fun i => fQ (v i)) := by
    ext z
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  have hgen : ∀ j : Fin m,
      ∃ t : T, ∃ z ∈ N, (t : R ⧸ I) • y j ∈ N := by
    intro j
    have hmem :
        fQ (y j) ∈
          Submodule.span (Localization T) (fQ '' Set.range v) := by
      rw [himage]
      rw [show Submodule.span (Localization T) (Set.range (fun i => fQ (v i))) =
          ⊤ by simpa [fQ, v, T] using hx]
      exact Submodule.mem_top
    let hmul := multiple_mem_span_of_mem_localization_span T (Localization T)
        (fQ '' Set.range v) (fQ (y j)) hmem
    let t := hmul.choose
    have ht := hmul.choose_spec
    have ht' : (t : R ⧸ I) • fQ (y j) ∈ Submodule.map fQ N := by
      change (t : R ⧸ I) • fQ (y j) ∈
        Submodule.map fQ (Submodule.span (R ⧸ I) (Set.range v))
      rw [Submodule.map_span]
      exact ht
    let z := ht'.choose
    have hz : z ∈ N := ht'.choose_spec.1
    have hzt := ht'.choose_spec.2
    have heq0 : fQ z = fQ ((t : R ⧸ I) • y j) := by
      simpa only [map_smul, z] using hzt
    have heq :
        IsLocalizedModule.mk' (S := T) fQ z (1 : T) =
          IsLocalizedModule.mk' (S := T) fQ ((t : R ⧸ I) • y j) (1 : T) := by
      simpa only [IsLocalizedModule.mk'_one] using heq0
    rw [IsLocalizedModule.mk'_eq_mk'_iff] at heq
    let u := heq.choose
    have hu := heq.choose_spec
    have hu' : (u : R ⧸ I) • ((t : R ⧸ I) • y j) =
        (u : R ⧸ I) • z := by
      change heq.choose • ((t : R ⧸ I) • y j) = heq.choose • z
      simpa [Submonoid.smul_def] using hu
    refine ⟨u * t, z, hz, ?_⟩
    change (((u : R ⧸ I) * (t : R ⧸ I)) • y j) ∈ N
    rw [← smul_smul, hu']
    exact N.smul_mem _ hz
  let t : Fin m → T := fun j => (hgen j).choose
  let w : T := Finset.univ.prod t
  have hw : ∀ j : Fin m, ((w : T) : R ⧸ I) • y j ∈ N := by
    intro j
    have ht : ((t j : T) : R ⧸ I) • y j ∈ N :=
      (hgen j).choose_spec.choose_spec.2
    change ((↑(Finset.univ.prod t) : R ⧸ I) • y j) ∈ N
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    simp only [Submonoid.coe_mul, mul_smul]
    exact N.smul_mem _ ht
  have hwtop :
      ((w : T) : R ⧸ I) • (⊤ : Submodule (R ⧸ I)
        (M ⧸ (I • (⊤ : Submodule R M)))) ≤ N := by
    rw [← hy, Submodule.smul_span]
    apply Submodule.span_le.2
    rintro z ⟨q, ⟨j, rfl⟩, hz⟩
    exact hz.symm ▸ hw j
  have hmapN :
      (Submodule.span R (Set.range x)).map
          ((I • (⊤ : Submodule R M)).mkQ) =
        N.restrictScalars R := by
    rw [Submodule.map_span]
    rw [Submodule.restrictScalars_span R (R ⧸ I)
      Ideal.Quotient.mk_surjective]
    change Submodule.span R
        ((I • (⊤ : Submodule R M)).mkQ '' Set.range x) =
      Submodule.span R (Set.range v)
    apply congrArg (Submodule.span R)
    ext z
    constructor
    · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  have hI0 :
      (I • (⊤ : Submodule R M)).map
          ((I • (⊤ : Submodule R M)).mkQ) = ⊥ := by
    simpa using (Submodule.mkQ_map_self (I • (⊤ : Submodule R M)))
  have hmap :
      (Submodule.span R (Set.range x) ⊔
        I • (⊤ : Submodule R M)).map
          ((I • (⊤ : Submodule R M)).mkQ) =
        N.restrictScalars R := by
    rw [Submodule.map_sup, hmapN, hI0, sup_bot_eq]
  have hcomap :
      Submodule.comap ((I • (⊤ : Submodule R M)).mkQ)
          (N.restrictScalars R) =
        Submodule.span R (Set.range x) ⊔
          I • (⊤ : Submodule R M) := by
    rw [← hmap]
    apply Submodule.comap_map_eq_self
    simp
  let s0 : S := ⟨w.property.choose, w.property.choose_spec.1⟩
  have hs0 : (Ideal.Quotient.mk I) (s0 : R) = (w : R ⧸ I) :=
    w.property.choose_spec.2
  have hsmul : (s0 : R) • (⊤ : Submodule R M) ≤
      Submodule.span R (Set.range x) ⊔ I • (⊤ : Submodule R M) := by
    intro z hz
    obtain ⟨m', hm', rfl⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists z (s0 : R)
        (⊤ : Submodule R M)).mp hz
    have hqmem :
        (I • (⊤ : Submodule R M)).mkQ ((s0 : R) • m') ∈
          N.restrictScalars R := by
      change (I • (⊤ : Submodule R M)).mkQ ((s0 : R) • m') ∈ N
      have hwt : ((w : R ⧸ I) •
          (I • (⊤ : Submodule R M)).mkQ m') ∈ N :=
        hwtop (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
      rw [map_smul]
      change (Ideal.Quotient.mk I (s0 : R)) •
        (I • (⊤ : Submodule R M)).mkQ m' ∈ N
      rw [hs0]
      exact hwt
    rw [← hcomap]
    exact Submodule.mem_comap.mpr hqmem
  let P := Localization (Submonoid.powers (s0 : R))
  let fM := LocalizedModule.mkLinearMap (Submonoid.powers (s0 : R)) M
  let Nloc : Submodule P (LocalizedModule (Submonoid.powers (s0 : R)) M) :=
      (Submodule.span R (Set.range x)).localized' P
      (Submonoid.powers (s0 : R)) fM
  let J : Ideal P :=
    Submodule.localized' P (Submonoid.powers (s0 : R))
      (Algebra.linearMap R P) I
  have hloc :
      (⊤ : Submodule R M).localized' P
          (Submonoid.powers (s0 : R)) fM ≤
        (Submodule.span R (Set.range x) ⊔ I • (⊤ : Submodule R M)).localized'
          P (Submonoid.powers (s0 : R)) fM :=
    Submodule.localized'_le_localized'_of_smul_le P
      (Submonoid.powers (s0 : R)) fM
      ⟨(s0 : R), Submonoid.mem_powers (s0 : R)⟩ hsmul
  have hlocal_smul :
      (Submodule.span R (Set.range x) ⊔ I • (⊤ : Submodule R M)).localized'
          P (Submonoid.powers (s0 : R)) fM =
        Nloc ⊔ J • (⊤ : Submodule P (LocalizedModule (Submonoid.powers (s0 : R)) M)) := by
    rw [sup_eq_iSup, Submodule.localized'_iSup]
    simp only [iSup_bool_eq, Bool.cond_true, Bool.cond_false]
    rw [Submodule.localized'_smul, Submodule.localized'_top]
  have hM :
      (⊤ : Submodule P (LocalizedModule (Submonoid.powers (s0 : R)) M)) =
        Nloc ⊔ J • (⊤ : Submodule P (LocalizedModule (Submonoid.powers (s0 : R)) M)) := by
    apply le_antisymm
    · rw [← hlocal_smul]
      simpa only [Submodule.localized'_top] using hloc
    · exact le_top
  obtain ⟨g, hg, hgsmul, hgloc⟩ :=
    nakayama_part_three J Nloc (⊤ : Submodule P
      (LocalizedModule (Submonoid.powers (s0 : R)) M)) hM
  have hJmap : J = Ideal.map (algebraMap R P) I := by
    dsimp [J]
    rw [Ideal.map, Ideal.span, Submodule.localized'_eq_span, Algebra.coe_linearMap]
  let f2 := LocalizedModule.mkLinearMap (Submonoid.powers g)
    (LocalizedModule (Submonoid.powers (s0 : R)) M)
  have hloc_mem : ∀ z : M,
      f2 (fM z) ∈ Nloc.localized (Submonoid.powers g) := by
    intro z
    rw [hgloc]
    exact Submodule.mem_top
  have hclear : ∀ z : M, ∃ q : Submonoid.powers g,
      (q : P) • fM z ∈ Nloc := by
    intro z
    have hz := hloc_mem z
    rw [Submodule.mem_localized'] at hz
    obtain ⟨m', hm', r, hr⟩ := hz
    have heq : IsLocalizedModule.mk' f2 m' r =
        IsLocalizedModule.mk' f2 (fM z) (1 : Submonoid.powers g) := by
      rw [IsLocalizedModule.mk'_one]
      exact hr
    rw [IsLocalizedModule.mk'_eq_mk'_iff] at heq
    obtain ⟨q, hq⟩ := heq
    refine ⟨q * r, ?_⟩
    have hqr : ((q * r : Submonoid.powers g) : P) • fM z =
        (q : P) • m' := by
      rw [Submonoid.coe_mul, mul_smul]
      simpa [Submonoid.smul_def] using hq
    rw [hqr]
    exact Nloc.smul_mem _ hm'
  have hscalar : ∀ z : M, ∃ e : R, e ∈ (S : Set R) + (I : Set R) ∧
      e • z ∈ Submodule.span R (Set.range x) := by
    intro z
    obtain ⟨q, hq⟩ := hclear z
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (q : P) g).mp q.property
    have hqJ : (q : P) - 1 ∈ J := by
      have hpow : g ^ k - 1 ∈ J := by
        obtain ⟨a, ha⟩ := sub_one_dvd_pow_sub_one g k
        rw [ha]
        exact J.mul_mem_right a hg
      simpa [hk] using hpow
    have hqmap : (q : P) - 1 ∈ Ideal.map (algebraMap R P) I := by
      rw [← hJmap]
      exact hqJ
    obtain ⟨b, v, hb⟩ :=
      IsLocalization.exists_mk'_eq (Submonoid.powers (s0 : R)) (S := P) (q : P)
    have hfrac : IsLocalization.mk' P (b - (v : R)) v ∈
        Ideal.map (algebraMap R P) I := by
      have he : IsLocalization.mk' P (b - (v : R)) v = (q : P) - 1 := by
        rw [← IsLocalization.mk'_cancel (S := P) (b - (v : R)) v v]
        rw [show (b - (v : R)) * (v : R) = b * (v : R) - (v : R) * (v : R) by ring]
        rw [IsLocalization.mk'_sub P b (v : R) v v]
        rw [IsLocalization.mk'_self' P]
        rw [hb]
      rw [he]
      exact hqmap
    obtain ⟨d', hd', hdb⟩ :=
      (IsLocalization.mk'_mem_map_algebraMap_iff (Submonoid.powers (s0 : R)) P I
        (b - (v : R)) v).mp hfrac
    have hqmem := hq
    rw [Submodule.mem_localized'] at hqmem
    obtain ⟨m', hm', s', hs'⟩ := hqmem
    have hmod : IsLocalizedModule.mk' fM m' s' =
        IsLocalizedModule.mk' fM (b • z) v := by
      calc
        IsLocalizedModule.mk' fM m' s' = (q : P) • fM z := hs'
        _ = IsLocalizedModule.mk' fM (b • z) v := by
          dsimp [fM]
          rw [← hb, ← IsLocalizedModule.mk'_one (Submonoid.powers (s0 : R))]
          simpa only [mul_one] using
            (IsLocalizedModule.mk'_smul_mk' (S := Submonoid.powers (s0 : R))
              P (LocalizedModule.mkLinearMap (Submonoid.powers (s0 : R)) M)
              b z v (1 : Submonoid.powers (s0 : R)))
    rw [IsLocalizedModule.mk'_eq_mk'_iff] at hmod
    obtain ⟨c, hc⟩ := hmod
    have hrel : ((c : R) * (s' : R) * b) • z ∈
        Submodule.span R (Set.range x) := by
      have hrhs : ((c : R) * (v : R)) • m' ∈
          Submodule.span R (Set.range x) := by
        exact (Submodule.span R (Set.range x)).smul_mem _ hm'
      have heq : ((c : R) * (s' : R) * b) • z =
          ((c : R) * (v : R)) • m' := by
        simpa [Submonoid.smul_def, smul_smul, mul_assoc] using hc
      rw [heq]
      exact hrhs
    refine ⟨(d' : R) * (c : R) * (s' : R) * b, ?_, ?_⟩
    · have hpow : (c : R) * (s' : R) * (d' : R) * (v : R) ∈
          Submonoid.powers (s0 : R) := by
        exact (Submonoid.powers (s0 : R)).mul_mem
          ((Submonoid.powers (s0 : R)).mul_mem
            ((Submonoid.powers (s0 : R)).mul_mem c.property s'.property) hd') v.property
      refine ⟨(c : R) * (s' : R) * (d' : R) * (v : R),
        (Submonoid.powers_le.mpr s0.property) hpow,
        (c : R) * (s' : R) * ((d' : R) * (b - (v : R))), ?_, ?_⟩
      · exact I.mul_mem_left _ hdb
      · ring
    · have hrel' := (Submodule.span R (Set.range x)).smul_mem (d' : R) hrel
      simpa [smul_smul, mul_assoc, mul_comm, mul_left_comm] using hrel'
  let hfinM : ∃ m : ℕ, ∃ y : Fin m → M,
      Submodule.span R (Set.range y) = ⊤ := Module.Finite.exists_fin
  let mM := hfinM.choose
  let yM := hfinM.choose_spec.choose
  have hyM : Submodule.span R (Set.range yM) = (⊤ : Submodule R M) :=
    hfinM.choose_spec.choose_spec
  let eM : Fin mM → R := fun j => (hscalar (yM j)).choose
  have heM : ∀ j : Fin mM, eM j ∈ (S : Set R) + (I : Set R) := by
    intro j
    exact (hscalar (yM j)).choose_spec.1
  have hmul_add : ∀ {a b : R}, a ∈ (S : Set R) + (I : Set R) →
      b ∈ (S : Set R) + (I : Set R) → a * b ∈ (S : Set R) + (I : Set R) := by
    intro a b ha hb
    rcases ha with ⟨sa, hsa, ia, hia, rfl⟩
    rcases hb with ⟨sb, hsb, ib, hib, rfl⟩
    refine ⟨sa * sb, S.mul_mem hsa hsb,
      sa * ib + sb * ia + ia * ib, ?_, ?_⟩
    · exact I.add_mem (I.add_mem (I.mul_mem_left sa hib) (I.mul_mem_left sb hia))
        (I.mul_mem_left ia hib)
    · ring
  have hprod : ∀ t : Finset (Fin mM),
      (∀ j ∈ t, eM j ∈ (S : Set R) + (I : Set R)) →
        t.prod eM ∈ (S : Set R) + (I : Set R) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨1, S.one_mem, 0, I.zero_mem, ?_⟩
        simp
    | @insert a t ha ih =>
        intro ht
        rw [Finset.prod_insert ha]
        exact hmul_add (ht a (Finset.mem_insert_self a t))
          (ih (fun b hb => ht b (Finset.mem_insert_of_mem hb)))
  let f : R := Finset.univ.prod eM
  have hfmem : f ∈ (S : Set R) + (I : Set R) := by
    exact hprod Finset.univ (fun j _ => heM j)
  have hfgen : ∀ j : Fin mM, f • yM j ∈ Submodule.span R (Set.range x) := by
    intro j
    have hj := (hscalar (yM j)).choose_spec.2
    change ((↑(Finset.univ.prod eM) : R) • yM j) ∈
      Submodule.span R (Set.range x)
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    simp only [mul_smul]
    exact (Submodule.span R (Set.range x)).smul_mem _ hj
  have hfrel : f • (⊤ : Submodule R M) ≤ Submodule.span R (Set.range x) := by
    rw [← hyM, Submodule.smul_span]
    apply Submodule.span_le.2
    rintro z ⟨m', ⟨j, rfl⟩, rfl⟩
    exact hfgen j
  refine ⟨f, hfmem, ?_⟩
  have hlocf := Submodule.localized'_le_localized'_of_smul_le
    (Localization.Away f) (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    ⟨f, Submonoid.mem_powers f⟩ hfrel
  have htopf : (⊤ : Submodule (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) M)) ≤
      (Submodule.span R (Set.range x)).localized'
        (Localization.Away f) (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M) := by
    simpa only [Submodule.localized'_top] using hlocf
  have hEq := le_antisymm le_top htopf
  rw [Submodule.localized'_span] at hEq
  have himagef : (LocalizedModule.mkLinearMap (Submonoid.powers f) M) ''
        Set.range x = Set.range (fun i =>
          LocalizedModule.mkLinearMap (Submonoid.powers f) M (x i)) := by
    ext z
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  rw [himagef] at hEq
  exact hEq

/-- Special case `I = 0` of `nakayama_localization`. -/
theorem nakayama_localization_zero
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (S : Submonoid R)
    [Module.Finite R M] (n : ℕ) (x : Fin n → M)
    (hx : Submodule.span (Localization S)
      (Set.range (fun i => LocalizedModule.mkLinearMap S M (x i))) = ⊤) :
    ∃ f : R, f ∈ (S : Set R) ∧
      Submodule.span (Localization.Away f)
        (Set.range (fun i =>
          LocalizedModule.mkLinearMap (Submonoid.powers f) M (x i))) = ⊤ := by
  let fM := LocalizedModule.mkLinearMap S M
  let N0 : Submodule R M := Submodule.span R (Set.range x)
  have himage : fM '' Set.range x = Set.range (fun i => fM (x i)) := by
    ext z
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  have hscalar : ∀ z : M, ∃ t : S, (t : R) • z ∈ N0 := by
    intro z
    have hmem : fM z ∈ Submodule.span (Localization S) (fM '' Set.range x) := by
      rw [himage, hx]
      exact Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S
      (Localization S) (fM '' Set.range x) (fM z) hmem
    have ht' : (t : R) • fM z ∈ Submodule.map fM N0 := by
      change (t : R) • fM z ∈ Submodule.map fM (Submodule.span R (Set.range x))
      rw [Submodule.map_span]
      exact ht
    obtain ⟨z', hz', hzt⟩ := ht'
    have heq0 : fM z' = fM ((t : R) • z) := by
      simpa only [map_smul] using hzt
    have heq : IsLocalizedModule.mk' fM z' (1 : S) =
        IsLocalizedModule.mk' fM ((t : R) • z) (1 : S) := by
      simpa only [IsLocalizedModule.mk'_one] using heq0
    rw [IsLocalizedModule.mk'_eq_mk'_iff] at heq
    obtain ⟨u, hu⟩ := heq
    refine ⟨u * t, ?_⟩
    have hu' : (u : R) • ((t : R) • z) = (u : R) • z' := by
      change u • ((t : R) • z) = u • z'
      simpa [Submonoid.smul_def] using hu
    change ((u : R) * (t : R)) • z ∈ N0
    rw [← smul_smul, hu']
    exact N0.smul_mem _ hz'
  let hfinM : ∃ m : ℕ, ∃ y : Fin m → M,
      Submodule.span R (Set.range y) = (⊤ : Submodule R M) := Module.Finite.exists_fin
  let mM := hfinM.choose
  let yM := hfinM.choose_spec.choose
  have hyM : Submodule.span R (Set.range yM) = (⊤ : Submodule R M) :=
    hfinM.choose_spec.choose_spec
  let tM : Fin mM → S := fun j => (hscalar (yM j)).choose
  let w : S := Finset.univ.prod tM
  have hw : ∀ j : Fin mM, (w : R) • yM j ∈ N0 := by
    intro j
    have ht : (tM j : R) • yM j ∈ N0 :=
      (hscalar (yM j)).choose_spec
    change ((↑(Finset.univ.prod tM) : R) • yM j) ∈ N0
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    simp only [Submonoid.coe_mul, mul_smul]
    exact N0.smul_mem _ ht
  have hwtop : (w : R) • (⊤ : Submodule R M) ≤ N0 := by
    rw [← hyM, Submodule.smul_span]
    apply Submodule.span_le.2
    rintro z ⟨m', ⟨j, rfl⟩, rfl⟩
    exact hw j
  refine ⟨(w : R), w.property, ?_⟩
  have hloc := Submodule.localized'_le_localized'_of_smul_le
    (Localization.Away (w : R)) (Submonoid.powers (w : R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (w : R)) M)
    ⟨(w : R), Submonoid.mem_powers (w : R)⟩ hwtop
  have htop : (⊤ : Submodule (Localization.Away (w : R))
      (LocalizedModule (Submonoid.powers (w : R)) M)) ≤
      N0.localized' (Localization.Away (w : R)) (Submonoid.powers (w : R))
        (LocalizedModule.mkLinearMap (Submonoid.powers (w : R)) M) := by
    simpa only [Submodule.localized'_top] using hloc
  have hEq := le_antisymm le_top htop
  rw [Submodule.localized'_span] at hEq
  have himagef : (LocalizedModule.mkLinearMap (Submonoid.powers (w : R)) M) ''
        Set.range x = Set.range (fun i =>
          LocalizedModule.mkLinearMap (Submonoid.powers (w : R)) M (x i)) := by
    ext z
    constructor
    · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  rw [himagef] at hEq
  exact hEq

/-- Special case `I = p` and `S = R \ p`: generators of the fibre
`M ⊗ κ(p)` generate `M_f` for some `f ∉ p`. -/
theorem nakayama_localization_at_prime
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (p : Ideal R) [p.IsPrime]
    [Module.Finite R M] (n : ℕ) (x : Fin n → M)
    (hx : Submodule.span p.ResidueField
      (Set.range (fun i => (1 : p.ResidueField) ⊗ₜ[R] x i)) = ⊤) :
    ∃ f : R, f ∉ p ∧
      Submodule.span (Localization.Away f)
        (Set.range (fun i =>
          LocalizedModule.mkLinearMap (Submonoid.powers f) M (x i))) = ⊤ := by
  let A := R ⧸ p
  let T : Submonoid A := p.primeCompl.map (Ideal.Quotient.mk p).toMonoidHom
  have hT : T = nonZeroDivisors A := by
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      rw [mem_nonZeroDivisors_iff_ne_zero]
      change Ideal.Quotient.mk p r ≠ 0
      intro hzero
      exact (Ideal.mem_primeCompl_iff.mp hr)
        (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    · intro hz
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hr : r ∉ p := by
        intro hrp
        have hz' : Ideal.Quotient.mk p r ≠ 0 := by
          rw [← mem_nonZeroDivisors_iff_ne_zero]
          exact hz
        exact hz' (Ideal.Quotient.eq_zero_iff_mem.mpr hrp)
      exact ⟨r, hr, rfl⟩
  haveI instLocalization : IsLocalization T p.ResidueField :=
    hT ▸ (inferInstance : IsLocalization (nonZeroDivisors A) p.ResidueField)
  let Q := M ⧸ (p • (⊤ : Submodule R M))
  haveI : TensorProduct.CompatibleSMul R A p.ResidueField Q :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (M := p.ResidueField) (N := Q) (by
        change Function.Surjective (Ideal.Quotient.mk p)
        exact Ideal.Quotient.mk_surjective)
  let eCompat : p.ResidueField ⊗[A] Q ≃ₗ[p.ResidueField]
      p.ResidueField ⊗[R] Q :=
    TensorProduct.equivOfCompatibleSMul R A p.ResidueField p.ResidueField Q
  let eCompatA : p.ResidueField ⊗[A] Q ≃ₗ[A]
      p.ResidueField ⊗[R] Q := eCompat.restrictScalars A
  let gA : Q →ₗ[A] p.ResidueField ⊗[A] Q :=
    TensorProduct.mk A p.ResidueField Q 1
  let g : Q →ₗ[A] p.ResidueField ⊗[R] Q :=
    eCompatA.toLinearMap.comp gA
  let qmap : p.ResidueField ⊗[R] M →ₗ[p.ResidueField]
      p.ResidueField ⊗[R] Q :=
    TensorProduct.AlgebraTensorModule.lTensor p.ResidueField
      p.ResidueField ((p • (⊤ : Submodule R M)).mkQ)
  have hg : ∀ z : M, g ((p • (⊤ : Submodule R M)).mkQ z) =
      qmap ((1 : p.ResidueField) ⊗ₜ[R] z) := by
    intro z
    change (1 : p.ResidueField) ⊗ₜ[R]
        (p • (⊤ : Submodule R M)).mkQ z =
      (1 : p.ResidueField) ⊗ₜ[R] (p • (⊤ : Submodule R M)).mkQ z
    rfl
  have hqmap : Function.Surjective qmap := by
    simpa [qmap] using
      (LinearMap.lTensor_surjective p.ResidueField
        (Submodule.mkQ_surjective (p • (⊤ : Submodule R M))))
  have himage : qmap '' Set.range (fun i =>
      (1 : p.ResidueField) ⊗ₜ[R] x i) = Set.range (fun i =>
        qmap ((1 : p.ResidueField) ⊗ₜ[R] x i)) := by
    ext z
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(1 : p.ResidueField) ⊗ₜ[R] x i, ⟨i, rfl⟩, rfl⟩
  have hmap :
      (Submodule.span p.ResidueField (Set.range (fun i =>
        (1 : p.ResidueField) ⊗ₜ[R] x i))).map qmap =
        Submodule.span p.ResidueField (Set.range (fun i =>
          qmap ((1 : p.ResidueField) ⊗ₜ[R] x i))) := by
    rw [Submodule.map_span, himage]
  have hxQ : Submodule.span p.ResidueField (Set.range (fun i =>
      qmap ((1 : p.ResidueField) ⊗ₜ[R] x i))) = ⊤ := by
    rw [← hmap, hx, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hqmap
  have himageG : g '' Set.range (fun i =>
      (p • (⊤ : Submodule R M)).mkQ (x i)) = Set.range (fun i =>
        g ((p • (⊤ : Submodule R M)).mkQ (x i))) := by
    ext z
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(p • (⊤ : Submodule R M)).mkQ (x i), ⟨i, rfl⟩, rfl⟩
  have hxG : Submodule.span p.ResidueField (Set.range (fun i =>
      g ((p • (⊤ : Submodule R M)).mkQ (x i)))) = ⊤ := by
    simpa only [hg] using hxQ
  let N : Submodule A Q := Submodule.span A (Set.range (fun i =>
    (p • (⊤ : Submodule R M)).mkQ (x i)))
  have hgenQ : ∀ y : Q, ∃ t : T, ∃ z ∈ N, (t : A) • y ∈ N := by
    intro y
    have hmem : g y ∈ Submodule.span p.ResidueField
        (g '' Set.range (fun i =>
          (p • (⊤ : Submodule R M)).mkQ (x i))) := by
      rw [himageG]
      rw [show Submodule.span p.ResidueField (Set.range (fun i =>
          g ((p • (⊤ : Submodule R M)).mkQ (x i)))) = ⊤ by exact hxG]
      exact Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span T
      p.ResidueField (g '' Set.range (fun i =>
        (p • (⊤ : Submodule R M)).mkQ (x i))) (g y) hmem
    have ht' : (t : A) • g y ∈ Submodule.map g N := by
      change (t : A) • g y ∈ Submodule.map g
        (Submodule.span A (Set.range (fun i =>
          (p • (⊤ : Submodule R M)).mkQ (x i))))
      rw [Submodule.map_span]
      exact ht
    obtain ⟨z, hz, hzt⟩ := ht'
    have heq0 : g z = g ((t : A) • y) := by
      simpa only [map_smul] using hzt
    obtain ⟨u, hu⟩ := (IsLocalizedModule.eq_iff_exists T g).mp heq0
    have hu' : (u : A) • ((t : A) • y) = (u : A) • z := by
      simpa [Submonoid.smul_def] using hu.symm
    refine ⟨u * t, z, hz, ?_⟩
    change (((u : A) * (t : A)) • y) ∈ N
    rw [← smul_smul, hu']
    exact N.smul_mem _ hz
  haveI instFiniteQ : Module.Finite A Q :=
    Module.Finite.of_restrictScalars_finite R A Q
  let hfinQ : ∃ m : ℕ, ∃ y : Fin m → Q,
      Submodule.span A (Set.range y) = (⊤ : Submodule A Q) :=
    Module.Finite.exists_fin
  let mQ := hfinQ.choose
  let yQ := hfinQ.choose_spec.choose
  have hyQ : Submodule.span A (Set.range yQ) = (⊤ : Submodule A Q) :=
    hfinQ.choose_spec.choose_spec
  let tQ : Fin mQ → T := fun j => (hgenQ (yQ j)).choose
  let wQ : T := Finset.univ.prod tQ
  have hwQ : ∀ j : Fin mQ, (wQ : A) • yQ j ∈ N := by
    intro j
    have ht : (tQ j : A) • yQ j ∈ N :=
      (hgenQ (yQ j)).choose_spec.choose_spec.2
    change ((↑(Finset.univ.prod tQ) : A) • yQ j) ∈ N
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    simp only [Submonoid.coe_mul, mul_smul]
    exact N.smul_mem _ ht
  have hwtop : (wQ : A) • (⊤ : Submodule A Q) ≤ N := by
    rw [← hyQ, Submodule.smul_span]
    apply Submodule.span_le.2
    rintro z ⟨j, ⟨j', rfl⟩, rfl⟩
    exact hwQ j'
  have hlocQ := Submodule.localized'_le_localized'_of_smul_le
    (Localization T) T (LocalizedModule.mkLinearMap T Q)
    wQ hwtop
  have htopQ : (⊤ : Submodule (Localization T)
      (LocalizedModule T Q)) ≤
      N.localized' (Localization T) T (LocalizedModule.mkLinearMap T Q) := by
    simpa only [Submodule.localized'_top] using hlocQ
  have hEqQ := le_antisymm le_top htopQ
  rw [Submodule.localized'_span] at hEqQ
  have himageQ : (LocalizedModule.mkLinearMap T Q) ''
        Set.range (fun i => (p • (⊤ : Submodule R M)).mkQ (x i)) =
      Set.range (fun i => LocalizedModule.mkLinearMap T Q
        ((p • (⊤ : Submodule R M)).mkQ (x i))) := by
    ext z
    constructor
    · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(p • (⊤ : Submodule R M)).mkQ (x i), ⟨i, rfl⟩, rfl⟩
  rw [himageQ] at hEqQ
  have hloc := nakayama_localization p.primeCompl p n x (by
    simpa [A, T, Q] using hEqQ)
  obtain ⟨f, hf, hgen⟩ := hloc
  refine ⟨f, ?_, hgen⟩
  rcases hf with ⟨s, hs, i, hi, rfl⟩
  intro hsi
  apply (Ideal.mem_primeCompl_iff.mp hs)
  simpa [add_sub_cancel_right] using p.sub_mem hsi hi

/-! ## Surjectivity criterion for a local homomorphism -/

private theorem maximalIdeal_element_mem_sup
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (mA : Ideal A) (mB : Ideal B) (N : Submodule B mB)
    (hN : N = Submodule.comap mB.subtype (Ideal.map (Algebra.ofId A B) mA))
    (hmax : mA ≤ mB.comap (algebraMap A B))
    (hmaxId : mA ≤ mB.comap (Algebra.ofId A B))
    (hcot : Function.Surjective
      (Ideal.mapCotangent mA mB (Algebra.ofId A B) hmaxId))
    (b : mB) : b ∈ N ⊔ mB • (⊤ : Submodule B mB) := by
  obtain ⟨a0, ha0⟩ := hcot (mB.toCotangent b)
  obtain ⟨a, rfl⟩ := mA.toCotangent_surjective a0
  have haB : algebraMap A B (a : A) ∈ mB := hmax a.property
  have hab : mB.toCotangent b =
      mB.toCotangent ⟨(Algebra.ofId A B) (a : A), hmaxId a.property⟩ := by
    calc
      mB.toCotangent b =
          Ideal.mapCotangent mA mB (Algebra.ofId A B) hmaxId
            (mA.toCotangent a) := ha0.symm
      _ = mB.toCotangent ⟨(Algebra.ofId A B) (a : A), hmaxId a.property⟩ :=
        Ideal.mapCotangent_toCotangent mA mB (Algebra.ofId A B) hmaxId a
  have hdiff : ((b : B) - algebraMap A B (a : A)) ∈ mB ^ 2 :=
    (mB.toCotangent_eq).mp (by simpa only [Algebra.ofId_apply] using hab)
  have hdiff' : ((b : B) - algebraMap A B (a : A)) ∈
      mB • (mB : Ideal B) := by
    simpa [Ideal.smul_eq_mul, pow_two] using hdiff
  let d : mB := ⟨(b : B) - algebraMap A B (a : A),
    mB.sub_mem b.property haB⟩
  have hd : d ∈ mB • (⊤ : Submodule B mB) := by
    rw [Submodule.mem_smul_top_iff]
    exact hdiff'
  have haN : (⟨algebraMap A B (a : A), haB⟩ : mB) ∈ N := by
    rw [hN]
    exact Submodule.mem_comap.mpr
      (Ideal.mem_map_of_mem (Algebra.ofId A B) a.property)
  refine Submodule.mem_sup.mpr
    ⟨⟨algebraMap A B (a : A), haB⟩, haN, d, hd, ?_⟩
  apply Subtype.ext
  change algebraMap A B (a : A) +
    ((b : B) - algebraMap A B (a : A)) = (b : B)
  ring

private theorem maximalIdeal_map_eq_of_cotangent_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hB : (IsLocalRing.maximalIdeal B).FG)
    (hcot : Function.Surjective
      (Ideal.mapCotangent (IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal B) (Algebra.ofId A B)
        (by
          change IsLocalRing.maximalIdeal A ≤
            (IsLocalRing.maximalIdeal B).comap (algebraMap A B)
          rw [IsLocalRing.maximalIdeal_comap]))) :
    Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B := by
  let mA : Ideal A := IsLocalRing.maximalIdeal A
  let mB : Ideal B := IsLocalRing.maximalIdeal B
  have hmax : mA ≤ mB.comap (algebraMap A B) := by
    dsimp [mA, mB]
    rw [IsLocalRing.maximalIdeal_comap]
  have hmaxId : mA ≤ mB.comap (Algebra.ofId A B) := by
    intro a ha
    change algebraMap A B a ∈ mB
    exact hmax ha
  let N : Submodule B mB :=
    Submodule.comap mB.subtype (Ideal.map (Algebra.ofId A B) mA)
  have hcot' : Function.Surjective
      (Ideal.mapCotangent mA mB (Algebra.ofId A B) hmaxId) := by
    simpa [mA, mB] using hcot
  have hNN : (⊤ : Submodule B mB) ≤ N ⊔ mB • (⊤ : Submodule B mB) := by
    intro b hb
    exact maximalIdeal_element_mem_sup mA mB N rfl hmax hmaxId hcot' b
  have htopfg : (⊤ : Submodule B mB).FG := (Submodule.fg_top _).mpr hB
  have hIJ : mB ≤ (⊥ : Ideal B).jacobson := by
    exact IsLocalRing.maximalIdeal_le_jacobson (R := B) (⊥ : Ideal B)
  have hNtop : (⊤ : Submodule B mB) ≤ N :=
    Submodule.le_of_le_smul_of_le_jacobson_bot htopfg hIJ hNN
  have hmap_eq : Ideal.map (algebraMap A B) mA = mB := by
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.mpr hmax
    · intro b hb
      have hbN : (⟨b, hb⟩ : mB) ∈ N := hNtop (Submodule.mem_top)
      exact Submodule.mem_comap.mp hbN
  simpa [mA, mB] using hmap_eq

private theorem residue_quotient_map_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (mA : Ideal A) (mB : Ideal B)
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap A B)))
    (hmap_eq : Ideal.map (algebraMap A B) mA = mB)
    (hmB : mB = IsLocalRing.maximalIdeal B) :
    Function.Surjective
      ((mA • (⊤ : Submodule A A)).mapQ
        (mA • (⊤ : Submodule A B)) (Algebra.linearMap A B)
        (Submodule.smul_top_le_comap_smul_top mA (Algebra.linearMap A B))) := by
  intro z
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (mA • (⊤ : Submodule A B)) z
  obtain ⟨r, hr⟩ := hres.2 (IsLocalRing.residue B b)
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective r
  have hab : IsLocalRing.residue B (algebraMap A B a) =
      IsLocalRing.residue B b := by
    calc
      IsLocalRing.residue B (algebraMap A B a) =
          algebraMap (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField B) (IsLocalRing.residue A a) := by
        symm
        exact IsLocalRing.ResidueField.algebraMap_residue a
      _ = algebraMap (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField B) r := by rw [ha]
      _ = IsLocalRing.residue B b := hr
  have hdiff : b - algebraMap A B a ∈ mB := by
    have hdiff₀ : b - algebraMap A B a ∈ IsLocalRing.maximalIdeal B := by
      apply (IsLocalRing.residue_eq_zero_iff (b - algebraMap A B a)).mp
      rw [map_sub, hab, sub_self]
    simpa [hmB] using hdiff₀
  have hdiff' : b - algebraMap A B a ∈ mA • (⊤ : Submodule A B) := by
    rw [Ideal.smul_top_eq_map]
    rw [hmap_eq]
    exact hdiff
  refine ⟨(mA • (⊤ : Submodule A A)).mkQ a, ?_⟩
  change (mA • (⊤ : Submodule A B)).mkQ (algebraMap A B a) =
    (mA • (⊤ : Submodule A B)).mkQ b
  apply (Submodule.Quotient.eq (mA • (⊤ : Submodule A B))).2
  have hdiff'' : algebraMap A B a - b ∈ mA • (⊤ : Submodule A B) := by
    simpa [neg_sub] using (mA • (⊤ : Submodule A B)).neg_mem hdiff'
  exact hdiff''

private theorem local_ring_hom_surjective_of_residue_quotient_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    (hres : Function.Surjective
      ((IsLocalRing.maximalIdeal A • (⊤ : Submodule A A)).mapQ
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A B))
        (Algebra.linearMap A B)
        (Submodule.smul_top_le_comap_smul_top
          (IsLocalRing.maximalIdeal A) (Algebra.linearMap A B)))) :
    Function.Surjective (algebraMap A B) := by
  have hI : IsLocalRing.maximalIdeal A ≤ Ring.jacobson A := by
    simpa only [Ideal.jacobson_bot] using
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A))
  have hsurj : Function.Surjective (Algebra.linearMap A B) := by
    exact nakayama_part_six (R := A) (M := B) (N := A)
      (IsLocalRing.maximalIdeal A) (Algebra.linearMap A B) hres hI
  exact hsurj

/-- A local map satisfying the four hypotheses in the source is surjective.
The cotangent spaces use Mathlib's canonical `Ideal.Cotangent` interface. -/
theorem local_ring_hom_surjective_of_residueField_bijective_of_cotangent_surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    (hB : (IsLocalRing.maximalIdeal B).FG)
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap A B)))
    (hcot : Function.Surjective
      (Ideal.mapCotangent (IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal B) (Algebra.ofId A B)
    (by
          change IsLocalRing.maximalIdeal A ≤
            (IsLocalRing.maximalIdeal B).comap (algebraMap A B)
          rw [IsLocalRing.maximalIdeal_comap]))) :
    Function.Surjective (algebraMap A B) := by
  have hmap_eq :
      Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
        IsLocalRing.maximalIdeal B :=
    maximalIdeal_map_eq_of_cotangent_surjective hB hcot
  apply local_ring_hom_surjective_of_residue_quotient_surjective
  exact residue_quotient_map_surjective
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
    hres hmap_eq rfl

end

end Formalization.Books.Algebra.Unit20
