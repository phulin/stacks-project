import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.Torsion.Basic
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
  sorry

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
  sorry

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
  sorry

/-! ## Surjectivity criterion for a local homomorphism -/

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
  sorry

end

end Formalization.Books.Algebra.Unit20
