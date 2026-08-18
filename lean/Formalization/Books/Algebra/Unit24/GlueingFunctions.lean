import Formalization.Books.Algebra.Unit09.Localization
import Formalization.Books.Algebra.Unit21.OpenAndClosed
import Formalization.Books.Algebra.Unit23.GlueingProperties
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Away.Lemmas

/-!
# Commutative Algebra, Chapter 24: Glueing functions

Finite direct sums in the source are represented by finite dependent products.
For an intersection of two standard opens, `localizationProduct` is used: it
is Mathlib's canonical joint localization at the two powers submonoids.
-/

namespace Formalization.Books.Algebra.Unit24

universe u v

noncomputable section

open Set

/-! ## The localization sequence for a standard-open cover -/

/-- The joint localization used on the intersection of the `i`th and `j`th
standard opens. -/
abbrev standardCoverJointSubmonoid {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (i j : Fin n) : Submonoid R :=
  Formalization.Books.Algebra.Unit09.localizationProduct
    (Submonoid.powers (f i)) (Submonoid.powers (f j))

/-- The module localized on the `i`th standard open. -/
abbrev standardCoverLocalModule {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M]
    (i : Fin n) : Type (max u v) :=
  LocalizedModule.Away (f i) M

/-- The module localized on the intersection of two standard opens. -/
abbrev standardCoverJointModule {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M]
    (i j : Fin n) : Type (max u v) :=
  LocalizedModule (standardCoverJointSubmonoid f i j) M

/-- The canonical map from the `i`th localization to the joint localization
on the `i,j` intersection. -/
noncomputable def standardCoverLocalizeLeft {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M]
    (i j : Fin n) :
    standardCoverLocalModule f M i →ₗ[R] standardCoverJointModule f M i j :=
  LocalizedModule.liftOfLE (Submonoid.powers (f i))
    (standardCoverJointSubmonoid f i j) (by exact le_sup_left)

/-- The canonical map from the `j`th localization to the joint localization
on the `i,j` intersection. -/
noncomputable def standardCoverLocalizeRight {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M]
    (i j : Fin n) :
    standardCoverLocalModule f M j →ₗ[R] standardCoverJointModule f M i j :=
  LocalizedModule.liftOfLE (Submonoid.powers (f j))
    (standardCoverJointSubmonoid f i j) (by exact le_sup_right)

/-- The map sending a module element to all of its standard-open localizations. -/
noncomputable def standardCoverModuleAlpha {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M] :
    M →ₗ[R] (∀ i : Fin n, standardCoverLocalModule f M i) :=
  LinearMap.pi fun i => LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M

/-- The difference map on one ordered pair of standard opens. -/
noncomputable def standardCoverModuleDifference {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M]
    (i j : Fin n) :
    (∀ k : Fin n, standardCoverLocalModule f M k) →ₗ[R]
      standardCoverJointModule f M i j :=
  (standardCoverLocalizeLeft f M i j).comp (LinearMap.proj i) -
    (standardCoverLocalizeRight f M i j).comp (LinearMap.proj j)

/-- The map of pairwise differences in the localization sequence. -/
noncomputable def standardCoverModuleBeta {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M] :
    (∀ i : Fin n, standardCoverLocalModule f M i) →ₗ[R]
      (∀ p : Fin n × Fin n, standardCoverJointModule f M p.1 p.2) :=
  LinearMap.pi fun p : Fin n × Fin n =>
    standardCoverModuleDifference f M p.1 p.2

@[simp]
theorem standardCoverModuleAlpha_apply {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M]
    (m : M) (i : Fin n) :
    standardCoverModuleAlpha f M m i =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m :=
  rfl

@[simp]
theorem standardCoverModuleDifference_apply {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M]
    (x : ∀ k : Fin n, standardCoverLocalModule f M k) (i j : Fin n) :
    standardCoverModuleDifference f M i j x =
      standardCoverLocalizeLeft f M i j (x i) -
        standardCoverLocalizeRight f M i j (x j) :=
  rfl

@[simp]
theorem standardCoverModuleBeta_apply {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M]
    (x : ∀ i : Fin n, standardCoverLocalModule f M i) (i j : Fin n) :
    standardCoverModuleBeta f M x (i, j) =
      standardCoverLocalizeLeft f M i j (x i) -
        standardCoverLocalizeRight f M i j (x j) :=
  rfl

/-- The localization sequence for a finite standard-open cover of a module is
exact. -/
/- TODO(proof agents): prove this algebraic lemma before the geometric Čech theorem.
First add a denominator-clearing lemma for equality in `LocalizedModule`, then a
finite uniform-exponent lemma using `Ideal.span (Set.range f) = ⊤`.  Use those
to prove injectivity, and to glue a compatible family after multiplying its
components to a common denominator.  The resulting numerator, expressed using
a power of the cover relation, gives exactness at the middle term. -/
theorem cover_module_exact {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (hf : Ideal.span (Set.range f) = ⊤)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Injective (standardCoverModuleAlpha f M) ∧
      Function.Exact (standardCoverModuleAlpha f M) (standardCoverModuleBeta f M) := by
  classical
  have hpow_mem : ∀ (z : M), (∀ i : Fin n, ∃ e : ℕ, (f i) ^ e • z = 0) → z = 0 := by
    intro z hz
    choose e he using hz
    let N : ℕ := ∑ i, e i
    have hle (i : Fin n) : e i ≤ N := by
      dsimp [N]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hkill (i : Fin n) : (f i) ^ N • z = 0 := by
      rw [← Nat.sub_add_cancel (hle i), pow_add, mul_smul]
      simp [he i]
    have hspan : Ideal.span ((fun x : R => x ^ N) '' Set.range f) = ⊤ :=
      Ideal.span_pow_eq_top (Set.range f) hf N
    have hle_torsion :
        Ideal.span ((fun x : R => x ^ N) '' Set.range f) ≤ Ideal.torsionOf R M z := by
      rw [Ideal.span_le]
      rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
      exact (Ideal.mem_torsionOf_iff z _).2 (hkill i)
    have htorsion : Ideal.torsionOf R M z = ⊤ :=
      top_unique (hspan.ge.trans hle_torsion)
    exact (Ideal.torsionOf_eq_top_iff R z).mp htorsion
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hpow_mem (x - y)
    intro i
    have hi := congrFun hxy i
    simp only [standardCoverModuleAlpha_apply] at hi
    have hi' :
        LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M (x - y) = 0 := by
      rw [map_sub, hi, sub_self]
    rcases LocalizedModule.mem_ker_mkLinearMap_iff.mp (LinearMap.mem_ker.mpr hi') with
      ⟨s, hs, hsz⟩
    obtain ⟨e, he⟩ := (Submonoid.mem_powers_iff _ _).mp hs
    refine ⟨e, ?_⟩
    rw [he]
    exact hsz
  have hrep (i : Fin n) (z : standardCoverLocalModule f M i) :
      ∃ m : M, ∃ s : Submonoid.powers (f i), LocalizedModule.mk m s = z := by
    induction z using LocalizedModule.induction_on with
    | _ m s => exact ⟨m, s, rfl⟩
  · intro x
    constructor
    · intro hx
      choose m s hs using fun i => hrep i (x i)
      choose e he using fun i => (Submonoid.mem_powers_iff _ _).mp (s i).property
      let N : ℕ := ∑ i, e i
      have hle (i : Fin n) : e i ≤ N := by
        dsimp [N]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      let powSub (i : Fin n) (k : ℕ) : Submonoid.powers (f i) :=
        ⟨(f i) ^ k, (Submonoid.mem_powers_iff _ _).2 ⟨k, rfl⟩⟩
      have hse (i : Fin n) : s i = powSub i (e i) := by
        apply Subtype.ext
        exact (he i).symm
      have hcommon (i : Fin n) :
          x i = LocalizedModule.mk (powSub i (N - e i) • m i) (powSub i N) := by
        rw [← hs i, hse i]
        symm
        simpa [powSub, ← pow_add, Nat.sub_add_cancel (hle i)] using
          (LocalizedModule.mk_cancel_common_left (powSub i (N - e i))
            (powSub i (e i)) (m i))
      have hleft (i j : Fin n) (a : M) (s : Submonoid.powers (f i)) :
          standardCoverLocalizeLeft f M i j (LocalizedModule.mk a s) =
            LocalizedModule.mk a
              ⟨(s : R), (show Submonoid.powers (f i) ≤ standardCoverJointSubmonoid f i j
                from le_sup_left) s.property⟩ := by
        change LocalizedModule.liftOfLE (Submonoid.powers (f i))
          (standardCoverJointSubmonoid f i j) (by
            change Submonoid.powers (f i) ≤
              Submonoid.powers (f i) ⊔ Submonoid.powers (f j)
            exact le_sup_left)
          (LocalizedModule.mk a s) = _
        rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk',
          IsLocalizedModule.mk_eq_mk']
      have hright (i j : Fin n) (a : M) (s : Submonoid.powers (f j)) :
          standardCoverLocalizeRight f M i j (LocalizedModule.mk a s) =
            LocalizedModule.mk a
              ⟨(s : R), (show Submonoid.powers (f j) ≤ standardCoverJointSubmonoid f i j
                from le_sup_right) s.property⟩ := by
        change LocalizedModule.liftOfLE (Submonoid.powers (f j))
          (standardCoverJointSubmonoid f i j) (by
            change Submonoid.powers (f j) ≤
              Submonoid.powers (f i) ⊔ Submonoid.powers (f j)
            exact le_sup_right)
          (LocalizedModule.mk a s) = _
        rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk',
          IsLocalizedModule.mk_eq_mk']
      have hcompat (i j : Fin n) :
          standardCoverLocalizeLeft f M i j (x i) =
            standardCoverLocalizeRight f M i j (x j) := by
        have hp := congrFun hx (i, j)
        simp only [standardCoverModuleBeta_apply] at hp
        apply sub_eq_zero.mp hp
      have hpair (i j : Fin n) :
          ∃ a b : ℕ,
            ((f i) ^ a * (f j) ^ b) •
                ((f j) ^ N • (powSub i (N - e i) • m i) -
                  (f i) ^ N • (powSub j (N - e j) • m j)) = 0 := by
        have hp := hcompat i j
        rw [hcommon i, hcommon j, hleft, hright] at hp
        rcases LocalizedModule.mk_eq.mp hp with ⟨u, hu⟩
        obtain ⟨ui, uj, huij⟩ :=
          (Formalization.Books.Algebra.Unit09.localizationProduct_mem_iff
            (Submonoid.powers (f i)) (Submonoid.powers (f j)) (u : R)).mp u.property
        obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).mp ui.property
        obtain ⟨b, hb⟩ := (Submonoid.mem_powers_iff _ _).mp uj.property
        refine ⟨a, b, ?_⟩
        have hu' :
            ((u : R) • ((powSub j N : R) • (powSub i (N - e i) • m i))) =
              (u : R) • ((powSub i N : R) • (powSub j (N - e j) • m j)) := by
          simpa only [Submonoid.smul_def] using hu
        rw [← huij, ← ha, ← hb] at hu'
        dsimp [powSub] at hu'
        simpa only [smul_sub, Submonoid.smul_def] using sub_eq_zero.mpr hu'
      choose a b hab using hpair
      let K : ℕ := ∑ i, ∑ j, b i j
      have hble (p : Fin n × Fin n) : b p.1 p.2 ≤ K := by
        dsimp [K]
        calc
          b p.1 p.2 ≤ ∑ j, b p.1 j :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
          _ ≤ ∑ i, ∑ j, b i j :=
            Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
              (f := fun i => ∑ j, b i j) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ p.1)
      let A : ℕ := ∑ i, ∑ j, a i j
      have hale (p : Fin n × Fin n) : a p.1 p.2 ≤ A := by
        dsimp [A]
        calc
          a p.1 p.2 ≤ ∑ j, a p.1 j :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
          _ ≤ ∑ i, ∑ j, a i j :=
            Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
              (f := fun i => ∑ j, a i j) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ p.1)
      let L : ℕ := N + K
      have hspan : Ideal.span (Set.range (fun i : Fin n => (f i) ^ L)) = ⊤ := by
        have hsset :
            Set.range (fun i : Fin n => (f i) ^ L) =
              (fun x : R => x ^ L) '' Set.range f := by
          ext z
          constructor
          · rintro ⟨i, rfl⟩
            exact ⟨f i, ⟨i, rfl⟩, rfl⟩
          · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
            exact ⟨i, rfl⟩
        rw [hsset]
        exact Ideal.span_pow_eq_top (Set.range f) hf L
      have hone : (1 : R) ∈ Ideal.span (Set.range (fun i : Fin n => (f i) ^ L)) := by
        rw [hspan]
        exact Submodule.mem_top
      obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hone
      let q : Fin n → M := fun j => powSub j (N - e j) • m j
      let glue : M :=
        ∑ j, c j • (powSub j K • q j)
      have hpair_common (i j : Fin n) :
          (f i) ^ A • ((f i) ^ N • (c j • ((f j) ^ K • q j))) =
            (f i) ^ A • ((c j * (f j) ^ L) • q i) := by
        have h := congrArg
          (fun z : M =>
            (c j * (f i) ^ (A - a i j) * (f j) ^ (K - b i j)) • z) (hab i j)
        have h' :
            (c j * (f i) ^ (A - a i j) * (f j) ^ (K - b i j) *
                ((f i) ^ a i j * (f j) ^ b i j)) •
              ((f j) ^ N • q i - (f i) ^ N • q j) = 0 := by
          simpa only [q, ← mul_smul, smul_zero] using h
        rw [smul_sub] at h'
        have h'' := sub_eq_zero.mp h'
        have hcoeff :
            c j * (f i) ^ (A - a i j) * (f j) ^ (K - b i j) *
                ((f i) ^ a i j * (f j) ^ b i j) =
              c j * (f i) ^ A * (f j) ^ K := by
          have hAi : (f i) ^ (A - a i j) * (f i) ^ a i j = (f i) ^ A := by
            rw [← pow_add, Nat.sub_add_cancel (hale (i, j))]
          have hKj : (f j) ^ (K - b i j) * (f j) ^ b i j = (f j) ^ K := by
            rw [← pow_add, Nat.sub_add_cancel (hble (i, j))]
          calc
            c j * (f i) ^ (A - a i j) * (f j) ^ (K - b i j) *
                ((f i) ^ a i j * (f j) ^ b i j) =
                c j * ((f i) ^ (A - a i j) * (f i) ^ a i j) *
                  ((f j) ^ (K - b i j) * (f j) ^ b i j) := by ring
            _ = c j * (f i) ^ A * (f j) ^ K := by rw [hAi, hKj]
        rw [hcoeff] at h''
        calc
          (f i) ^ A • ((f i) ^ N • (c j • ((f j) ^ K • q j))) =
              (c j * (f i) ^ A * (f j) ^ K) • ((f i) ^ N • q j) := by
                simp only [← mul_smul]
                congr 1
                ring
          _ = (c j * (f i) ^ A * (f j) ^ K) • ((f j) ^ N • q i) := h''.symm
          _ = (f i) ^ A • ((c j * (f j) ^ L) • q i) := by
                simp only [← mul_smul]
                congr 1
                simp only [L, pow_add]
                ring
      have hsum (i : Fin n) :
          (f i) ^ A • ((f i) ^ N • glue) = (f i) ^ A • q i := by
        dsimp [glue]
        simp only [Finset.smul_sum]
        calc
          ∑ j, (f i) ^ A • ((f i) ^ N • (c j • ((f j) ^ K • q j))) =
              ∑ j, (f i) ^ A • ((c j * (f j) ^ L) • q i) := by
                apply Finset.sum_congr rfl
                intro j hj
                exact hpair_common i j
          _ = (f i) ^ A • ((∑ j, c j * (f j) ^ L) • q i) := by
            simp only [← Finset.smul_sum, ← Finset.sum_smul]
          _ = (f i) ^ A • q i := by rw [hc, one_smul]
      refine ⟨glue, ?_⟩
      funext i
      rw [standardCoverModuleAlpha_apply, hcommon i]
      apply LocalizedModule.mk_eq.mpr
      refine ⟨powSub i A, ?_⟩
      simpa only [Submonoid.smul_def, powSub, q, one_smul] using hsum i
    · rintro ⟨m, rfl⟩
      apply funext
      intro p
      change
        standardCoverLocalizeLeft f M p.1 p.2
            (LocalizedModule.mk m (1 : Submonoid.powers (f p.1))) -
          standardCoverLocalizeRight f M p.1 p.2
            (LocalizedModule.mk m (1 : Submonoid.powers (f p.2))) = 0
      have hleft0 :
          standardCoverLocalizeLeft f M p.1 p.2
              (LocalizedModule.mk m (1 : Submonoid.powers (f p.1))) =
            LocalizedModule.mk m
              ⟨(1 : R), (show Submonoid.powers (f p.1) ≤
                standardCoverJointSubmonoid f p.1 p.2 from le_sup_left)
                (Submonoid.powers (f p.1)).one_mem⟩ := by
        change LocalizedModule.liftOfLE (Submonoid.powers (f p.1))
          (standardCoverJointSubmonoid f p.1 p.2) (by
            change Submonoid.powers (f p.1) ≤
              Submonoid.powers (f p.1) ⊔ Submonoid.powers (f p.2)
            exact le_sup_left)
          (LocalizedModule.mk m (1 : Submonoid.powers (f p.1))) = _
        rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk',
          IsLocalizedModule.mk_eq_mk']
        rfl
      have hright0 :
          standardCoverLocalizeRight f M p.1 p.2
              (LocalizedModule.mk m (1 : Submonoid.powers (f p.2))) =
            LocalizedModule.mk m
              ⟨(1 : R), (show Submonoid.powers (f p.2) ≤
                standardCoverJointSubmonoid f p.1 p.2 from le_sup_right)
                (Submonoid.powers (f p.2)).one_mem⟩ := by
        change LocalizedModule.liftOfLE (Submonoid.powers (f p.2))
          (standardCoverJointSubmonoid f p.1 p.2) (by
            change Submonoid.powers (f p.2) ≤
              Submonoid.powers (f p.1) ⊔ Submonoid.powers (f p.2)
            exact le_sup_right)
          (LocalizedModule.mk m (1 : Submonoid.powers (f p.2))) = _
        rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk',
          IsLocalizedModule.mk_eq_mk']
        rfl
      rw [hleft0, hright0, sub_self]

/-! ## The ring specialization -/

/-- The ring case of the localization sequence is the module case for `M = R`. -/
theorem standard_covering_exact {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (standardCoverModuleAlpha f R) ∧
      Function.Exact (standardCoverModuleAlpha f R) (standardCoverModuleBeta f R) := by
  exact cover_module_exact f hf R

/-! ## Disjoint open decompositions -/

/-- A disjoint open decomposition of a spectrum is the product decomposition
coming from a complementary idempotent.  The two factors are displayed both
as localizations and as quotients of the original ring. -/
theorem disjoint_implies_product {R : Type u} [CommRing R]
    {U V : Set (PrimeSpectrum R)}
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hcover : U ∪ V = Set.univ) :
    ∃ e : R, IsIdempotentElem e ∧
      U = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) ∧
      V = (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum R)) ∧
      Nonempty (R ≃+* (Localization.Away e × Localization.Away (1 - e))) ∧
      Nonempty ((U : Type u) ≃ₜ PrimeSpectrum (Localization.Away e)) ∧
      Nonempty ((V : Type u) ≃ₜ PrimeSpectrum (Localization.Away (1 - e))) ∧
      Nonempty (Localization.Away e ≃+* R ⧸ Ideal.span ({1 - e} : Set R)) ∧
      Nonempty (Localization.Away (1 - e) ≃+* R ⧸ Ideal.span ({e} : Set R)) := by
  have hUcompl : Uᶜ = V := by
    apply Set.Subset.antisymm
    · intro p hp
      have hp' : p ∈ U ∪ V := by
        rw [hcover]
        trivial
      exact hp'.resolve_left hp
    · intro p hp hpU
      exact (Set.disjoint_left.1 hdisj) hpU hp
  have hVcompl : Vᶜ = U := by
    simpa only [compl_compl] using congrArg (fun s : Set (PrimeSpectrum R) => sᶜ)
      hUcompl.symm
  have hUclopen : IsClopen U :=
    ⟨by rw [← hVcompl]; exact hV.isClosed_compl, hU⟩
  obtain ⟨e, ⟨he, hUe⟩, -⟩ :=
    Formalization.Books.Algebra.Unit21.existsUnique_idempotent_basicOpen_eq_of_isClopen
      hUclopen
  have hpartition := Formalization.Books.Algebra.Unit21.idempotent_spec_partition e he
  have hbasic_compl :
      (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R))ᶜ =
        (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum R)) := by
    apply Set.Subset.antisymm
    · intro p hp
      have hp' : p ∈
          (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) ∪
            (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum R)) := by
        rw [hpartition.2]
        trivial
      exact hp'.resolve_left hp
    · intro p hp hp0
      exact (Set.disjoint_left.1 hpartition.1) hp0 hp
  have hVe : V = (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum R)) := by
    calc
      V = Uᶜ := hUcompl.symm
      _ = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R))ᶜ := by rw [hUe]
      _ = (PrimeSpectrum.basicOpen (1 - e) : Set (PrimeSpectrum R)) := hbasic_compl
  letI : IsLocalization.Away e (R ⧸ Ideal.span ({1 - e} : Set R)) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  letI : IsLocalization.Away (1 - e) (R ⧸ Ideal.span ({e} : Set R)) := by
    have h := IsLocalization.Away.quotient_of_isIdempotentElem he.one_sub
    rw [sub_sub_cancel] at h
    exact h
  let awayE : Localization.Away e ≃+* R ⧸ Ideal.span ({1 - e} : Set R) :=
    (IsLocalization.algEquiv (Submonoid.powers e) (Localization.Away e)
      (R ⧸ Ideal.span ({1 - e} : Set R))).toRingEquiv
  let awayOneSub : Localization.Away (1 - e) ≃+* R ⧸ Ideal.span ({e} : Set R) :=
    (IsLocalization.algEquiv (Submonoid.powers (1 - e))
      (Localization.Away (1 - e)) (R ⧸ Ideal.span ({e} : Set R))).toRingEquiv
  refine ⟨e, he, hUe, hVe, ?_, ?_, ?_, ⟨awayE⟩, ⟨awayOneSub⟩⟩
  · let qprod : R ≃+* (R ⧸ Ideal.span ({1 - e} : Set R)) ×
        (R ⧸ Ideal.span ({e} : Set R)) :=
      (AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
        (by ring) (by simpa using he.one_sub_mul_self)).toRingEquiv
    exact ⟨qprod.trans (RingEquiv.prodCongr awayE.symm awayOneSub.symm)⟩
  · exact ⟨(Homeomorph.setCongr hUe).trans
      (Formalization.Books.Algebra.Unit17.standardOpenSpectrumHomeomorph e).symm⟩
  · exact ⟨(Homeomorph.setCongr hVe).trans
      (Formalization.Books.Algebra.Unit17.standardOpenSpectrumHomeomorph (1 - e)).symm⟩

/-! ## Injectivity on a standard-open cover -/

/-- Multiplication by each member of a finite standard-open cover, collected
as a single linear map. -/
def standardCoverMultiplicationMap {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M] :
    M →ₗ[R] (Fin n → M) where
  toFun m i := (f i) • m
  map_add' m m' := by
    ext i
    simp
  map_smul' r m := by
    ext i
    change (f i) • (r • m) = r • ((f i) • m)
    rw [smul_smul, smul_smul, mul_comm]

/-- The map to the product of localizations is injective exactly when
multiplication by the cover elements is jointly injective. -/
theorem injective_covering_iff {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Injective (standardCoverModuleAlpha f M) ↔
      Function.Injective (standardCoverMultiplicationMap f M) := by
  classical
  have hpow : ∀ (hμ : Function.Injective (standardCoverMultiplicationMap f M))
      (k : ℕ) (e : Fin n → ℕ) (z : M),
      (∑ i, e i = k) →
        (∀ i, (f i) ^ e i • z = 0) → z = 0 := by
    intro hμ k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro e z hsum he
        by_cases hz : ∃ i, e i = 0
        · obtain ⟨i, hi⟩ := hz
          simpa [hi] using he i
        · by_cases hlarge : ∃ i, 1 < e i
          · obtain ⟨i, hi⟩ := hlarge
            let e' : Fin n → ℕ := Function.update e i (e i - 1)
            have hsum_erase :
                (∑ j ∈ ((Finset.univ : Finset (Fin n)).erase i), e j) + e i = k := by
              calc
                (∑ j ∈ ((Finset.univ : Finset (Fin n)).erase i), e j) + e i =
                    ∑ j, e j := Finset.sum_erase_add _ _ (Finset.mem_univ i)
                _ = k := hsum
            have hsum' : ∑ j, e' j = k - 1 := by
              dsimp [e']
              rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
              have hsum_erase' :
                  (∑ x ∈ (Finset.univ : Finset (Fin n)) \ {i}, e x) + e i = k := by
                have h := hsum_erase
                rw [Finset.erase_eq] at h
                exact h
              omega
            have he' : ∀ j, (f j) ^ e' j • ((f i) • z) = 0 := by
              intro j
              by_cases hji : j = i
              · subst j
                simp [e']
                rw [← mul_smul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
                  (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hi)))]
                exact he i
              · simp [e', hji]
                rw [← mul_smul, mul_comm, mul_smul, he j, smul_zero]
            have hzi : (f i) • z = 0 := by
              have hkpos : 0 < k := by
                have hle : e i ≤ ∑ j, e j :=
                  Finset.single_le_sum (fun _ _ => Nat.zero_le _)
                    (Finset.mem_univ i)
                rw [hsum] at hle
                omega
              exact ih (k - 1) (Nat.sub_lt hkpos Nat.zero_lt_one) e' ((f i) • z)
                hsum' he'
            let e'' : Fin n → ℕ := Function.update e i 1
            have hsum'' : ∑ j, e'' j < k := by
              dsimp [e'']
              rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
              have hsum_erase' :
                  (∑ x ∈ (Finset.univ : Finset (Fin n)) \ {i}, e x) + e i = k := by
                have h := hsum_erase
                rw [Finset.erase_eq] at h
                exact h
              omega
            have he'' : ∀ j, (f j) ^ e'' j • z = 0 := by
              intro j
              by_cases hji : j = i
              · subst j
                simp [e'', hzi]
              · simpa [e'', hji] using he j
            exact ih (∑ j, e'' j) hsum'' e'' z rfl he''
          · have hone : ∀ i, e i = 1 := by
              intro i
              apply Nat.le_antisymm
              · exact Nat.le_of_not_gt (fun hi => hlarge ⟨i, hi⟩)
              · exact Nat.one_le_iff_ne_zero.mpr (fun hi => hz ⟨i, hi⟩)
            apply hμ
            funext i
            change (f i) • z = (f i) • (0 : M)
            simpa [hone i] using he i
  constructor
  · intro hα x y hxy
    apply hα
    funext i
    change LocalizedModule.mk x (1 : Submonoid.powers (f i)) =
      LocalizedModule.mk y (1 : Submonoid.powers (f i))
    apply LocalizedModule.mk_eq.mpr
    refine ⟨⟨f i, (Submonoid.mem_powers_iff _ _).2 ⟨1, by simp⟩⟩, ?_⟩
    have hi := congrFun hxy i
    change (f i) • x = (f i) • y at hi
    simpa only [Submonoid.smul_def, one_smul] using hi
  · intro hμ x y hxy
    apply sub_eq_zero.mp
    have hex : ∀ i : Fin n, ∃ e : ℕ, (f i) ^ e • (x - y) = 0 := by
      intro i
      have hi := congrFun hxy i
      simp only [standardCoverModuleAlpha_apply] at hi
      have hi' :
          LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M (x - y) = 0 := by
        rw [map_sub, hi, sub_self]
      rcases LocalizedModule.mem_ker_mkLinearMap_iff.mp
        (LinearMap.mem_ker.mpr hi') with ⟨s, hs, hsz⟩
      obtain ⟨e, he⟩ := (Submonoid.mem_powers_iff _ _).mp hs
      refine ⟨e, ?_⟩
      rw [he]
      exact hsz
    choose e he using hex
    exact hpow hμ (∑ i, e i) e (x - y) rfl he

/-! ## Glueing modules -/

/-- A finite family of modules over the standard-open localizations. -/
structure GlueModuleFamily {R : Type u} [CommRing R] {n : ℕ}
    (f : Fin n → R) where
  carrier : Fin n → Type v
  addCommGroup : ∀ i, AddCommGroup (carrier i)
  module : ∀ i, Module (Localization.Away (f i)) (carrier i)

instance glueModuleFamilyAddCommGroup {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f) (i : Fin n) :
    AddCommGroup (F.carrier i) :=
  F.addCommGroup i

instance glueModuleFamilyLocalizationModule {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f) (i : Fin n) :
    Module (Localization.Away (f i)) (F.carrier i) :=
  F.module i

instance glueModuleFamilyModule {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f) (i : Fin n) :
    Module R (F.carrier i) :=
  Module.compHom (F.carrier i) (algebraMap R (Localization.Away (f i)))

instance glueModuleFamilyScalarTower {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f) (i : Fin n) :
    IsScalarTower R (Localization.Away (f i)) (F.carrier i) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The common localization of the `i`th and `j`th members, applied to the
`k`th module in a gluing datum. -/
abbrev gluePairModule {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f)
    (i j k : Fin n) : Type (max u v) :=
  LocalizedModule (standardCoverJointSubmonoid f i j) (F.carrier k)

/-- Transition isomorphisms, oriented so that `ψ i j` carries the `j`th
module to the `i`th module on the `i,j` intersection. -/
structure GlueModuleTransitionData {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f) where
  ψ : ∀ i j : Fin n,
    gluePairModule F i j j ≃ₗ[Localization (standardCoverJointSubmonoid f i j)]
      gluePairModule F i j i

private def glueTransitionAsRLinear {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f)
    (D : GlueModuleTransitionData F) (i j : Fin n) :
    gluePairModule F i j j →ₗ[R] gluePairModule F i j i :=
  { toFun := D.ψ i j
    map_add' := (D.ψ i j).map_add
    map_smul' := fun r x => (D.ψ i j).map_smul_of_tower r x }

/-- The transition map after passing from a pairwise localization to any
larger common localization. -/
noncomputable def glueTransitionAt {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f)
    (D : GlueModuleTransitionData F) (i j : Fin n) (T : Submonoid R)
    (hij : standardCoverJointSubmonoid f i j ≤ T) :
    LocalizedModule T (F.carrier j) →ₗ[R] LocalizedModule T (F.carrier i) :=
  (IsLocalizedModule.map T
    (LocalizedModule.liftOfLE (standardCoverJointSubmonoid f i j) T hij)
    (LocalizedModule.liftOfLE (standardCoverJointSubmonoid f i j) T hij))
    (glueTransitionAsRLinear F D i j)

/-- The cocycle condition for the transition isomorphisms.  Quantifying over
an arbitrary common localization avoids choosing an order for the indices. -/
def glueModuleCocycle {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f)
    (D : GlueModuleTransitionData F) : Prop :=
  ∀ (i j k : Fin n) (T : Submonoid R)
    (hji : standardCoverJointSubmonoid f j i ≤ T)
    (hkj : standardCoverJointSubmonoid f k j ≤ T)
    (hki : standardCoverJointSubmonoid f k i ≤ T),
    (glueTransitionAt F D k j T hkj).comp
        (glueTransitionAt F D j i T hji) =
      glueTransitionAt F D k i T hki

/-- The map whose kernel is the glued module. -/
noncomputable def gluedModuleComparisonMap {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f)
    (D : GlueModuleTransitionData F) :
    (∀ i : Fin n, F.carrier i) →ₗ[R]
      (∀ p : Fin n × Fin n, gluePairModule F p.1 p.2 p.1) :=
  LinearMap.pi fun p : Fin n × Fin n =>
    (LocalizedModule.mkLinearMap (standardCoverJointSubmonoid f p.1 p.2)
        (F.carrier p.1)).comp (LinearMap.proj p.1) -
      ((D.ψ p.1 p.2).toLinearMap.restrictScalars R).comp
        ((LocalizedModule.mkLinearMap (standardCoverJointSubmonoid f p.1 p.2)
          (F.carrier p.2)).comp (LinearMap.proj p.2))

@[simp]
theorem gluedModuleComparisonMap_apply {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f)
    (D : GlueModuleTransitionData F)
    (x : ∀ i : Fin n, F.carrier i) (i j : Fin n) :
    gluedModuleComparisonMap F D x (i, j) =
      LocalizedModule.mkLinearMap (standardCoverJointSubmonoid f i j)
          (F.carrier i) (x i) -
        (D.ψ i j).toLinearMap.restrictScalars R
          (LocalizedModule.mkLinearMap (standardCoverJointSubmonoid f i j)
            (F.carrier j) (x j)) :=
  rfl

/-- The module obtained as the kernel of the gluing comparison map. -/
def gluedModule {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f)
    (D : GlueModuleTransitionData F) :
    Submodule R (∀ i : Fin n, F.carrier i) :=
  LinearMap.ker (gluedModuleComparisonMap F D)

/-- The natural projection from the glued module to one member of the
localizing family. -/
def gluedModuleProjection {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f)
    (D : GlueModuleTransitionData F) (i : Fin n) :
    gluedModule F D →ₗ[R] F.carrier i :=
  (LinearMap.proj i).comp (gluedModule F D).subtype

/-- Modules with compatible transition isomorphisms glue, and the resulting
module localizes back to every member of the family. -/
theorem glue_modules {R : Type u} [CommRing R] {n : ℕ}
    {f : Fin n → R} (F : GlueModuleFamily f)
    (D : GlueModuleTransitionData F) (hD : glueModuleCocycle F D) :
    (∀ i : Fin n, ∃ e : LocalizedModule.Away (f i) (gluedModule F D) ≃ₗ[
        Localization.Away (f i)] F.carrier i,
      (e.toLinearMap.restrictScalars R).comp
          (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (gluedModule F D)) =
        gluedModuleProjection F D i) ∧
      (∀ (i j : Fin n) (m : gluedModule F D),
        D.ψ i j
            (LocalizedModule.mkLinearMap (standardCoverJointSubmonoid f i j)
              (F.carrier j) (gluedModuleProjection F D j m)) =
          LocalizedModule.mkLinearMap (standardCoverJointSubmonoid f i j)
            (F.carrier i) (gluedModuleProjection F D i m)) := by
  constructor
  · intro i
    let g := gluedModuleProjection F D i
    have hg : IsLocalizedModule (Submonoid.powers (f i)) g := by
      constructor
      · intro s
        rw [← (Algebra.lsmul R (A := Localization.Away (f i)) R (F.carrier i)).commutes]
        exact (IsLocalization.map_units (Localization.Away (f i)) s).map _
      · intro y
        have hunit (j : Fin n) (s : Submonoid.powers (f j)) :
            IsUnit (algebraMap R (Module.End R (F.carrier j)) s) := by
          rw [← (Algebra.lsmul R (A := Localization.Away (f j)) R
            (F.carrier j)).commutes]
          exact (IsLocalization.map_units (Localization.Away (f j)) s).map _
        have hrepr (j : Fin n) :
            ∃ m : F.carrier j, ∃ s : standardCoverJointSubmonoid f j i,
              LocalizedModule.mk m s =
                D.ψ j i (LocalizedModule.mk y 1) := by
          let z := D.ψ j i (LocalizedModule.mk y 1)
          induction z using LocalizedModule.induction_on with
          | _ m s => exact ⟨m, s, rfl⟩
        choose num den hnum using hrepr
        choose denLeft denRight hden using fun j =>
          (Formalization.Books.Algebra.Unit09.localizationProduct_mem_iff
            (Submonoid.powers (f j)) (Submonoid.powers (f i)) (den j : R)).mp
            (den j).property
        choose a ha using fun j =>
          (Submonoid.mem_powers_iff _ _).mp (denLeft j).property
        choose b hb using fun j =>
          (Submonoid.mem_powers_iff _ _).mp (denRight j).property
        sorry
      · intro x y hxy
        let z : gluedModule F D := x - y
        have hz_i : gluedModuleProjection F D i z = 0 := by
          change x.1 i - y.1 i = 0
          exact sub_eq_zero.mpr hxy
        have hkill : ∀ j : Fin n, ∃ b : ℕ,
            (f i) ^ b • gluedModuleProjection F D j z = 0 := by
          intro j
          have hp := congrFun (LinearMap.mem_ker.mp z.property) (j, i)
          rw [gluedModuleComparisonMap_apply] at hp
          change LocalizedModule.mkLinearMap (standardCoverJointSubmonoid f j i)
              (F.carrier j) (gluedModuleProjection F D j z) -
            (D.ψ j i).toLinearMap.restrictScalars R
              (LocalizedModule.mkLinearMap (standardCoverJointSubmonoid f j i)
                (F.carrier i) (gluedModuleProjection F D i z)) = 0 at hp
          have hzi' : LocalizedModule.mkLinearMap (standardCoverJointSubmonoid f j i)
              (F.carrier i) (gluedModuleProjection F D i z) = 0 := by
            rw [hz_i, map_zero]
          rw [hzi'] at hp
          simp only [map_zero, sub_zero] at hp
          have hp0 : LocalizedModule.mkLinearMap
              (standardCoverJointSubmonoid f j i) (F.carrier j)
              (gluedModuleProjection F D j z) = 0 := by
            exact hp
          rcases LocalizedModule.mem_ker_mkLinearMap_iff.mp
              (LinearMap.mem_ker.mpr hp0) with ⟨s, hs, hsz⟩
          obtain ⟨sj, si, hsi⟩ :=
            (Formalization.Books.Algebra.Unit09.localizationProduct_mem_iff
              (Submonoid.powers (f j)) (Submonoid.powers (f i)) (s : R)).mp hs
          obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).mp sj.property
          obtain ⟨b, hb⟩ := (Submonoid.mem_powers_iff _ _).mp si.property
          letI : IsLocalizedModule (Submonoid.powers (f j))
              (LinearMap.id : F.carrier j →ₗ[R] F.carrier j) :=
            isLocalizedModule_id (Submonoid.powers (f j)) (F.carrier j)
              (Localization.Away (f j))
          refine ⟨b, ?_⟩
          apply (IsLocalizedModule.smul_injective
            (f := (LinearMap.id : F.carrier j →ₗ[R] F.carrier j)) sj)
          rw [← hsi] at hsz
          simpa [ha, hb, Submonoid.smul_def, mul_smul] using hsz
        choose b hb using hkill
        let N : ℕ := ∑ j, b j
        let c : Submonoid.powers (f i) :=
          ⟨(f i) ^ N, (Submonoid.mem_powers_iff _ _).2 ⟨N, rfl⟩⟩
        refine ⟨c, ?_⟩
        apply Subtype.ext
        funext j
        change (f i) ^ N • x.1 j = (f i) ^ N • y.1 j
        rw [← sub_eq_zero]
        rw [← smul_sub]
        dsimp [N]
        rw [← Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)), pow_add, mul_smul]
        change (f i) ^ (∑ x, b x - b j) •
          ((f i) ^ b j • gluedModuleProjection F D j z) = 0
        rw [hb j, smul_zero]
    let e :=
      (IsLocalizedModule.iso (Submonoid.powers (f i)) g).extendScalarsOfIsLocalization
        (Submonoid.powers (f i)) (Localization.Away (f i))
    exact ⟨e, by
      ext x
      simp [e, g]
      ⟩
  · intro i j m
    have hm := congrFun (LinearMap.mem_ker.mp m.property) (i, j)
    exact (sub_eq_zero.mp hm).symm

end

end Formalization.Books.Algebra.Unit24
