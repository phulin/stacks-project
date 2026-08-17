import Formalization.Books.Topology.Unit09.NoetherianSpaces
import Formalization.Books.Topology.Unit11.CodimensionAndCatenary
import Mathlib.Topology.Inseparable
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sober

/-!
# Topology, Chapter 20: Dimension functions

The source's specialization relation is Mathlib's `Specializes`.  The
dimension-function predicate below is new source-specific infrastructure;
immediate specializations are represented by the corresponding cover
relation in the specialization preorder.  Relative codimension uses the
canonical `relativeCodimension` from Chapter 11.
-/

namespace Formalization.Books.Topology.Unit20

open Set Function _root_.Topology TopologicalSpace
open Formalization.Books.Topology.Unit08
open Formalization.Books.Topology.Unit09
open Formalization.Books.Topology.Unit11

universe u

section DimensionFunctions

variable {X : Type u} [TopologicalSpace X]

/-! ## Definitions -/

/-
The source warns that this terminology is nonstandard and is usually used
for (locally) Noetherian schemes, where strict decrease along every
nontrivial specialization follows from the immediate-specialization
condition.  We retain both conditions because the source defines the notion
for arbitrary topological spaces.
-/

/-- `y` is an immediate specialization of `x`. -/
def IsImmediateSpecialization (x y : X) : Prop :=
  x ≠ y ∧ x ⤳ y ∧
    ¬ ∃ z : X, z ≠ x ∧ z ≠ y ∧ x ⤳ z ∧ z ⤳ y

/--
A dimension function decreases strictly along nontrivial specializations and
decreases by exactly one along immediate specializations.
-/
def IsDimensionFunction (δ : X → ℤ) : Prop :=
  (∀ ⦃x y : X⦄, x ⤳ y → x ≠ y → δ x > δ y) ∧
    (∀ ⦃x y : X⦄, IsImmediateSpecialization x y → δ x = δ y + 1)

/-!
The following bridge exposes the ambient-subspace order needed to express
the source's `codim(closure {y}, closure {x})` using Chapter 11's canonical
relative codimension.
-/

theorem closureSingletonIrreducibleClosed_le_of_specializes
    {x y : X} (hxy : x ⤳ y) :
    closureSingletonIrreducibleClosed y ≤
      closureSingletonIrreducibleClosed x := by
  change closure ({y} : Set X) ⊆ closure ({x} : Set X)
  exact hxy.closure_subset

/-! ## Basic consequences -/

/-- Adding an integer constant to a dimension function gives another one. -/
theorem isDimensionFunction_add_const
    (δ : X → ℤ) (hδ : IsDimensionFunction δ) (t : ℤ) :
    IsDimensionFunction (fun x => δ x + t) := by
  simpa [IsDimensionFunction, gt_iff_lt, add_assoc, add_comm, add_left_comm,
    add_lt_add_iff_right] using hδ

/-! ## Catenarity and codimension -/

/-
The source cautions that dimension functions are most natural on sober
spaces.  Sobriety is represented by the established `[QuasiSober X]`
`[T0Space X]` assumptions on the results below; no parallel soberification
construction is introduced here.
-/

/--
A sober space carrying a dimension function is catenary, and the difference
of the function along a specialization is its relative codimension.

The codimension is `ℕ∞`, while the dimension difference is an integer.  The
well-typed form below records the source identity through `Int.toNat`; the
dimension-function hypotheses imply that this difference is nonnegative.
-/
theorem isCatenary_of_isDimensionFunction
    [QuasiSober X] [T0Space X]
    (δ : X → ℤ) (hδ : IsDimensionFunction δ) :
    IsCatenary X ∧
      ∀ ⦃x y : X⦄ (hxy : x ⤳ y),
        0 ≤ δ x - δ y ∧
            relativeCodimension
              (closureSingletonIrreducibleClosed_le_of_specializes hxy) =
            (δ x - δ y).toNat := by
  have hbetween :
      ∀ {p q : X}, p ⤳ q →
        ∀ {k : ℤ}, δ q ≤ k → k ≤ δ p →
          ∃ z : X, p ⤳ z ∧ z ⤳ q ∧ δ z = k := by
    have aux :
        ∀ n : ℕ, ∀ {p q : X}, p ⤳ q →
          δ p - δ q = (n : ℤ) →
          ∀ {k : ℤ}, δ q ≤ k → k ≤ δ p →
            ∃ z : X, p ⤳ z ∧ z ⤳ q ∧ δ z = k := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
          intro p q hpq hdiff k hqk hkp
          by_cases hkp_eq : k = δ p
          · exact ⟨p, specializes_rfl, hpq, hkp_eq.symm⟩
          by_cases hqk_eq : k = δ q
          · exact ⟨q, hpq, specializes_rfl, hqk_eq.symm⟩
          have hpqne : p ≠ q := by
            intro hpqeq
            subst q
            exact hkp_eq (le_antisymm hkp hqk)
          by_cases hmid : ∃ z : X, z ≠ p ∧ z ≠ q ∧ p ⤳ z ∧ z ⤳ q
          · obtain ⟨z, hzp, hzq, hpz, hzq'⟩ := hmid
            have hpzδ : δ z < δ p := hδ.1 hpz hzp.symm
            have hzqδ : δ q < δ z := hδ.1 hzq' hzq
            have hpz_nonneg : 0 ≤ δ p - δ z := by omega
            have hzq_nonneg : 0 ≤ δ z - δ q := by omega
            have hpz_diff : δ p - δ z = ((δ p - δ z).toNat : ℤ) := by
              symm
              exact Int.toNat_of_nonneg hpz_nonneg
            have hzq_diff : δ z - δ q = ((δ z - δ q).toNat : ℤ) := by
              symm
              exact Int.toNat_of_nonneg hzq_nonneg
            have hpz_lt : (δ p - δ z).toNat < n := by
              apply (Int.toNat_lt_of_ne_zero (by omega)).2
              omega
            have hzq_lt : (δ z - δ q).toNat < n := by
              apply (Int.toNat_lt_of_ne_zero (by omega)).2
              omega
            by_cases hkz : δ z ≤ k
            · obtain ⟨w, hpw, hwz, hkw⟩ :=
                ih _ hpz_lt (p := p) (q := z) hpz hpz_diff
                  (k := k) hkz hkp
              exact ⟨w, hpw, hwz.trans hzq', hkw⟩
            · obtain ⟨w, hzw, hwq, hkw⟩ :=
                ih _ hzq_lt (p := z) (q := q) hzq' hzq_diff
                  (k := k) hqk (le_of_not_ge hkz)
              exact ⟨w, hpz.trans hzw, hwq, hkw⟩
          · have himm : IsImmediateSpecialization p q := ⟨hpqne, hpq, hmid⟩
            have hδpq := hδ.2 himm
            omega
    intro p q hpq k hqk hkp
    have hnonneg : 0 ≤ δ p - δ q := by
      by_cases hpqeq : p = q
      · subst q
        simp
      · omega
    apply aux (δ p - δ q).toNat hpq
    · symm
      exact Int.toNat_of_nonneg hnonneg
    · exact hqk
    · exact hkp
  have hcoheight_int_Iic :
      ∀ (m n : ℤ) (hnm : n ≤ m),
        Order.coheight (⟨n, hnm⟩ : Set.Iic m) = (m - n).toNat := by
    intro m n hnm
    apply le_antisymm
    · rw [Order.coheight_le_iff']
      intro p hp
      let q := p.map (fun z : Set.Iic m => (z : ℤ))
        (fun _ _ h => h)
      have hqhead : q.head = n := by
        change (p.head : ℤ) = n
        exact congrArg (fun z : Set.Iic m => (z : ℤ)) hp
      have hqbound : (q.length : ℤ) ≤ m - n := by
        have hindex :
            ∀ {l : ℕ} (v : Fin (l + 1) → ℤ),
              StrictMono v →
                ∀ i : Fin (l + 1), v 0 + (i : ℤ) ≤ v i := by
          intro l v hv i
          induction i using Fin.induction with
          | zero => simp
          | succ i ih =>
              have hlt : v i.castSucc < v i.succ := hv Fin.castSucc_lt_succ
              have hcast : (i.succ : ℤ) = (i.castSucc : ℤ) + 1 := by
                change ((i.val + 1 : ℕ) : ℤ) = (i.val : ℤ) + 1
                omega
              omega
        have hi := hindex q.toFun q.strictMono (Fin.last q.length)
        have hlast : (q.last : ℤ) ≤ m := by
          change (p.last : ℤ) ≤ m
          exact p.last.property
        change q.head + (q.length : ℤ) ≤ q.last at hi
        rw [hqhead] at hi
        omega
      have hnonneg : 0 ≤ m - n := sub_nonneg.mpr hnm
      have hcast : ((m - n).toNat : ℤ) = m - n :=
        Int.toNat_of_nonneg hnonneg
      have hpbound : (p.length : ℤ) ≤ ((m - n).toNat : ℤ) := by
        change (p.length : ℤ) ≤ m - n at hqbound
        simpa [hcast] using hqbound
      exact_mod_cast hpbound
    · have hnonneg : 0 ≤ m - n := sub_nonneg.mpr hnm
      let l := (m - n).toNat
      have hl_int : (l : ℤ) = m - n := by
        dsimp [l]
        exact Int.toNat_of_nonneg hnonneg
      have hle (i : Fin (l + 1)) : n + (i : ℤ) ≤ m := by
        have hi : (i : ℕ) ≤ l := i.is_le
        omega
      let q : LTSeries (Set.Iic m) :=
        LTSeries.mk l (fun i => ⟨n + (i : ℤ), hle i⟩) (by
          intro i j hij
          have hij' : (i : ℤ) < (j : ℤ) := by
            exact_mod_cast hij
          change n + (i : ℤ) < n + (j : ℤ)
          omega)
      have hqhead : q.head = ⟨n, hnm⟩ := by
        apply Subtype.ext
        change n + (0 : ℤ) = n
        simp
      rw [Order.coheight_eq_iSup_head_eq]
      apply le_iSup₂_of_le q hqhead
      rw [show q.length = l by rfl]
  let g : IrreducibleCloseds X → X :=
    fun Z => Z.2.genericPoint
  have hg (Z : IrreducibleCloseds X) :
      IsGenericPoint (g Z) (Z : Set X) := by
    dsimp [g]
    exact Z.2.isGenericPoint_genericPoint Z.3
  have hg_closure (z : X) :
      g (closureSingletonIrreducibleClosed z) = z := by
    apply (hg _).eq
    exact closureSingleton_isGenericPoint z
  have hspec_of_le {A B : IrreducibleCloseds X} (hAB : A ≤ B) :
      g B ⤳ g A := by
    apply (hg B).specializes
    exact hAB (hg A).mem
  have hne_of_lt {A B : IrreducibleCloseds X} (hAB : A < B) :
      g B ≠ g A := by
    intro heq
    apply hAB.ne
    apply IrreducibleCloseds.ext
    rw [← (hg A).def, ← (hg B).def, heq]
  have hδ_lt_of_lt {A B : IrreducibleCloseds X} (hAB : A < B) :
      δ (g A) < δ (g B) := by
    exact hδ.1 (hspec_of_le hAB.le) (hne_of_lt hAB)
  have hδ_le_of_le {A B : IrreducibleCloseds X} (hAB : A ≤ B) :
      δ (g A) ≤ δ (g B) := by
    by_cases hEq : A = B
    · subst B
      rfl
    · exact (hδ_lt_of_lt (lt_of_le_of_ne hAB hEq)).le
  have hrelative {A B : IrreducibleCloseds X} (hAB : A ≤ B) :
      relativeCodimension hAB =
        (δ (g B) - δ (g A)).toNat := by
    let f : Set.Iic B → Set.Iic (δ (g B)) :=
      fun C => ⟨δ (g C), hδ_le_of_le C.property⟩
    have hf : StrictMono f := by
      intro C D hCD
      exact hδ_lt_of_lt hCD
    have hsurj :
        ∀ C : Set.Iic B, ∀ b : Set.Iic (δ (g B)), f C < b →
          ∃ C' : Set.Iic B, C < C' ∧ f C' = b := by
      intro C b hCb
      have hCb' : f C < b := hCb
      change δ (g C) < (b : ℤ) at hCb
      have hklo : δ (g C) ≤ (b : ℤ) := hCb.le
      have hkhi : (b : ℤ) ≤ δ (g B) := b.property
      obtain ⟨z, hBz, hzgC, hδz⟩ :=
        hbetween (hspec_of_le C.property) hklo hkhi
      let D := closureSingletonIrreducibleClosed z
      have hDB : D ≤ B := by
        change closure ({z} : Set X) ⊆ (B : Set X)
        rw [← (hg B).def]
        exact hBz.closure_subset
      have hCD : (C : IrreducibleCloseds X) ≤ D := by
        change (C : Set X) ⊆ closure ({z} : Set X)
        rw [← (hg C).def]
        exact hzgC.closure_subset
      have hfd : f ⟨D, hDB⟩ = b := by
        apply Subtype.ext
        change δ (g D) = (b : ℤ)
        rw [hg_closure, hδz]
      have hneCD : C ≠ (⟨D, hDB⟩ : Set.Iic B) := by
        intro heq
        apply (ne_of_lt hCb')
        rw [heq, hfd]
      exact ⟨⟨D, hDB⟩, lt_of_le_of_ne hCD hneCD, hfd⟩
    have hcoh := Order.coheight_eq_of_strictMono f hf hsurj
      (⟨A, hAB⟩ : Set.Iic B)
    unfold relativeCodimension
    rw [hcoh]
    simpa [f] using hcoheight_int_Iic (δ (g B)) (δ (g A))
      (hδ_le_of_le hAB)
  have hcat : IsCatenary X := by
    apply (isCatenary_iff_finite_and_additive_relativeCodimension).2
    constructor
    · intro A B hAB
      rw [hrelative hAB.le]
      simp
    · intro A B C hAB hBC
      rw [hrelative (le_of_lt (lt_trans hAB hBC)),
        hrelative hAB.le, hrelative hBC.le]
      have h1 : 0 ≤ δ (g B) - δ (g A) :=
        sub_nonneg.mpr (hδ_le_of_le hAB.le)
      have h2 : 0 ≤ δ (g C) - δ (g B) :=
        sub_nonneg.mpr (hδ_le_of_le hBC.le)
      have h3 : 0 ≤ δ (g C) - δ (g A) :=
        sub_nonneg.mpr (hδ_le_of_le (le_of_lt (lt_trans hAB hBC)))
      have hnat :
          (δ (g C) - δ (g A)).toNat =
            (δ (g B) - δ (g A)).toNat +
              (δ (g C) - δ (g B)).toNat := by
        have hz1 := Int.toNat_of_nonneg h1
        have hz2 := Int.toNat_of_nonneg h2
        have hz3 := Int.toNat_of_nonneg h3
        have hz :
            (((δ (g C) - δ (g A)).toNat : ℤ)) =
              (((δ (g B) - δ (g A)).toNat : ℤ)) +
                (((δ (g C) - δ (g B)).toNat : ℤ)) := by
          rw [hz3, hz1, hz2]
          ring
        exact_mod_cast hz
      simpa using congrArg (fun n : ℕ => (n : ℕ∞)) hnat
  refine ⟨hcat, ?_⟩
  intro x y hxy
  have hnonneg : 0 ≤ δ x - δ y := by
    by_cases hxy_eq : x = y
    · subst y
      simp
    · exact sub_nonneg.mpr (hδ.1 hxy hxy_eq).le
  have hrel := hrelative
    (closureSingletonIrreducibleClosed_le_of_specializes hxy)
  refine ⟨hnonneg, ?_⟩
  simpa [hg_closure] using hrel

/-! ## Uniqueness -/

/-- Two dimension functions differ by a locally constant integer-valued map. -/
theorem isLocallyConstant_sub_of_isDimensionFunction
    [LocallyNoetherianSpace X] [QuasiSober X] [T0Space X]
    (δ δ' : X → ℤ)
    (hδ : IsDimensionFunction δ) (hδ' : IsDimensionFunction δ') :
    IsLocallyConstant (fun x => δ x - δ' x) := by
  refine (IsLocallyConstant.iff_exists_open _).2 ?_
  intro x
  obtain ⟨U, hUx, hUN⟩ := exists_mem_nhds_noetherian x
  rcases mem_nhds_iff.mp hUx with ⟨V, hVU, hVopen, hxV⟩
  let _ : NoetherianSpace U := hUN
  let _ : NoetherianSpace V := NoetherianSpace.of_subset hVU
  let _ : QuasiSober V :=
    Topology.IsOpenEmbedding.quasiSober hVopen.isOpenEmbedding_subtypeVal
  let xV : V := ⟨x, hxV⟩
  have hrestrict (ε : X → ℤ) (hε : IsDimensionFunction ε) :
      IsDimensionFunction (fun y : V => ε y) := by
    have hspec_subtype {a b : V} (hab : a ⤳ b) :
        (a : X) ⤳ (b : X) := by
      apply hVopen.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mpr
      exact hab
    constructor
    · intro a b hab hne
      change ε (a : X) > ε (b : X)
      apply hε.1 (hspec_subtype hab)
      intro heq
      apply hne
      exact Subtype.ext heq
    · intro a b hab
      rcases hab with ⟨hne, hab, hmid⟩
      have hab' := hspec_subtype hab
      have hne' : (a : X) ≠ (b : X) := by
        intro heq
        apply hne
        exact Subtype.ext heq
      have hmid' : ¬ ∃ z : X, z ≠ (a : X) ∧ z ≠ (b : X) ∧
          (a : X) ⤳ z ∧ z ⤳ (b : X) := by
        rintro ⟨z, hza, hzb, haz, hzb'⟩
        have hzV : z ∈ V := hzb'.mem_open hVopen b.property
        let zV : V := ⟨z, hzV⟩
        apply hmid
        refine ⟨zV, ?_, ?_, ?_, ?_⟩
        · intro h
          apply hza
          exact congrArg Subtype.val h
        · intro h
          apply hzb
          exact congrArg Subtype.val h
        · apply hVopen.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mp
          exact haz
        · apply hVopen.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mp
          exact hzb'
      simpa using hε.2 ⟨hne', hab', hmid'⟩
  let δV : V → ℤ := fun y => δ y
  let δV' : V → ℤ := fun y => δ' y
  have hδV : IsDimensionFunction δV := by
    simpa [δV] using hrestrict δ hδ
  have hδV' : IsDimensionFunction δV' := by
    simpa [δV'] using hrestrict δ' hδ'
  have hformula : IsCatenary V ∧
      ∀ ⦃a b : V⦄ (hab : a ⤳ b),
        0 ≤ δV a - δV b ∧
          relativeCodimension
              (closureSingletonIrreducibleClosed_le_of_specializes hab) =
            (δV a - δV b).toNat :=
    isCatenary_of_isDimensionFunction δV hδV
  have hformula' : IsCatenary V ∧
      ∀ ⦃a b : V⦄ (hab : a ⤳ b),
        0 ≤ δV' a - δV' b ∧
          relativeCodimension
              (closureSingletonIrreducibleClosed_le_of_specializes hab) =
            (δV' a - δV' b).toNat :=
    isCatenary_of_isDimensionFunction δV' hδV'
  let I : Set (Set V) :=
    {Z | Z ∈ irreducibleComponents V ∧ xV ∈ Z}
  let J : Set (Set V) :=
    Set.diff (irreducibleComponents V) {Z | xV ∈ Z}
  let C0 : Set V := ⋃₀ I
  have hcomponents : (irreducibleComponents V).Finite :=
    noetherianSpace_finite_irreducibleComponents
  have hxC0 : xV ∈ C0 := by
    apply Set.mem_sUnion.mpr
    refine ⟨irreducibleComponent xV, ?_, mem_irreducibleComponent⟩
    exact ⟨irreducibleComponent_mem_irreducibleComponents xV, mem_irreducibleComponent⟩
  have hJclosed : IsClosed (⋃₀ J) := by
    change IsClosed (⋃₀ (Set.diff (irreducibleComponents V) {Z | xV ∈ Z}))
    rw [Set.sUnion_eq_biUnion]
    apply hcomponents.sdiff.isClosed_biUnion
    intro Z hZ
    exact isClosed_of_mem_irreducibleComponents Z hZ.1
  let O0 : Set V := (⋃₀ J)ᶜ
  have hO0open : IsOpen O0 := by
    dsimp [O0]
    exact hJclosed.isOpen_compl
  have hxO0 : xV ∈ O0 := by
    dsimp [O0]
    intro hxJ
    rcases Set.mem_sUnion.mp hxJ with ⟨Z, hZ, hxZ⟩
    exact hZ.2 hxZ
  have hO0sub : O0 ⊆ C0 := by
    intro z hz
    have hzcover : z ∈ ⋃₀ (irreducibleComponents V) := by
      rw [sUnion_irreducibleComponents]
      trivial
    rcases Set.mem_sUnion.mp hzcover with ⟨Z, hZ, hzZ⟩
    by_cases hxZ : xV ∈ Z
    · exact Set.mem_sUnion.mpr ⟨Z, ⟨hZ, hxZ⟩, hzZ⟩
    · exfalso
      exact hz (Set.mem_sUnion.mpr ⟨Z, ⟨hZ, hxZ⟩, hzZ⟩)
  have hconst_C0 :
      ∀ y : V, y ∈ C0 → δV y - δV' y = δV xV - δV' xV := by
    intro y hy
    rcases Set.mem_sUnion.mp hy with ⟨Z, hZI, hyZ⟩
    change Z ∈ irreducibleComponents V ∧ xV ∈ Z at hZI
    have hZx : xV ∈ Z := hZI.2
    have hZ : Z ∈ irreducibleComponents V := hZI.1
    let ξ : V := hZ.1.genericPoint
    have hξ : IsGenericPoint ξ Z := by
      dsimp [ξ]
      exact hZ.1.isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents Z hZ)
    have hconst_on_Z :
        ∀ z : V, z ∈ Z → δV z - δV' z = δV ξ - δV' ξ := by
      intro z hz
      have hξz : ξ ⤳ z := hξ.specializes hz
      have hzδ := hformula.2 hξz
      have hzδ' := hformula'.2 hξz
      have hnat :
          (δV ξ - δV z).toNat = (δV' ξ - δV' z).toNat := by
        have hnat_top :
            ((δV ξ - δV z).toNat : ℕ∞) =
              ((δV' ξ - δV' z).toNat : ℕ∞) := by
          calc
            ((δV ξ - δV z).toNat : ℕ∞) =
                relativeCodimension
                  (closureSingletonIrreducibleClosed_le_of_specializes hξz) :=
              (hzδ.2).symm
            _ = ((δV' ξ - δV' z).toNat : ℕ∞) := hzδ'.2
        exact_mod_cast hnat_top
      have hdiff : δV ξ - δV z = δV' ξ - δV' z := by
        have hzcast := congrArg (fun n : ℕ => (n : ℤ)) hnat
        rw [Int.toNat_of_nonneg hzδ.1, Int.toNat_of_nonneg hzδ'.1] at hzcast
        exact hzcast
      omega
    exact (hconst_on_Z y hyZ).trans (hconst_on_Z xV hZx).symm
  have hO0nh : O0 ∈ 𝓝 xV := hO0open.mem_nhds hxO0
  rcases (mem_nhds_subtype V xV O0).mp hO0nh with ⟨W, hW, hWO⟩
  rcases mem_nhds_iff.mp hW with ⟨W', hW'W, hW'open, hxW'⟩
  refine ⟨W' ∩ V, hW'open.inter hVopen, ⟨hxW', hxV⟩, ?_⟩
  intro y hy
  let yV : V := ⟨y, hy.2⟩
  have hyO0 : yV ∈ O0 := by
    apply hWO
    exact hW'W hy.1
  simpa [δV, δV', xV, yV] using hconst_C0 yV (hO0sub hyO0)

/-! ## Local existence -/

/--
In a locally Noetherian, sober, catenary space every point has an open
neighbourhood carrying a dimension function.
-/
theorem exists_open_isDimensionFunction_nhds
    [LocallyNoetherianSpace X] [QuasiSober X] [T0Space X]
    (hX : IsCatenary X) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ δ : U → ℤ, IsDimensionFunction δ := by
  classical
  obtain ⟨N, hNx, hNN⟩ := exists_mem_nhds_noetherian x
  rcases mem_nhds_iff.mp hNx with ⟨V, hVN, hVopen, hxV⟩
  let _ : NoetherianSpace N := hNN
  let _ : NoetherianSpace V := NoetherianSpace.of_subset hVN
  let _ : QuasiSober V :=
    Topology.IsOpenEmbedding.quasiSober hVopen.isOpenEmbedding_subtypeVal
  let xV : V := ⟨x, hxV⟩
  have hVcat : IsCatenary V :=
    isCatenary_subtype_of_isLocallyClosed hX hVopen.isLocallyClosed
  have hcodim_self (A : IrreducibleCloseds V) :
      relativeCodimension (le_rfl : A ≤ A) = 0 := by
    have htop : (⟨A, Set.mem_Iic.mpr (le_refl A)⟩ : Set.Iic A) = ⊤ := by
      apply Subtype.ext
      rfl
    calc
      relativeCodimension (le_rfl : A ≤ A) =
          Order.coheight (⟨A, Set.mem_Iic.mpr (le_refl A)⟩ : Set.Iic A) := rfl
      _ = Order.coheight (⊤ : Set.Iic A) := by rw [htop]
      _ = 0 := Order.coheight_top (Set.Iic A)
  have hcodim_ne_top {A B : IrreducibleCloseds V} (hAB : A ≤ B) :
      relativeCodimension hAB ≠ ⊤ := by
    by_cases hEq : A = B
    · subst B
      simp [hcodim_self]
    · exact ne_top_of_lt
        ((isCatenary_iff_finite_and_additive_relativeCodimension.mp hVcat).1
          (lt_of_le_of_ne hAB hEq))
  have hcodim_add {A B C : IrreducibleCloseds V}
      (hAB : A ≤ B) (hBC : B ≤ C) :
      relativeCodimension (hAB.trans hBC) =
        relativeCodimension hAB + relativeCodimension hBC := by
    by_cases hEqAB : A = B
    · subst B
      simp [hcodim_self]
    by_cases hEqBC : B = C
    · subst C
      simp [hcodim_self]
    exact (isCatenary_iff_finite_and_additive_relativeCodimension.mp hVcat).2
      (lt_of_le_of_ne hAB hEqAB) (lt_of_le_of_ne hBC hEqBC)
  have hcodim_add_nat {A B C : IrreducibleCloseds V}
      (hAB : A ≤ B) (hBC : B ≤ C) :
      (relativeCodimension (hAB.trans hBC)).toNat =
        (relativeCodimension hAB).toNat +
          (relativeCodimension hBC).toNat := by
    have h := congrArg ENat.toNat (hcodim_add hAB hBC)
    rw [ENat.toNat_add (hcodim_ne_top hAB) (hcodim_ne_top hBC)] at h
    exact h
  have hcomponents : (irreducibleComponents V).Finite :=
    noetherianSpace_finite_irreducibleComponents
  let P : Set (Set V) :=
    Set.image2 (fun Z Z' : Set V => Z ∩ Z')
      (irreducibleComponents V) (irreducibleComponents V)
  have hPfin : P.Finite := by
    dsimp [P]
    apply Set.Finite.image2 <;> exact hcomponents
  have hPclosed : ∀ T ∈ P, IsClosed T := by
    intro T hT
    rcases hT with ⟨Z, hZ, Z', hZ', rfl⟩
    exact (isClosed_of_mem_irreducibleComponents Z hZ).inter
      (isClosed_of_mem_irreducibleComponents Z' hZ')
  let Kfun : P → Set (Set V) := fun T =>
    Classical.choose
      (NoetherianSpace.exists_finite_set_isClosed_irreducible
        (hPclosed T T.property))
  have hKfun_spec (T : P) :
      (Kfun T).Finite ∧
        (∀ A ∈ Kfun T, IsClosed A) ∧
        (∀ A ∈ Kfun T, IsIrreducible A) ∧
        (T : Set V) = ⋃₀ Kfun T := by
    dsimp [Kfun]
    exact Classical.choose_spec
      (NoetherianSpace.exists_finite_set_isClosed_irreducible
        (hPclosed T T.property))
  let _ : Finite P := hPfin.to_subtype
  let Kall : Set (Set V) := ⋃ T : P, Kfun T
  have hKallfin : Kall.Finite := by
    dsimp [Kall]
    exact Set.finite_iUnion fun T => (hKfun_spec T).1
  let I : Set (Set V) :=
    {Z | Z ∈ irreducibleComponents V ∧ xV ∈ Z}
  let J : Set (Set V) :=
    Set.union (Set.diff (irreducibleComponents V) {Z | xV ∈ Z})
      (Set.diff Kall {T | xV ∈ T})
  have hJfin : J.Finite := by
    dsimp [J]
    exact (hcomponents.sdiff).union (hKallfin.sdiff)
  have hJclosed : IsClosed (⋃₀ J) := by
    rw [Set.sUnion_eq_biUnion]
    apply hJfin.isClosed_biUnion
    intro T hT
    rcases hT with hT | hT
    · exact isClosed_of_mem_irreducibleComponents T hT.1
    · exact (by
        rcases Set.mem_iUnion.mp hT.1 with ⟨K, hK⟩
        exact (by
          rcases hKfun_spec K with ⟨_, hKclosed, _, _⟩
          exact hKclosed T hK))
  let O0 : Set V := (⋃₀ J)ᶜ
  have hO0open : IsOpen O0 := by
    dsimp [O0]
    exact hJclosed.isOpen_compl
  have hxO0 : xV ∈ O0 := by
    dsimp [O0]
    intro hxJ
    rcases Set.mem_sUnion.mp hxJ with ⟨T, hTJ, hxT⟩
    rcases hTJ with hTJ | hTJ
    · exact hTJ.2 hxT
    · exact hTJ.2 hxT
  have hxI : xV ∈ ⋃₀ I := by
    apply Set.mem_sUnion.mpr
    refine ⟨irreducibleComponent xV, ?_, mem_irreducibleComponent⟩
    exact ⟨irreducibleComponent_mem_irreducibleComponents xV,
      mem_irreducibleComponent⟩
  have hO0sub : O0 ⊆ ⋃₀ I := by
    intro z hz
    have hzcover : z ∈ ⋃₀ (irreducibleComponents V) := by
      rw [sUnion_irreducibleComponents]
      trivial
    rcases Set.mem_sUnion.mp hzcover with ⟨Z, hZ, hzZ⟩
    by_cases hxZ : xV ∈ Z
    · exact Set.mem_sUnion.mpr ⟨Z, ⟨hZ, hxZ⟩, hzZ⟩
    · exfalso
      exact hz (Set.mem_sUnion.mpr ⟨Z, Or.inl ⟨hZ, hxZ⟩, hzZ⟩)
  have hO0_component_x {z : V} (hzO0 : z ∈ O0)
      {Z : Set V} (hZ : Z ∈ irreducibleComponents V) (hzZ : z ∈ Z) :
      xV ∈ Z := by
    by_cases hxZ : xV ∈ Z
    · exact hxZ
    have hzI : z ∈ ⋃₀ I := hO0sub hzO0
    rcases Set.mem_sUnion.mp hzI with ⟨Z0, hZ0, hzZ0⟩
    have hPZ : Z ∩ Z0 ∈ P := by
      dsimp [P]
      exact ⟨Z, hZ, Z0, hZ0.1, rfl⟩
    let T : P := ⟨Z ∩ Z0, hPZ⟩
    have hzT : z ∈ (T : Set V) := ⟨hzZ, hzZ0⟩
    have hzK : z ∈ ⋃₀ Kfun T := by
      rw [← (hKfun_spec T).2.2.2]
      exact hzT
    rcases Set.mem_sUnion.mp hzK with ⟨A, hAT, hzA⟩
    have hAall : A ∈ Kall := by
      dsimp [Kall]
      exact Set.mem_iUnion.mpr ⟨T, hAT⟩
    have hAx : xV ∈ A := by
      by_contra hAx
      have hAJ : A ∈ J := Or.inr ⟨hAall, hAx⟩
      have hzJ : z ∈ ⋃₀ J := Set.mem_sUnion.mpr ⟨A, hAJ, hzA⟩
      exact hzO0 hzJ
    have hATsub : A ⊆ (T : Set V) := by
      calc
        A ⊆ ⋃₀ Kfun T := Set.subset_sUnion_of_mem hAT
        _ = (T : Set V) := (hKfun_spec T).2.2.2.symm
    have hAxT : xV ∈ (T : Set V) := hATsub hAx
    change xV ∈ Z ∩ Z0 at hAxT
    exact hAxT.1
  have hcomp_y (y : V) :
      irreducibleComponent y ∈ irreducibleComponents V :=
    irreducibleComponent_mem_irreducibleComponents y
  let Zc (y : V) : IrreducibleCloseds V :=
    ⟨irreducibleComponent y, isIrreducible_irreducibleComponent,
      isClosed_of_mem_irreducibleComponents _ (hcomp_y y)⟩
  have hZc_mem (y : V) : y ∈ (Zc y : Set V) := by
    dsimp [Zc]
    exact mem_irreducibleComponent
  have hZc_component (y : V) :
      (Zc y : Set V) ∈ irreducibleComponents V := by
    dsimp [Zc]
    exact hcomp_y y
  have hclosure_le_of_mem {a : V} {Z : IrreducibleCloseds V}
      (ha : a ∈ (Z : Set V)) :
      closureSingletonIrreducibleClosed a ≤ Z := by
    change closure ({a} : Set V) ⊆ (Z : Set V)
    exact closure_minimal (singleton_subset_iff.mpr ha) Z.isClosed
  have hcomponent_consistency {y : O0}
      (Z₁ Z₂ : IrreducibleCloseds V)
      (hZ₁ : (Z₁ : Set V) ∈ irreducibleComponents V)
      (hZ₂ : (Z₂ : Set V) ∈ irreducibleComponents V)
      (hy₁ : (y : V) ∈ Z₁) (hy₂ : (y : V) ∈ Z₂) :
      ((relativeCodimension
          (hclosure_le_of_mem
            (Z := Z₁)
            (hO0_component_x y.property hZ₁ hy₁))).toNat : ℤ) -
          ((relativeCodimension
            (hclosure_le_of_mem (Z := Z₁) hy₁)).toNat : ℤ) =
        ((relativeCodimension
          (hclosure_le_of_mem
            (Z := Z₂)
            (hO0_component_x y.property hZ₂ hy₂))).toNat : ℤ) -
          ((relativeCodimension
            (hclosure_le_of_mem (Z := Z₂) hy₂)).toNat : ℤ) := by
    have hx₁ : xV ∈ Z₁ := hO0_component_x y.property hZ₁ hy₁
    have hx₂ : xV ∈ Z₂ := hO0_component_x y.property hZ₂ hy₂
    have hPZ : (Z₁ : Set V) ∩ (Z₂ : Set V) ∈ P := by
      dsimp [P]
      exact ⟨(Z₁ : Set V), hZ₁, (Z₂ : Set V), hZ₂, rfl⟩
    let T : P := ⟨(Z₁ : Set V) ∩ (Z₂ : Set V), hPZ⟩
    have hyT : (y : V) ∈ (T : Set V) := ⟨hy₁, hy₂⟩
    have hyK : (y : V) ∈ ⋃₀ Kfun T := by
      rw [← (hKfun_spec T).2.2.2]
      exact hyT
    rcases Set.mem_sUnion.mp hyK with ⟨A, hAT, hyA⟩
    have hAall : A ∈ Kall := by
      dsimp [Kall]
      exact Set.mem_iUnion.mpr ⟨T, hAT⟩
    have hxA : xV ∈ A := by
      by_contra hxA
      have hAJ : A ∈ J := Or.inr ⟨hAall, hxA⟩
      have hyJ : (y : V) ∈ ⋃₀ J := Set.mem_sUnion.mpr ⟨A, hAJ, hyA⟩
      exact y.property hyJ
    have hATsub : A ⊆ (T : Set V) := by
      calc
        A ⊆ ⋃₀ Kfun T := Set.subset_sUnion_of_mem hAT
        _ = (T : Set V) := (hKfun_spec T).2.2.2.symm
    let Kobj : IrreducibleCloseds V :=
      ⟨A, (hKfun_spec T).2.2.1 A hAT,
        (hKfun_spec T).2.1 A hAT⟩
    have hAxK : closureSingletonIrreducibleClosed xV ≤ Kobj := by
      apply hclosure_le_of_mem
      exact hxA
    have hyKobj : closureSingletonIrreducibleClosed (y : V) ≤ Kobj := by
      apply hclosure_le_of_mem
      exact hyA
    have hKZ₁ : Kobj ≤ Z₁ := by
      change A ⊆ (Z₁ : Set V)
      intro a ha
      have haT : a ∈ (T : Set V) := hATsub ha
      change a ∈ (Z₁ : Set V) ∩ (Z₂ : Set V) at haT
      exact haT.1
    have hKZ₂ : Kobj ≤ Z₂ := by
      change A ⊆ (Z₂ : Set V)
      intro a ha
      have haT : a ∈ (T : Set V) := hATsub ha
      change a ∈ (Z₁ : Set V) ∩ (Z₂ : Set V) at haT
      exact haT.2
    have hcx₁ := hcodim_add_nat hAxK hKZ₁
    have hcy₁ := hcodim_add_nat hyKobj hKZ₁
    have hcx₂ := hcodim_add_nat hAxK hKZ₂
    have hcy₂ := hcodim_add_nat hyKobj hKZ₂
    omega
  let d : O0 → ℤ := fun y =>
    ((relativeCodimension
        (hclosure_le_of_mem
          (Z := Zc y)
          (hO0_component_x y.property (hZc_component y) (hZc_mem y)))).toNat : ℤ) -
      ((relativeCodimension
        (hclosure_le_of_mem (Z := Zc y) (hZc_mem y))).toNat : ℤ)
  have hd_component {y : O0} {Z : IrreducibleCloseds V}
      (hZ : (Z : Set V) ∈ irreducibleComponents V)
      (hyZ : (y : V) ∈ Z) :
      d y =
        ((relativeCodimension
          (hclosure_le_of_mem
            (Z := Z)
            (hO0_component_x y.property hZ hyZ))).toNat : ℤ) -
          ((relativeCodimension
            (hclosure_le_of_mem (Z := Z) hyZ)).toNat : ℤ) := by
    dsimp [d]
    exact hcomponent_consistency (y := y) (Zc y) Z
      (hZc_component y) hZ (hZc_mem y) hyZ
  have hcodim_pos {A B : IrreducibleCloseds V}
      (hBA : B < A) :
      1 ≤ relativeCodimension (le_of_lt hBA) := by
    have hlt :
        (⟨B, Set.mem_Iic.mpr hBA.le⟩ : Set.Iic A) <
          (⟨A, Set.mem_Iic.mpr (le_refl A)⟩ : Set.Iic A) := by
      exact hBA
    have h := Order.coheight_add_one_le hlt
    have htop :
        (⟨A, Set.mem_Iic.mpr (le_refl A)⟩ : Set.Iic A) = ⊤ := by
      apply Subtype.ext
      rfl
    rw [htop, Order.coheight_top] at h
    simpa [relativeCodimension] using h
  let gV : IrreducibleCloseds V → V :=
    fun Z => Z.2.genericPoint
  have hgV (Z : IrreducibleCloseds V) :
      IsGenericPoint (gV Z) (Z : Set V) := by
    dsimp [gV]
    exact Z.2.isGenericPoint_genericPoint Z.3
  have hgV_closure (z : V) :
      gV (closureSingletonIrreducibleClosed z) = z := by
    apply (hgV _).eq
    exact closureSingleton_isGenericPoint z
  have hgV_def (Z : IrreducibleCloseds V) :
      closureSingletonIrreducibleClosed (gV Z) = Z := by
    apply IrreducibleCloseds.ext
    rw [← (hgV Z).def]
    rfl
  have hspecV_of_le {A B : IrreducibleCloseds V} (hAB : A ≤ B) :
      gV B ⤳ gV A := by
    apply (hgV B).specializes
    exact hAB (hgV A).mem
  have hclosure_inj :
      Function.Injective (closureSingletonIrreducibleClosed (X := V)) :=
    closureSingleton_injective_iff_t0.mpr (by infer_instance)
  have hdim_strict {a b : O0} (hab : a ⤳ b) (hne : a ≠ b) :
      d a > d b := by
    have habV : (a : V) ⤳ (b : V) :=
      hO0open.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mpr hab
    have hBA :
        closureSingletonIrreducibleClosed (b : V) <
          closureSingletonIrreducibleClosed (a : V) := by
      apply lt_of_le_of_ne
      · exact closureSingletonIrreducibleClosed_le_of_specializes habV
      · intro heq
        apply hne
        apply Subtype.ext
        exact (hclosure_inj heq).symm
    let Z := Zc (a : V)
    have hbZ : (b : V) ∈ Z := by
      exact habV.mem_closed Z.isClosed (hZc_mem (a : V))
    have hA_Z : closureSingletonIrreducibleClosed (a : V) ≤ Z :=
      hclosure_le_of_mem (hZc_mem (a : V))
    have hB_Z : closureSingletonIrreducibleClosed (b : V) ≤ Z :=
      hclosure_le_of_mem hbZ
    have hpos :
        1 ≤ (relativeCodimension (le_of_lt hBA)).toNat := by
      have hpos' := hcodim_pos hBA
      rw [← ENat.natCast_toNat (hcodim_ne_top (le_of_lt hBA))] at hpos'
      exact_mod_cast hpos'
    have hadd := hcodim_add_nat (le_of_lt hBA) hA_Z
    have hda := hd_component (y := a) (Z := Z)
      (by dsimp [Z]; exact hZc_component (a : V))
      (by dsimp [Z]; exact hZc_mem (a : V))
    have hdb := hd_component (y := b) (Z := Z)
      (by dsimp [Z]; exact hZc_component (a : V)) hbZ
    rw [hda, hdb]
    omega
  have hdim_immediate {a b : O0}
      (hab : IsImmediateSpecialization a b) : d a = d b + 1 := by
    have habV : (a : V) ⤳ (b : V) :=
      hO0open.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mpr hab.2.1
    have hBA :
        closureSingletonIrreducibleClosed (b : V) <
          closureSingletonIrreducibleClosed (a : V) := by
      apply lt_of_le_of_ne
      · exact closureSingletonIrreducibleClosed_le_of_specializes habV
      · intro heq
        apply hab.1
        apply Subtype.ext
        exact (hclosure_inj heq).symm
    let A : IrreducibleCloseds V :=
      closureSingletonIrreducibleClosed (a : V)
    let B : IrreducibleCloseds V :=
      closureSingletonIrreducibleClosed (b : V)
    have hBA' : B < A := by
      dsimp [A, B]
      exact hBA
    have hcoh_one :
        Order.coheight
            (⟨B, Set.mem_Iic.mpr hBA'.le⟩ : Set.Iic A) = 1 := by
      apply (Order.coheight_eq_coe_add_one_iff
        (x := (⟨B, Set.mem_Iic.mpr hBA'.le⟩ : Set.Iic A)) (n := 0)).2
      constructor
      · exact (lt_top_iff_ne_top).2
          (hcodim_ne_top (A := B) (B := A) hBA'.le)
      constructor
      · refine ⟨(⟨A, Set.mem_Iic.mpr (le_refl A)⟩ : Set.Iic A), ?_, ?_⟩
        · exact hBA'
        · have htop :
              (⟨A, Set.mem_Iic.mpr (le_refl A)⟩ : Set.Iic A) = ⊤ := by
            apply Subtype.ext
            rfl
          rw [htop, Order.coheight_top]
          exact ENat.natCast_zero.symm
      · intro C hBC
        have hBC' : B < (C : IrreducibleCloseds V) := hBC
        by_cases hCAeq : (C : IrreducibleCloseds V) = A
        · have hCtop : C = (⊤ : Set.Iic A) := by
            apply Subtype.ext
            exact hCAeq
          rw [hCtop, Order.coheight_top]
          rw [ENat.natCast_zero]
        · have hCA : (C : IrreducibleCloseds V) < A :=
            lt_of_le_of_ne C.property hCAeq
          have haC : (a : V) ⤳ gV (C : IrreducibleCloseds V) := by
            have h := hspecV_of_le hCA.le
            simpa [A, hgV_closure] using h
          have hCb : gV (C : IrreducibleCloseds V) ⤳ (b : V) := by
            have h := hspecV_of_le hBC'.le
            simpa [B, hgV_closure] using h
          have hCopen : gV (C : IrreducibleCloseds V) ∈ O0 :=
            hCb.mem_open hO0open b.property
          let z : O0 := ⟨gV (C : IrreducibleCloseds V), hCopen⟩
          have haC' : a ⤳ z := by
            apply hO0open.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mp
            exact haC
          have hCb' : z ⤳ b := by
            apply hO0open.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mp
            exact hCb
          have hza : z ≠ a := by
            intro hza
            have hza' : gV (C : IrreducibleCloseds V) = (a : V) :=
              congrArg Subtype.val hza
            have hEq : (C : IrreducibleCloseds V) = A := by
              calc
                (C : IrreducibleCloseds V) =
                    closureSingletonIrreducibleClosed
                      (gV (C : IrreducibleCloseds V)) :=
                  (hgV_def (C : IrreducibleCloseds V)).symm
                _ = closureSingletonIrreducibleClosed (a : V) := by
                  rw [hza']
                _ = A := rfl
            exact hCAeq hEq
          have hzb : z ≠ b := by
            intro hzb
            have hzb' : gV (C : IrreducibleCloseds V) = (b : V) :=
              congrArg Subtype.val hzb
            have hEq : (C : IrreducibleCloseds V) = B := by
              calc
                (C : IrreducibleCloseds V) =
                    closureSingletonIrreducibleClosed
                      (gV (C : IrreducibleCloseds V)) :=
                  (hgV_def (C : IrreducibleCloseds V)).symm
                _ = closureSingletonIrreducibleClosed (b : V) := by
                  rw [hzb']
                _ = B := rfl
            exact hBC'.ne hEq.symm
          exact (hab.2.2 ⟨z, hza, hzb, haC', hCb'⟩).elim
    have hcodim_one :
        relativeCodimension hBA'.le = 1 := by
      change Order.coheight
          (⟨B, Set.mem_Iic.mpr hBA'.le⟩ : Set.Iic A) = 1
      exact hcoh_one
    let Z := Zc (a : V)
    have hbZ : (b : V) ∈ Z := by
      exact habV.mem_closed Z.isClosed (hZc_mem (a : V))
    have hA_Z : A ≤ Z := by
      dsimp [A, Z]
      exact hclosure_le_of_mem (hZc_mem (a : V))
    have hadd := hcodim_add_nat hBA'.le hA_Z
    have hone : (relativeCodimension hBA'.le).toNat = 1 := by
      rw [hcodim_one, ENat.toNat_one]
    have hda := hd_component (y := a) (Z := Z)
      (by dsimp [Z]; exact hZc_component (a : V))
      (by dsimp [Z]; exact hZc_mem (a : V))
    have hdb := hd_component (y := b) (Z := Z)
      (by dsimp [Z]; exact hZc_component (a : V)) hbZ
    rw [hda, hdb]
    omega
  let hEO : IsOpenEmbedding (fun y : O0 => (y : X)) := by
    simpa [Function.comp_def] using
      hVopen.isOpenEmbedding_subtypeVal.comp
        hO0open.isOpenEmbedding_subtypeVal
  let U : Set X := Set.range (fun y : O0 => (y : X))
  have hUopen : IsOpen U := by
    dsimp [U]
    exact hEO.isOpen_range
  let e : U → O0 := fun u =>
    Classical.choose u.2
  have he_val (u : U) : (e u : X) = u := by
    exact Classical.choose_spec u.2
  have he_inj : Function.Injective e := by
    intro u v huv
    apply Subtype.ext
    exact (he_val u).symm.trans
      ((congrArg (fun z : O0 => (z : X)) huv).trans (he_val v))
  have hU_to_X {u v : U} (huv : u ⤳ v) :
      (u : X) ⤳ (v : X) := by
    exact hUopen.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mpr huv
  have hO0_to_X {p q : O0} (hpq : p ⤳ q) :
      ((p : O0) : X) ⤳ ((q : O0) : X) := by
    apply hVopen.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mpr
    apply hO0open.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mpr
    exact hpq
  have hX_to_U {u v : U} (huv : (u : X) ⤳ (v : X)) : u ⤳ v := by
    exact hUopen.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mp huv
  have hX_to_O0 {p q : O0} (hpq : ((p : O0) : X) ⤳ ((q : O0) : X)) :
      p ⤳ q := by
    apply hO0open.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mp
    apply hVopen.isOpenEmbedding_subtypeVal.isInducing.specializes_iff.mp
    exact hpq
  have heU_mem (u : U) : (e u : X) ∈ U := by
    exact he_val u ▸ u.property
  let δ : U → ℤ := fun u => d (e u)
  have hδ_strict {u v : U} (huv : u ⤳ v) (hne : u ≠ v) :
      δ u > δ v := by
    apply hdim_strict
    · apply hX_to_O0
      have h := hU_to_X huv
      simpa only [he_val] using h
    · intro heq
      exact hne (he_inj heq)
  have hδ_immediate {u v : U}
      (himm : IsImmediateSpecialization u v) : δ u = δ v + 1 := by
    apply hdim_immediate
    constructor
    · intro heq
      exact himm.1 (he_inj heq)
    constructor
    · apply hX_to_O0
      have h := hU_to_X himm.2.1
      simpa only [he_val] using h
    · rintro ⟨z, hzeu, hzev, heuz, hzv⟩
      have hzvX := hO0_to_X hzv
      have hzU : (z : X) ∈ U :=
        hzvX.mem_open hUopen (heU_mem v)
      let w : U := ⟨(z : X), hzU⟩
      have hwu : w ≠ u := by
        intro hwu
        apply hzeu
        apply Subtype.ext
        apply Subtype.ext
        calc
          (z : X) = (w : X) := rfl
          _ = (u : X) := congrArg Subtype.val hwu
          _ = (e u : X) := (he_val u).symm
      have hwv : w ≠ v := by
        intro hwv
        apply hzev
        apply Subtype.ext
        apply Subtype.ext
        calc
          (z : X) = (w : X) := rfl
          _ = (v : X) := congrArg Subtype.val hwv
          _ = (e v : X) := (he_val v).symm
      have huwX : (u : X) ⤳ (w : X) := by
        have h := hO0_to_X heuz
        simpa only [he_val] using h
      have hwvX : (w : X) ⤳ (v : X) := by
        have h := hO0_to_X hzv
        simpa only [he_val] using h
      exact himm.2.2 ⟨w, hwu, hwv, hX_to_U huwX, hX_to_U hwvX⟩
  have hδ : IsDimensionFunction δ := by
    constructor
    · intro u v huv hne
      exact hδ_strict huv hne
    · intro u v huv
      exact hδ_immediate huv
  refine ⟨U, hUopen, ?_, δ, hδ⟩
  exact ⟨⟨xV, hxO0⟩, rfl⟩

/-!
The final source remark identifies the obstruction with a class in
`H^1(X, ℤ)`.  This chapter has no canonical topological/sheaf-cohomology API
or definition of that obstruction, so the remark is retained here as
documentation rather than replaced by an unrelated formal predicate.
-/

end DimensionFunctions

end Formalization.Books.Topology.Unit20
