import Formalization.Books.Algebra.Unit44.SeparableExtensionsContinued
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PerfectClosure
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Commutative Algebra, Chapter 45: Perfect fields

The source's perfect-field predicate is represented by Mathlib's canonical
`PerfectField` class.  Relative perfect closures are represented by
`perfectClosure` inside an algebraic closure, while the positive-characteristic
root levels are represented by the canonical `PerfectClosure` construction.
-/

namespace Formalization.Books.Algebra.Unit45

open Set
open scoped TensorProduct

universe u v w

noncomputable section

open Formalization.Books.Algebra.Unit42
open Formalization.Books.Algebra.Unit43

private theorem algebra_isSeparable_of_isSeparableExtension_of_isAlgebraic
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E]
    (h : IsSeparableExtension F E) : Algebra.IsSeparable F E := by
  apply (Algebra.isSeparable_iff).2
  intro x
  refine ⟨(Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral, ?_⟩
  let L : IntermediateField F E := IntermediateField.adjoin F ({x} : Set E)
  have hL : Algebra.EssFiniteType F L := by
    change Algebra.EssFiniteType F (IntermediateField.adjoin F ({x} : Set E))
    apply IntermediateField.essFiniteType_iff.mpr
    exact IntermediateField.fg_adjoin_of_finite (F := F) (Set.finite_singleton x)
  let _ : Algebra.IsAlgebraic F L := by
    change Algebra.IsAlgebraic F (IntermediateField.adjoin F ({x} : Set E))
    rw [IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic]
    simp only [Set.mem_singleton_iff]
    intro z rfl
    exact Algebra.IsAlgebraic.isAlgebraic (R := F) z
  rcases h L hL with ⟨ι, y, hy, hsep⟩
  have hi : IsEmpty ι := (hy.isEmpty_iff_isAlgebraic).2 inferInstance
  have hrange : range y = ∅ := Set.range_eq_empty y
  rw [hrange, IntermediateField.adjoin_empty] at hsep
  let _ : Algebra.IsSeparable (⊥ : IntermediateField F L) L := hsep
  have hsepFL : Algebra.IsSeparable F L := by
    exact Algebra.IsSeparable.of_equiv_equiv
      (IntermediateField.botEquiv F L).toRingEquiv (RingEquiv.refl L) (by
        ext z
        obtain ⟨a, rfl⟩ := (IntermediateField.botEquiv F L).symm.surjective z
        simp)
  let _ : Algebra.IsSeparable F L := hsepFL
  apply IntermediateField.isSeparable_of_mem_isSeparable F E (L := L)
  change x ∈ IntermediateField.adjoin F ({x} : Set E)
  exact IntermediateField.subset_adjoin F ({x} : Set E) (Set.mem_singleton x)

/-! ## Perfect fields -/

/- The source defines perfection by separability of every field extension.
   `PerfectField` is Mathlib's canonical equivalent formulation, while
   `IsSeparableExtension` is the earlier chapter's arbitrary-extension notion. -/
/-- Mathlib's canonical perfect-field class is equivalent to the source's
    definition by separability of every field extension. -/
theorem perfectField_iff_all_field_extensions_separable
    {k : Type u} [Field k] :
    PerfectField k ↔
      ∀ (K : Type*) [Field K] [Algebra k K],
        IsSeparableExtension k K := by
  constructor
  · intro hk K _ _
    let _ : PerfectField k := hk
    unfold IsSeparableExtension
    intro L hL
    let _ : Algebra.EssFiniteType k L := hL
    obtain ⟨s, hs, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_perfectField k L
    refine ⟨s, (fun z : s => (z : L)), hs, ?_⟩
    have hrange : range (fun z : s => (z : L)) = (s : Set L) := by
      ext z
      simp
    rw [hrange]
    exact hsep
  · sorry

/-- A field is perfect exactly in characteristic zero or in prime
    characteristic with surjective Frobenius on elements. -/
theorem perfectField_iff_charZero_or_prime_root
    {k : Type u} [Field k] :
    PerfectField k ↔
      CharZero k ∨
        ∃ p : ℕ, p.Prime ∧ CharP k p ∧
          ∀ x : k, ∃ y : k, y ^ p = x := by
  constructor
  · intro h
    by_cases hzero : CharZero k
    · exact Or.inl hzero
    · obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
      · exact (hzero ‹CharZero k›).elim
      right
      refine ⟨p, hp.out, hpk, ?_⟩
      let _ : PerfectField k := h
      let _ : Fact p.Prime := hp
      let _ : CharP k p := hpk
      let _ : ExpChar k p := ExpChar.prime hp.out
      intro x
      rcases (surjective_frobenius k p) x with ⟨y, hy⟩
      exact ⟨y, hy⟩
  · rintro (hzero | ⟨p, hp, hpk, hroot⟩)
    · let _ : CharZero k := hzero
      exact inferInstance
    · let _ : Fact p.Prime := ⟨hp⟩
      let _ : CharP k p := hpk
      let _ : ExpChar k p := ExpChar.prime hp
      let : PerfectRing k p :=
        PerfectRing.ofSurjective k p (by
          intro x
          rcases hroot x with ⟨y, hy⟩
          exact ⟨y, by change y ^ p = x; exact hy⟩)
      exact PerfectRing.toPerfectField k p

/-! ## Making a finitely generated extension separable -/

/- Unit 42 already bundles the source's commuting diagram and the finite
   purely inseparable hypotheses.  These predicates expose the two additional
   normalizations stated in this chapter without duplicating that structure. -/
/-- The upper extension in a `PurelyInseparableBaseChange` is separable in the
    source's arbitrary-extension sense. -/
def IsSeparableBaseChange
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (b : PurelyInseparableBaseChange k K) : Prop :=
  letI := b.baseField
  letI := b.topField
  letI := b.baseAlgebra
  letI := b.topAlgebra
  letI := b.topOverK
  letI := b.topOverBase
  letI := b.baseTower
  letI := b.topTower
  IsSeparableExtension b.base b.top

/-- The upper field of a base-change diagram is the compositum of the base
    field and the original extension inside the upper field. -/
def IsCompositumBaseChange
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (b : PurelyInseparableBaseChange k K) : Prop :=
  letI := b.baseField
  letI := b.topField
  letI := b.baseAlgebra
  letI := b.topAlgebra
  letI := b.topOverK
  letI := b.topOverBase
  letI := b.baseTower
  letI := b.topTower
  IntermediateField.adjoin b.base (range (algebraMap K b.top)) = ⊤

/- The notation `(R)_{red}` in the source is the quotient by the nilradical.
   The assertion is recorded as the corresponding canonical algebra
   equivalence, rather than by introducing a second reduced-ring definition. -/
/-- The upper field is the reduced tensor product of the two lower fields. -/
def IsReducedTensorProductBaseChange
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (b : PurelyInseparableBaseChange k K) : Prop :=
  letI := b.baseField
  letI := b.topField
  letI := b.baseAlgebra
  letI := b.topAlgebra
  letI := b.topOverK
  letI := b.topOverBase
  letI := b.baseTower
  letI := b.topTower
  Nonempty
    (((b.base ⊗[k] K) ⧸ (nilradical (b.base ⊗[k] K))) ≃ₐ[k] b.top)

private theorem isSeparablyGenerated_of_algEquiv
    {k : Type u} {A : Type v} {B : Type v} [Field k] [Field A] [Field B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (hA : IsSeparablyGenerated k A) : IsSeparablyGenerated k B := by
  rcases hA with ⟨ι, x, hx, hsep⟩
  refine ⟨ι, e ∘ x, e.isTranscendenceBasis hx, ?_⟩
  have hmap :
      (IntermediateField.adjoin k (range x)).map e.toAlgHom =
        IntermediateField.adjoin k (range (e ∘ x)) := by
    rw [IntermediateField.adjoin_map]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  rw [← hmap]
  let e₀ := IntermediateField.intermediateFieldMap e
    (IntermediateField.adjoin k (range x))
  have hcompat :
      RingHom.comp
          (algebraMap ((IntermediateField.adjoin k (range x)).map e.toAlgHom) B)
          e₀.toRingEquiv.toRingHom =
        RingHom.comp e.toRingEquiv.toRingHom
          (algebraMap (IntermediateField.adjoin k (range x)) A) := by
    ext z
    rfl
  exact Algebra.IsSeparable.of_equiv_equiv e₀.toRingEquiv e.toRingEquiv hcompat

/-- A finitely generated field extension admits the source's finite purely
    inseparable base-change diagram with separable, compositum, and reduced
    tensor-product normalizations. -/
theorem exists_make_separable_base_change
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    ∃ b : PurelyInseparableBaseChange k K,
      IsSeparableBaseChange b ∧
        IsCompositumBaseChange b ∧ IsReducedTensorProductBaseChange b := by
  obtain ⟨b₀⟩ := exists_purely_inseparable_base_change (k := k) (K := K)
  let _ := b₀.baseField
  let _ := b₀.topField
  let _ := b₀.baseAlgebra
  let _ := b₀.topAlgebra
  let _ := b₀.topOverK
  let _ := b₀.topOverBase
  let _ := b₀.baseTower
  let _ := b₀.topTower
  let _ := b₀.baseFinite
  let _ := b₀.basePurelyInseparable
  let _ := b₀.topFinite
  let _ := b₀.topPurelyInseparable
  let C : IntermediateField K b₀.top :=
    IntermediateField.adjoin K (range (algebraMap b₀.base b₀.top))
  have hbase_mem (x : b₀.base) :
      algebraMap b₀.base b₀.top x ∈ C :=
    IntermediateField.subset_adjoin K _ ⟨x, rfl⟩
  let baseToC : b₀.base →+* C :=
    RingHom.codRestrict (algebraMap b₀.base b₀.top) C hbase_mem
  have hk_mem (x : k) : algebraMap k b₀.top x ∈ C := by
    rw [IsScalarTower.algebraMap_apply k b₀.base b₀.top x]
    exact hbase_mem _
  let kToC : k →+* C :=
    RingHom.codRestrict (algebraMap k b₀.top) C hk_mem
  let : Algebra b₀.base C := RingHom.toAlgebra baseToC
  let : Algebra k C := RingHom.toAlgebra kToC
  let : IsScalarTower k b₀.base C := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    exact IsScalarTower.algebraMap_apply k b₀.base b₀.top x
  let : IsScalarTower k K C := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    exact IsScalarTower.algebraMap_apply k K b₀.top x
  let Cbase : IntermediateField b₀.base b₀.top :=
    IntermediateField.adjoin b₀.base (range (algebraMap K b₀.top))
  have hCeq : ∀ x : b₀.top, x ∈ C ↔ x ∈ Cbase := by
    intro x
    constructor
    · intro hx
      change x ∈ IntermediateField.adjoin K
        (range (algebraMap b₀.base b₀.top)) at hx
      refine IntermediateField.adjoin_induction (F := K)
        (p := fun y _ => y ∈ Cbase) ?_ ?_ ?_ ?_ ?_ hx
      · rintro y ⟨z, rfl⟩
        exact Cbase.algebraMap_mem z
      · intro y
        exact IntermediateField.subset_adjoin b₀.base _ ⟨y, rfl⟩
      · exact fun _ _ _ _ hy hz => Cbase.add_mem hy hz
      · exact fun _ _ hy => Cbase.inv_mem hy
      · exact fun _ _ _ _ hy hz => Cbase.mul_mem hy hz
    · intro hx
      change x ∈ IntermediateField.adjoin b₀.base
        (range (algebraMap K b₀.top)) at hx
      refine IntermediateField.adjoin_induction (F := b₀.base)
        (p := fun y _ => y ∈ C) ?_ ?_ ?_ ?_ ?_ hx
      · rintro y ⟨z, rfl⟩
        exact C.algebraMap_mem z
      · intro y
        exact IntermediateField.subset_adjoin K _ ⟨y, rfl⟩
      · exact fun _ _ _ _ hy hz => C.add_mem hy hz
      · exact fun _ _ hy => C.inv_mem hy
      · exact fun _ _ _ _ hy hz => C.mul_mem hy hz
  classical
  obtain ⟨s, hs⟩ := IntermediateField.fg_top k K
  let t : Finset b₀.top := s.image (algebraMap K b₀.top)
  let D : IntermediateField b₀.base b₀.top :=
    IntermediateField.adjoin b₀.base (t : Set b₀.top)
  have hKmem : ∀ x : K, algebraMap K b₀.top x ∈ D := by
    intro x
    have hx : x ∈ IntermediateField.adjoin k (s : Set K) := by
      rw [hs]
      exact Set.mem_univ x
    refine IntermediateField.adjoin_induction (F := k)
      (p := fun y _ => algebraMap K b₀.top y ∈ D) ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy
      apply IntermediateField.subset_adjoin b₀.base (t : Set b₀.top)
      change algebraMap K b₀.top y ∈ s.image (algebraMap K b₀.top)
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    · intro y
      rw [← IsScalarTower.algebraMap_apply k K b₀.top y,
        IsScalarTower.algebraMap_apply k b₀.base b₀.top y]
      exact D.algebraMap_mem _
    · intro x y _ _ hx hy
      simpa only [map_add] using D.add_mem hx hy
    · intro x _ hx
      simpa only [map_inv₀] using D.inv_mem hx
    · intro x y _ _ hx hy
      simpa only [map_mul] using D.mul_mem hx hy
  have hD : D = Cbase := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      change x ∈ t at hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      exact IntermediateField.subset_adjoin b₀.base _ ⟨y, rfl⟩
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases hx with ⟨y, rfl⟩
      exact hKmem y
  have hD' : D = Cbase := hD
  have hCbaseFG : Cbase.FG := by
    refine ⟨t, ?_⟩
    change D = Cbase
    exact hD'
  have hCbaseFinite : Algebra.EssFiniteType b₀.base Cbase :=
    (IntermediateField.essFiniteType_iff).2 hCbaseFG
  have hCbaseSepExt : IsSeparableExtension b₀.base Cbase :=
    Formalization.Books.Algebra.Unit42.subextension_is_separable
      (Formalization.Books.Algebra.Unit44.isSeparableExtension_of_isSeparablyGenerated
        b₀.topSeparablyGenerated) Cbase
  have hCtopFinite :
      Algebra.EssFiniteType b₀.base (⊤ : IntermediateField b₀.base Cbase) :=
    let _ : Algebra.EssFiniteType b₀.base Cbase := hCbaseFinite
    Algebra.EssFiniteType.of_surjective
      (IntermediateField.topEquiv (F := b₀.base) (E := Cbase)).symm.toAlgHom
      (IntermediateField.topEquiv (F := b₀.base) (E := Cbase)).symm.surjective
  have hCbase : IsSeparablyGenerated b₀.base Cbase :=
    isSeparablyGenerated_of_algEquiv
      (IntermediateField.topEquiv (F := b₀.base) (E := Cbase))
      (hCbaseSepExt (⊤ : IntermediateField b₀.base Cbase) hCtopFinite)
  let e₀ : Cbase →ₐ[b₀.base] C :=
    { toFun := fun x => ⟨x.1, (hCeq x.1).2 x.2⟩
      map_one' := by rfl
      map_mul' := by intros; rfl
      map_zero' := by rfl
      map_add' := by intros; rfl
      commutes' := by intro x; rfl }
  have he₀ : Function.Bijective e₀ := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      simpa [e₀] using congrArg Subtype.val hxy
    · intro x
      refine ⟨⟨x.1, (hCeq x.1).1 x.2⟩, ?_⟩
      rfl
  let e : Cbase ≃ₐ[b₀.base] C := AlgEquiv.ofBijective e₀ he₀
  have hC : IsSeparablyGenerated b₀.base C :=
    isSeparablyGenerated_of_algEquiv e hCbase
  let b : PurelyInseparableBaseChange k K :=
    { base := b₀.base
      top := C
      topSeparablyGenerated := hC }
  let : IsPurelyInseparable K C :=
    IntermediateField.isPurelyInseparable_tower_bot K b₀.top C
  have hcomp :
      IntermediateField.adjoin b₀.base (range (algebraMap K C)) = ⊤ := by
    apply top_unique
    intro x hx
    have hx' : (x : b₀.top) ∈
        IntermediateField.adjoin K (range (algebraMap b₀.base b₀.top)) := x.2
    have hx'' : ∃ z : C,
        (z : b₀.top) = (x : b₀.top) ∧ z ∈ IntermediateField.adjoin b₀.base
          (range (algebraMap K C)) := by
      refine IntermediateField.adjoin_induction (F := K)
        (p := fun y _ => ∃ z : C,
          (z : b₀.top) = y ∧ z ∈ IntermediateField.adjoin b₀.base
            (range (algebraMap K C))) ?_ ?_ ?_ ?_ ?_ hx'
      · rintro y ⟨z, rfl⟩
        refine ⟨algebraMap b₀.base C z, ?_, ?_⟩
        · rfl
        · exact (IntermediateField.adjoin b₀.base
            (range (algebraMap K C))).algebraMap_mem z
      · intro y
        refine ⟨algebraMap K C y, ?_, ?_⟩
        · rfl
        · exact IntermediateField.subset_adjoin b₀.base _ ⟨y, rfl⟩
      · rintro x y hx hy ⟨x', hx', hxs⟩ ⟨y', hy', hys⟩
        refine ⟨x' + y', ?_, ?_⟩
        · exact congrArg₂ (· + ·) hx' hy'
        · exact (IntermediateField.adjoin b₀.base
            (range (algebraMap K C))).add_mem hxs hys
      · rintro x hx ⟨x', hx', hxs⟩
        refine ⟨x'⁻¹, ?_, ?_⟩
        · exact congrArg Inv.inv hx'
        · exact (IntermediateField.adjoin b₀.base
            (range (algebraMap K C))).inv_mem hxs
      · rintro x y hx hy ⟨x', hx', hxs⟩ ⟨y', hy', hys⟩
        refine ⟨x' * y', ?_, ?_⟩
        · exact congrArg₂ (· * ·) hx' hy'
        · exact (IntermediateField.adjoin b₀.base
            (range (algebraMap K C))).mul_mem hxs hys
    rcases hx'' with ⟨z, hz, hzm⟩
    have hzx : z = x := Subtype.ext hz
    simpa [← hzx] using hzm
  refine ⟨b, ?_, ?_, ?_⟩
  · simp only [IsSeparableBaseChange]
    exact Formalization.Books.Algebra.Unit44.isSeparableExtension_of_isSeparablyGenerated hC
  · simp only [IsCompositumBaseChange]
    exact hcomp
  · simp only [IsReducedTensorProductBaseChange]
    change Nonempty (((b₀.base ⊗[k] K) ⧸ (nilradical (b₀.base ⊗[k] K))) ≃ₐ[k] C)
    let : IsScalarTower k k b₀.base := by
      apply IsScalarTower.of_algebraMap_eq'
      ext x
      simp
    let : IsScalarTower k k C := by
      apply IsScalarTower.of_algebraMap_eq'
      ext x
      rfl
    let f : (b₀.base ⊗[k] K) →ₐ[k] C :=
      Algebra.TensorProduct.lift
        (IsScalarTower.toAlgHom k b₀.base C)
        (IsScalarTower.toAlgHom k K C)
        (fun _ _ => Commute.all _ _)
    let : Algebra K (b₀.base ⊗[k] K) :=
      Algebra.TensorProduct.rightAlgebra
    let fK : (b₀.base ⊗[k] K) →ₐ[K] C :=
      { f.toRingHom with
        commutes' := by
          intro x
          change f (1 ⊗ₜ[k] x) = algebraMap K C x
          simp [f] }
    let S : Subalgebra K C := fK.range
    let : Algebra.IsAlgebraic K C :=
      IsPurelyInseparable.isAlgebraic K C
    have hf : Function.Surjective f := by
      intro x
      have hx : x ∈ IntermediateField.adjoin b₀.base
          (range (algebraMap K C)) := by
        rw [hcomp]
        exact Set.mem_univ x
      refine IntermediateField.adjoin_induction (F := b₀.base)
        (p := fun y _ => ∃ z, f z = y) ?_ ?_ ?_ ?_ ?_ hx
      · rintro y ⟨z, rfl⟩
        exact ⟨Algebra.TensorProduct.includeRight z, by simp [f]⟩
      · intro y
        refine ⟨(Algebra.TensorProduct.includeLeft :
          b₀.base →ₐ[k] b₀.base ⊗[k] K) y, ?_⟩
        have hleft :=
          congrArg (fun g => g y)
            (Algebra.TensorProduct.lift_comp_includeLeft
              (R := k) (S := k) (A := b₀.base) (B := K) (C := C)
              (IsScalarTower.toAlgHom k b₀.base C)
              (IsScalarTower.toAlgHom k K C)
              (fun _ _ => Commute.all _ _))
        change f ((Algebra.TensorProduct.includeLeft :
          b₀.base →ₐ[k] b₀.base ⊗[k] K) y) = (algebraMap b₀.base C) y
        exact hleft
      · rintro x y hx hy ⟨x', hxf⟩ ⟨y', hyf⟩
        exact ⟨x' + y', by rw [map_add, hxf, hyf]⟩
      · rintro x hx ⟨x', hxf⟩
        have hxin : x ∈ S := ⟨x', hxf⟩
        have hxalg : IsAlgebraic K ((⟨x, hxin⟩ : S) : C) := by
          simpa using (Algebra.IsAlgebraic.isAlgebraic (x : C))
        have hinv :=
          S.inv_mem_of_algebraic
            (x := (⟨x, hxin⟩ : S)) hxalg
        rcases hinv with
          ⟨y', hy'⟩
        exact ⟨y', hy'⟩
      · rintro x y hx hy ⟨x', hxf⟩ ⟨y', hyf⟩
        exact ⟨x' * y', by rw [map_mul, hxf, hyf]⟩
    have hker : RingHom.ker f.toRingHom = nilradical (b₀.base ⊗[k] K) := by
      ext x
      constructor
      · intro hx
        change f x = 0 at hx
        change IsNilpotent x
        let comm := Algebra.TensorProduct.comm k b₀.base K
        let : Algebra K (K ⊗[k] b₀.base) :=
          Algebra.TensorProduct.leftAlgebra
        obtain ⟨n, hn, r, hr⟩ :=
          IsPurelyInseparable.exists_pow_mem_range_tensorProduct
            (k := k) (K := b₀.base) (R := K) (comm x)
        refine ⟨n, ?_⟩
        have hr' : algebraMap K (b₀.base ⊗[k] K) r = x ^ n := by
          simpa [comm, Algebra.TensorProduct.right_algebraMap_apply] using
            congrArg comm.symm hr
        have hxK : fK x = 0 := by
          simpa [fK] using hx
        have hfr : fK (algebraMap K (b₀.base ⊗[k] K) r) = 0 := by
          rw [hr', map_pow, hxK, zero_pow (Nat.ne_of_gt hn)]
        have hr0 : r = 0 := by
          apply FaithfulSMul.algebraMap_injective K C
          simpa [fK] using hfr
        rw [← hr', hr0]
        simp
      · intro hx
        change IsNilpotent x at hx
        change f x = 0
        apply (isNilpotent_iff_eq_zero.mp ?_)
        rcases hx with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [← map_pow, hn, map_zero]
    refine ⟨?_⟩
    rw [← hker]
    exact Ideal.quotientKerAlgEquivOfSurjective hf

/-! ## Perfect closures -/

/- The source's characteristic-free `k^{perf}` is the relative perfect
   closure of `k` in an algebraic closure. -/
/-- The canonical relative perfect closure is purely inseparable over the
    base and is a perfect field. -/
theorem perfectClosure_is_purelyInseparable_and_perfect
    (k : Type u) [Field k] :
    IsPurelyInseparable k (perfectClosure k (AlgebraicClosure k)) ∧
      PerfectField (perfectClosure k (AlgebraicClosure k)) := by
  constructor
  · infer_instance
  · infer_instance

/-- In characteristic zero the canonical perfect closure is the base field,
    represented as the bottom intermediate field. -/
theorem perfectClosure_eq_bot_of_charZero
    (k : Type u) [Field k] [CharZero k] :
    perfectClosure k (AlgebraicClosure k) = ⊥ := by
  exact perfectClosure.eq_bot_of_isSeparable k (AlgebraicClosure k)

/-- Any two purely inseparable perfect extensions of a field are uniquely
    isomorphic as extensions of that field. -/
theorem perfectClosure_unique_up_to_unique_algEquiv
    {k : Type u} {k' : Type v} {k'' : Type w}
    [Field k] [Field k'] [Field k'']
    [Algebra k k'] [Algebra k k'']
    [IsPurelyInseparable k k'] [IsPurelyInseparable k k'']
    [PerfectField k'] [PerfectField k''] :
    ∃ e : k' ≃ₐ[k] k'', ∀ e' : k' ≃ₐ[k] k'', e' = e := by
  let e : k' →ₐ[k] k'' := Classical.arbitrary _
  let E : k' ≃ₐ[k] k'' := AlgEquiv.ofBijective e ⟨e.injective, by
    intro y
    let f : k'' →ₐ[k] k' := Classical.arbitrary _
    have h : e.comp f = AlgHom.id k k'' := Subsingleton.elim _ _
    exact ⟨f y, congrArg (fun g : k'' →ₐ[k] k'' => g y) h⟩⟩
  refine ⟨E, ?_⟩
  intro e'
  apply AlgEquiv.ext
  intro x
  have hEq : e'.toAlgHom = E.toAlgHom := Subsingleton.elim _ _
  exact congrArg (fun g : k' →ₐ[k] k'' => g x) hEq

/- Mathlib's absolute perfect closure presents the positive-characteristic
   levels `k^(1/p^n)` by representatives `PerfectClosure.mk (n, x)`. -/
/- `PerfectClosure.of` is the canonical structure map, and its associated
   algebra instance is needed to form the intermediate fields generated by
   the finite root levels below. -/
noncomputable instance perfectClosureAlgebra
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    Algebra k (PerfectClosure k p) :=
  (PerfectClosure.of k p).toAlgebra

/-- The canonical finite `p^n`-th-root level inside the absolute perfect
    closure. -/
noncomputable def pthRootLevel
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) :
    IntermediateField k (PerfectClosure k p) :=
  IntermediateField.adjoin k
    (range fun x : k => PerfectClosure.mk k p (n, x))

/-- Every element of the finite root level has a `p^n`-th root in the level
    for each element of the base field. -/
theorem pthRootLevel_has_roots
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) (x : k) :
    ∃ y : pthRootLevel k p n,
      (y : PerfectClosure k p) ^ (p ^ n) = PerfectClosure.of k p x := by
  refine ⟨⟨PerfectClosure.mk k p (n, x), IntermediateField.subset_adjoin k _ ⟨x, rfl⟩⟩, ?_⟩
  rw [← PerfectClosure.iterate_frobenius_mk k p n x, iterate_frobenius]

/-- Every element of the finite root level has its `p^n`-th power in the base
    field. -/
theorem pthRootLevel_element_pow_mem_base
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) (y : pthRootLevel k p n) :
    ∃ x : k,
      (y : PerfectClosure k p) ^ (p ^ n) = PerfectClosure.of k p x := by
  rcases y with ⟨y, hy⟩
  change ∃ x : k, y ^ (p ^ n) = PerfectClosure.of k p x
  refine IntermediateField.adjoin_induction (F := k)
    (p := fun z _ => ∃ x : k, z ^ (p ^ n) = PerfectClosure.of k p x) ?_ ?_ ?_ ?_ ?_ hy
  · rintro z ⟨x, rfl⟩
    exact ⟨x, by rw [← PerfectClosure.iterate_frobenius_mk k p n x, iterate_frobenius]⟩
  · intro x
    refine ⟨x ^ (p ^ n), ?_⟩
    change (PerfectClosure.of k p x) ^ (p ^ n) = PerfectClosure.of k p (x ^ (p ^ n))
    exact (map_pow (PerfectClosure.of k p) x (p ^ n)).symm
  · rintro x z hx hz ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [add_pow_char_pow, ha, hb, map_add]
  · rintro x hx ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    rw [inv_pow, ha]
    exact (map_inv₀ (PerfectClosure.of k p) a).symm
  · rintro x z hx hz ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    simp only [mul_pow, ha, hb, map_mul]

/-- Each finite root level is algebraic over its base field. -/
theorem pthRootLevel_is_algebraic
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) :
    Algebra.IsAlgebraic k (pthRootLevel k p n) := by
  let _ : ExpChar k p := ExpChar.prime Fact.out
  let _ : IsPurelyInseparable k (pthRootLevel k p n) := by
    rw [pthRootLevel,
      IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem k (PerfectClosure k p) p]
    rintro _ ⟨x, rfl⟩
    refine ⟨n, x, ?_⟩
    change PerfectClosure.of k p x =
      (PerfectClosure.mk k p (n, x)) ^ (p ^ n)
    rw [← PerfectClosure.iterate_frobenius_mk k p n x, iterate_frobenius]
  exact IsPurelyInseparable.isAlgebraic k _

/-- Each finite root level is purely inseparable over its base field. -/
theorem pthRootLevel_is_purelyInseparable
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) :
    IsPurelyInseparable k (pthRootLevel k p n) := by
  let _ : ExpChar k p := ExpChar.prime Fact.out
  rw [pthRootLevel,
    IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem k (PerfectClosure k p) p]
  rintro _ ⟨x, rfl⟩
  refine ⟨n, x, ?_⟩
  change PerfectClosure.of k p x =
    (PerfectClosure.mk k p (n, x)) ^ (p ^ n)
  rw [← PerfectClosure.iterate_frobenius_mk k p n x, iterate_frobenius]

/-- The finite root levels form an increasing tower inside the absolute
    perfect closure. -/
theorem pthRootLevel_mono
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) :
    pthRootLevel k p n ≤ pthRootLevel k p (n + 1) := by
  unfold pthRootLevel
  apply IntermediateField.adjoin.mono k
  rintro _ ⟨x, rfl⟩
  exact ⟨x ^ p, PerfectClosure.mk_succ_pow k p n x⟩

/-- The finite root level is uniquely determined, up to a unique isomorphism,
    by its algebraicity and its two `p^n`-power properties. -/
theorem pthRootLevel_unique_up_to_unique_algEquiv
    {k : Type u} {L : Type v} [Field k] [Field L] (p : ℕ) [Fact p.Prime] [CharP k p]
    [Algebra k L] (n : ℕ) (hn : 0 < n) [Algebra.IsAlgebraic k L]
    (hroot : ∀ x : k, ∃ y : L,
      y ^ (p ^ n) = algebraMap k L x)
    (hbase : ∀ y : L, ∃ x : k,
      y ^ (p ^ n) = algebraMap k L x) :
    ∃ e : pthRootLevel k p n ≃ₐ[k] L,
      ∀ e' : pthRootLevel k p n ≃ₐ[k] L, e' = e := by
  let _ : ExpChar k p := ExpChar.prime Fact.out
  let _ : CharP L p := charP_of_injective_algebraMap' k p
  let _ : ExpChar L p := ExpChar.prime Fact.out
  let _ : CharP (pthRootLevel k p n) p := charP_of_injective_algebraMap' k p
  let _ : ExpChar (pthRootLevel k p n) p := ExpChar.prime Fact.out
  let _ : ExpChar (PerfectClosure k p) p := ExpChar.prime Fact.out
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpowL : Function.Injective (fun y : L => y ^ (p ^ n)) := by
    intro y z h
    apply iterateFrobenius_inj L p n
    simpa [iterateFrobenius_def, hp0] using h
  have hpowC : Function.Injective
      (fun y : PerfectClosure k p => y ^ (p ^ n)) := by
    intro y z h
    apply iterateFrobenius_inj (PerfectClosure k p) p n
    simpa [iterateFrobenius_def, hp0] using h
  let g : L →+* k :=
    { toFun := fun y => Classical.choose (hbase y)
      map_one' := by
        apply FaithfulSMul.algebraMap_injective k L
        rw [← Classical.choose_spec (hbase 1)]
        simp [hp0]
      map_mul' := by
        intro y z
        apply FaithfulSMul.algebraMap_injective k L
        rw [← Classical.choose_spec (hbase (y * z)), map_mul,
          ← Classical.choose_spec (hbase y), ← Classical.choose_spec (hbase z),
          mul_pow]
      map_zero' := by
        apply FaithfulSMul.algebraMap_injective k L
        rw [← Classical.choose_spec (hbase 0)]
        simp [hp0]
      map_add' := by
        intro y z
        apply FaithfulSMul.algebraMap_injective k L
        rw [← Classical.choose_spec (hbase (y + z)), map_add,
          ← Classical.choose_spec (hbase y), ← Classical.choose_spec (hbase z),
          add_pow_char_pow] }
  have hg_spec (y : L) : y ^ (p ^ n) = algebraMap k L (g y) :=
    Classical.choose_spec (hbase y)
  have hg_base (x : k) : g (algebraMap k L x) = x ^ (p ^ n) := by
    apply FaithfulSMul.algebraMap_injective k L
    rw [map_pow, ← hg_spec]
  have hmk (x : k) :
      (PerfectClosure.mk k p (n, x)) ^ (p ^ n) = PerfectClosure.of k p x := by
    rw [← PerfectClosure.iterate_frobenius_mk k p n x, iterate_frobenius]
  let r : k →+* pthRootLevel k p n :=
    { toFun := fun x =>
        ⟨PerfectClosure.mk k p (n, x),
          IntermediateField.subset_adjoin k _ ⟨x, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        apply hpowC
        change (PerfectClosure.mk k p (n, 1)) ^ (p ^ n) =
          (1 : PerfectClosure k p) ^ (p ^ n)
        rw [hmk, map_one]
        simp [hp0]
      map_mul' := by
        intro x y
        apply Subtype.ext
        apply hpowC
        change (PerfectClosure.mk k p (n, x * y)) ^ (p ^ n) =
          (PerfectClosure.mk k p (n, x) * PerfectClosure.mk k p (n, y)) ^ (p ^ n)
        rw [hmk, mul_pow, hmk, hmk, map_mul]
      map_zero' := by
        apply Subtype.ext
        apply hpowC
        change (PerfectClosure.mk k p (n, 0)) ^ (p ^ n) =
          (0 : PerfectClosure k p) ^ (p ^ n)
        rw [hmk, map_zero]
        simp [hp0]
      map_add' := by
        intro x y
        apply Subtype.ext
        apply hpowC
        change (PerfectClosure.mk k p (n, x + y)) ^ (p ^ n) =
          (PerfectClosure.mk k p (n, x) + PerfectClosure.mk k p (n, y)) ^ (p ^ n)
        rw [hmk, add_pow_char_pow, hmk, hmk, map_add] }
  have hr_pow (x : k) :
      ((r x : pthRootLevel k p n) : PerfectClosure k p) ^ (p ^ n) =
        PerfectClosure.of k p x :=
    hmk x
  let φ : L →ₐ[k] pthRootLevel k p n :=
    { toRingHom := r.comp g
      commutes' := by
        intro x
        change r (g (algebraMap k L x)) = algebraMap k (pthRootLevel k p n) x
        apply Subtype.ext
        apply hpowC
        change ((r (g (algebraMap k L x)) : pthRootLevel k p n) :
            PerfectClosure k p) ^ (p ^ n) =
          ((algebraMap k (pthRootLevel k p n) x : pthRootLevel k p n) :
            PerfectClosure k p) ^ (p ^ n)
        rw [hr_pow, hg_base, map_pow]
        change (PerfectClosure.of k p x) ^ (p ^ n) =
          (PerfectClosure.of k p x) ^ (p ^ n)
        rfl }
  have hφ_pow (y : L) :
      ((φ y : pthRootLevel k p n) : PerfectClosure k p) ^ (p ^ n) =
        PerfectClosure.of k p (g y) := by
    change ((r (g y) : pthRootLevel k p n) : PerfectClosure k p) ^ (p ^ n) = _
    exact hr_pow (g y)
  have hφ_pow' (y : L) :
      (φ y : pthRootLevel k p n) ^ (p ^ n) =
        algebraMap k (pthRootLevel k p n) (g y) := by
    apply Subtype.ext
    exact hφ_pow y
  have hφ_inj : Function.Injective φ := by
    intro y z hyz
    apply hpowL
    change y ^ (p ^ n) = z ^ (p ^ n)
    rw [hg_spec y, hg_spec z]
    have h := congrArg (fun w : pthRootLevel k p n =>
      ((w : PerfectClosure k p) ^ (p ^ n))) hyz
    rw [hφ_pow y, hφ_pow z] at h
    exact congrArg (algebraMap k L)
      (FaithfulSMul.algebraMap_injective k (PerfectClosure k p) h)
  have hφ_surj : Function.Surjective φ := by
    intro z
    obtain ⟨x, hx⟩ := pthRootLevel_element_pow_mem_base p n z
    obtain ⟨y, hy⟩ := hroot x
    have hgy : g y = x := by
      apply FaithfulSMul.algebraMap_injective k L
      exact (hg_spec y).symm.trans hy
    refine ⟨y, ?_⟩
    apply Subtype.ext
    apply hpowC
    change ((φ y : pthRootLevel k p n) : PerfectClosure k p) ^ (p ^ n) =
      (z : PerfectClosure k p) ^ (p ^ n)
    rw [hφ_pow, hgy, ← hx]
  let e₀ : L ≃ₐ[k] pthRootLevel k p n := AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  let e : pthRootLevel k p n ≃ₐ[k] L := e₀.symm
  refine ⟨e, ?_⟩
  intro e'
  apply AlgEquiv.ext
  intro z
  obtain ⟨y, hy⟩ := e₀.surjective z
  have hey : e' (φ y) = y := by
    apply hpowL
    calc
      e' (φ y) ^ (p ^ n) = e' ((φ y) ^ (p ^ n)) := by
        rw [map_pow]
      _ = e' (algebraMap k (pthRootLevel k p n) (g y)) := by
        rw [hφ_pow']
      _ = algebraMap k L (g y) := e'.commutes _
      _ = y ^ (p ^ n) := (hg_spec y).symm
  rw [← hy]
  calc
    e' (e₀ y) = y := by
      change e' (φ y) = y
      exact hey
    _ = e (e₀ y) := by simp [e, e₀]

/-- Every element of the canonical `p`-th-root level has the expected
    `p^n`-th power in the base. -/
theorem perfectClosure_mk_pow
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) (x : k) :
    (PerfectClosure.mk k p (n, x)) ^ (p ^ n) = PerfectClosure.of k p x := by
  rw [← PerfectClosure.iterate_frobenius_mk k p n x, iterate_frobenius]

/-- Every element of the absolute perfect closure occurs at some finite
    `p`-th-root level. -/
theorem perfectClosure_is_union_of_pth_root_levels
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∀ y : PerfectClosure k p,
      ∃ n : ℕ, ∃ x : k, y = PerfectClosure.mk k p (n, x) := by
  intro y
  obtain ⟨⟨n, x⟩, h⟩ := PerfectClosure.mk_surjective k p y
  exact ⟨n, x, h.symm⟩

/-- An element represented at level `n` has its `p^n`-th power in the base. -/
theorem perfectClosure_level_element_pow_mem_base
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) (y : PerfectClosure k p)
    (hy : ∃ x : k, y = PerfectClosure.mk k p (n, x)) :
    ∃ x : k, y ^ (p ^ n) = PerfectClosure.of k p x := by
  sorry

/-- The absolute perfect closure is the union of its positive finite root
    levels. -/
theorem perfectClosure_is_union_of_finite_pth_root_levels
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∀ y : PerfectClosure k p,
      ∃ n : ℕ, 0 < n ∧
        ∃ z : pthRootLevel k p n, (z : PerfectClosure k p) = y := by
  sorry

/- The source's subextension observation is stated with the necessary choice
   of an embedding into a fixed algebraic closure. -/
/-- An algebraic purely inseparable extension embeds over the base into the
    canonical perfect closure inside an algebraic closure. -/
theorem algebraic_purelyInseparable_extension_embeds_in_perfectClosure
    {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E]
    [Algebra.IsAlgebraic k E] [IsPurelyInseparable k E] :
    ∃ i : E →ₐ[k] AlgebraicClosure k,
      ∀ x : E, i x ∈ perfectClosure k (AlgebraicClosure k) := by
  sorry

/-! ## Perfect fields and reduced algebras -/

/-- A reduced algebra over a perfect field is geometrically reduced. -/
theorem isGeometricallyReduced_of_perfectField
    {k : Type u} {S : Type v} [Field k] [CommRing S]
    [Algebra k S] [PerfectField k] (hS : IsReduced S) :
    IsGeometricallyReduced k S := by
  sorry

/-- The tensor product of two reduced algebras over a perfect field is
    reduced. -/
theorem isReduced_tensorProduct_of_perfectField
    {k : Type u} {R : Type v} {S : Type w} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [PerfectField k]
    (hR : IsReduced R) (hS : IsReduced S) :
    IsReduced (R ⊗[k] S) := by
  sorry

end

end Formalization.Books.Algebra.Unit45
