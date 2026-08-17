import Formalization.Books.Fields.Unit06.FieldExtensions
import Formalization.Books.Fields.Unit12.SeparableAlgebraicExtensions
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Fields, Chapter 14: Purely inseparable extensions

Mathlib's `IsPurelyInseparable` is the canonical extension predicate used by
this chapter.  Its `isPurelyInseparable_iff_pow_mem` characterization records
the source's p-power definition, while `perfectClosure` is the canonical
intermediate field formed by the purely inseparable elements.  The source's
separable and inseparable degrees are `Field.sepDegree` and
`Field.insepDegree`; the finite embedding count is `Field.finSepDegree`.
-/

namespace Formalization.Books.Fields.Unit14

noncomputable section

open Polynomial
open scoped BigOperators

universe u v w

/-! ## Definitions and the p-th-root example -/

/- The source's extension predicate is Mathlib's `IsPurelyInseparable`.
   The characteristic-free convention includes the identity extension through
   Mathlib's canonical `isPurelyInseparable_self` instance. -/
/-- The identity field extension is purely inseparable. -/
theorem purely_inseparable_self_extension
    (F : Type u) [Field F] : IsPurelyInseparable F F :=
  inferInstance

/- `perfectClosure` is Mathlib's canonical intermediate field of all elements
   satisfying the source's element-level p-power condition. -/
/-- An element is purely inseparable over the base exactly when it lies in the
    relative perfect closure. -/
theorem purely_inseparable_element_iff_pow_mem
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : ℕ) (hp : p.Prime) [CharP F p] (α : E) :
    α ∈ perfectClosure F E ↔
      ∃ n : ℕ, α ^ p ^ n ∈ (algebraMap F E).range := by
  let _ : Fact p.Prime := ⟨hp⟩
  exact mem_perfectClosure_iff_pow_mem p

/- The simple-extension form is also useful for the source's p-th-root
   example, and is already part of Mathlib's perfect-closure API. -/
/-- A simple extension is purely inseparable exactly when its generator has a
    p-power in the base field. -/
theorem purely_inseparable_simple_extension_iff_pow_mem
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : ℕ) (hp : p.Prime) [CharP F p] (α : E) :
    IsPurelyInseparable F (IntermediateField.adjoin F ({α} : Set E)) ↔
      ∃ n : ℕ, α ^ p ^ n ∈ (algebraMap F E).range := by
  let _ : Fact p.Prime := ⟨hp⟩
  exact IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem F E p

/-- Over a field of exponential characteristic `p`, an extension is purely
    inseparable exactly when every element becomes a p-power in the base. -/
theorem purely_inseparable_extension_iff_pow_mem
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : ℕ) (hp : p.Prime) [CharP F p] :
    IsPurelyInseparable F E ↔
      ∀ x : E, ∃ n : ℕ, x ^ p ^ n ∈ (algebraMap F E).range := by
  let _ : Fact p.Prime := ⟨hp⟩
  exact isPurelyInseparable_iff_pow_mem F p

/- The source's observation that purely inseparable extensions are algebraic is
   already a field of the canonical Mathlib class. -/
/-- A purely inseparable field extension is algebraic. -/
theorem purely_inseparable_extension_is_algebraic
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsPurelyInseparable F E] : Algebra.IsAlgebraic F E :=
  IsPurelyInseparable.isAlgebraic F E

/-- In characteristic zero, a purely inseparable field extension is the
    identity extension in the sense that its base-field map is surjective. -/
theorem purely_inseparable_char_zero_is_trivial
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero F]
    [IsPurelyInseparable F E] : Function.Surjective (algebraMap F E) := by
  let _ : Algebra.IsAlgebraic F E := IsPurelyInseparable.isAlgebraic F E
  let _ : Algebra.IsSeparable F E :=
    Formalization.Books.Fields.Unit12.algebraic_extension_separable_of_char_zero
  exact IsPurelyInseparable.surjective_algebraMap_of_isSeparable F E

/- The source's polynomial `x^p - t` is represented by this canonical
   polynomial interface. -/
/-- If `t` has no p-th root, then `X^p - C t` is irreducible. -/
theorem take_pth_root_polynomial_irreducible
    {F : Type u} [Field F] (p : ℕ) (hp : p.Prime) [CharP F p]
    (t : F) (ht : ∀ b : F, b ^ p ≠ t) :
    Irreducible (X ^ p - C t) :=
  X_pow_sub_C_irreducible_of_prime hp ht

/- The quotient's distinguished element is the source's `t^(1/p)`. -/
/-- The distinguished root of the p-th-root quotient has p-th power `t`. -/
theorem pth_root_extension_root_is_pth_root
    {F : Type u} [Field F] (p : ℕ) (t : F) :
    (AdjoinRoot.root (X ^ p - C t)) ^ p = AdjoinRoot.of (X ^ p - C t) t :=
  root_X_pow_sub_C_pow p t

/-- Every element of the p-th-root quotient has the source's degree-`p`
    coefficient expansion, and its p-th power is in the base field. -/
theorem pth_root_extension_element_expansion
    {F : Type u} [Field F] (p : ℕ) (hp : p.Prime) [CharP F p]
    (t : F) (z : AdjoinRoot (X ^ p - C t)) :
    ∃ a : Fin p → F,
      z = ∑ i : Fin p,
          algebraMap F (AdjoinRoot (X ^ p - C t)) (a i) *
            (AdjoinRoot.root (X ^ p - C t)) ^ (i : ℕ) ∧
      z ^ p = algebraMap F (AdjoinRoot (X ^ p - C t))
          (∑ i : Fin p, (a i) ^ p * t ^ (i : ℕ)) := by
  let pb : PowerBasis F (AdjoinRoot (X ^ p - C t)) :=
    AdjoinRoot.powerBasis (f := X ^ p - C t) (X_pow_sub_C_ne_zero hp.pos t)
  have hdim : pb.dim = p := by
    simp [pb]
  letI : Fact p.Prime := ⟨hp⟩
  letI : ExpChar (AdjoinRoot (X ^ p - C t)) p :=
    expChar_of_injective_algebraMap
      (by
        rw [AdjoinRoot.algebraMap_eq]
        exact AdjoinRoot.of.injective_of_degree_ne_zero (by
          rw [degree_X_pow_sub_C hp.pos]
          exact_mod_cast hp.ne_zero)) p
  let B : Module.Basis (Fin p) F (AdjoinRoot (X ^ p - C t)) :=
    pb.basis.reindex (finCongr hdim)
  let a : Fin p → F := B.repr z
  refine ⟨a, ?_, ?_⟩
  · simpa [a, B, pb, Module.Basis.reindex_apply, Algebra.smul_def, pb.basis_eq_pow] using
      (B.sum_repr z).symm
  · have hroot : ∀ i : Fin p,
        (AdjoinRoot.root (X ^ p - C t) ^ (i : ℕ)) ^ p =
          AdjoinRoot.of (X ^ p - C t) (t ^ (i : ℕ)) := by
      intro i
      rw [← pow_mul, Nat.mul_comm, pow_mul, root_X_pow_sub_C_pow p t, map_pow]
    have hB : ∀ i : Fin p,
        B i = AdjoinRoot.root (X ^ p - C t) ^ (i : ℕ) := by
      intro i
      simp [B, Module.Basis.reindex_apply, pb, pb.basis_eq_pow]
    rw [← B.sum_repr z, sum_pow_char]
    simp only [Algebra.smul_def]
    simp_rw [mul_pow]
    simp_rw [← map_pow]
    simp_rw [hB]
    simp_rw [hroot]
    rw [AdjoinRoot.algebraMap_eq]
    simp_rw [← map_mul]
    rw [← map_sum]

/-- Adjoining a p-th root of an element without a p-th root gives a field and
    a purely inseparable extension. -/
theorem pth_root_adjoinRoot_field_and_purely_inseparable
    {F : Type u} [Field F] (p : ℕ) (hp : p.Prime) [CharP F p]
    (t : F) (ht : ∀ b : F, b ^ p ≠ t) :
    IsField (AdjoinRoot (X ^ p - C t)) ∧
      IsPurelyInseparable F (AdjoinRoot (X ^ p - C t)) := by
  let hfield : IsField (AdjoinRoot (X ^ p - C t)) :=
    Formalization.Books.Fields.Unit06.adjoinRoot_isField_of_irreducible
      (take_pth_root_polynomial_irreducible p hp t ht)
  letI : Field (AdjoinRoot (X ^ p - C t)) := hfield.toField
  refine ⟨hfield, ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  rw [isPurelyInseparable_iff_pow_mem F p]
  intro z
  obtain ⟨a, _, hz⟩ := pth_root_extension_element_expansion p hp t z
  refine ⟨1, ∑ i : Fin p, (a i) ^ p * t ^ (i : ℕ), ?_⟩
  simpa using hz.symm

/- The rational-function sentence in the source is made explicit using
   `RatFunc.X` over the prime field `ZMod p`. -/
/-- The rational-function indeterminate is not a p-th power. -/
theorem rational_function_indeterminate_not_pth_power
    (p : ℕ) [Fact p.Prime] :
    ∀ b : RatFunc (ZMod p), b ^ p ≠ (RatFunc.X : RatFunc (ZMod p)) := by
  intro b h
  have hp : p.Prime := Fact.out
  have hb : b ≠ 0 := by
    intro hb
    exact (RatFunc.X_ne_zero (K := ZMod p))
      (by simpa [hb, zero_pow hp.ne_zero] using h.symm)
  have hpow : ∀ n : ℕ,
      RatFunc.intDegree (b ^ n) = (n : ℤ) * RatFunc.intDegree b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ hb) hb, ih]
        push_cast
        ring
  have hdeg : (p : ℤ) * RatFunc.intDegree b = 1 := by
    rw [← hpow p, h, RatFunc.intDegree_X]
  have hdiv : (p : ℤ) ∣ (1 : ℤ) := ⟨RatFunc.intDegree b, hdeg.symm⟩
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hdiv)

/-- The rational-function field supplies the source's p-th-root example. -/
theorem rational_function_pth_root_extension
    (p : ℕ) [Fact p.Prime] :
    Irreducible
        (X ^ p - C (RatFunc.X : RatFunc (ZMod p))) ∧
      IsField
        (AdjoinRoot (X ^ p - C (RatFunc.X : RatFunc (ZMod p)))) ∧
      IsPurelyInseparable
        (RatFunc (ZMod p))
        (AdjoinRoot (X ^ p - C (RatFunc.X : RatFunc (ZMod p)))) := by
  have hp : p.Prime := Fact.out
  have ht : ∀ b : RatFunc (ZMod p),
      b ^ p ≠ (RatFunc.X : RatFunc (ZMod p)) :=
    rational_function_indeterminate_not_pth_power p
  have h := pth_root_adjoinRoot_field_and_purely_inseparable p hp
    (RatFunc.X : RatFunc (ZMod p)) ht
  exact ⟨take_pth_root_polynomial_irreducible p hp _ ht, h.1, h.2⟩

/-! ## Permanence and the purely inseparable subextension -/

/- This is Mathlib's tower theorem, with the source's field-extension
   notation made explicit through `Algebra` and `IsScalarTower`. -/
/-- Purely inseparable extensions are transitive in a field tower. -/
theorem purely_inseparable_extension_permanence
    {k E F : Type*} [Field k] [Field E] [Field F]
    [Algebra k E] [Algebra E F] [Algebra k F] [IsScalarTower k E F]
    [IsPurelyInseparable k E] [IsPurelyInseparable E F] :
    IsPurelyInseparable k F :=
  IsPurelyInseparable.trans k E F

/- `perfectClosure F E` is Mathlib's canonical subextension of all elements
   satisfying the source's purely-inseparable element condition. -/
/-- The purely inseparable elements form an intermediate field. -/
theorem purely_inseparable_elements_form_subextension
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    ∃ L : IntermediateField F E, ∀ x : E,
      x ∈ L ↔
        ∃ n : ℕ, x ^ (ringExpChar F) ^ n ∈ (algebraMap F E).range := by
  refine ⟨perfectClosure F E, ?_⟩
  exact fun _ => mem_perfectClosure_iff

/-! ## Finite purely inseparable extensions -/

/- The finite tower is expressed with Unit 12's ordered generator family and
   its canonical prefix intermediate fields.  This retains the source's
   successive fields while reusing the established field-extension interface. -/
private theorem purely_inseparable_pth_root_step
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : ℕ} (hp : p.Prime) [CharP F p]
    [FiniteDimensional F E] [IsPurelyInseparable F E]
    (x : E) (hx : x ∉ (algebraMap F E).range) :
    ∃ w : E, ∃ y : F,
      w ^ p = algebraMap F E y ∧
        (∀ z : F, z ^ p ≠ y) ∧
          Module.finrank F (IntermediateField.adjoin F ({w} : Set E)) = p := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : ExpChar E p :=
    expChar_of_injective_algebraMap (algebraMap F E).injective p
  letI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  let e := IsPurelyInseparable.elemExponent F x
  let w := x ^ p ^ (e - 1)
  let y := IsPurelyInseparable.elemReduct F x
  have he_mem : x ^ p ^ e ∈ (algebraMap F E).range := by
    exact IsPurelyInseparable.elemExponent_def' F p x
  have he_ne : e ≠ 0 := by
    intro he
    apply hx
    simpa [e, he] using he_mem
  have he_pos : 0 < e := Nat.pos_of_ne_zero he_ne
  have he_sub_lt : e - 1 < e := by omega
  have hw_not : w ∉ (algebraMap F E).range := by
    dsimp [w, e]
    exact IsPurelyInseparable.elemExponent_min' F p he_sub_lt
  have hw_pow : w ^ p = algebraMap F E y := by
    change (x ^ p ^ (e - 1)) ^ p = algebraMap F E y
    calc
      (x ^ p ^ (e - 1)) ^ p = x ^ (p ^ (e - 1) * p) := by rw [← pow_mul]
      _ = x ^ p ^ e := by
        rw [← pow_succ,
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he_ne)]
      _ = algebraMap F E y :=
        (IsPurelyInseparable.algebraMap_elemReduct_eq' F p x).symm
  have hy : ∀ z : F, z ^ p ≠ y := by
    intro z hz
    apply hw_not
    refine ⟨z, ?_⟩
    apply sub_eq_zero.mp
    apply eq_zero_of_pow_eq_zero (n := p)
    rw [sub_pow_expChar, hw_pow, ← map_pow, hz, sub_self]
  have hw_exp_le : IsPurelyInseparable.elemExponent F w ≤ 1 := by
    apply IsPurelyInseparable.elemExponent_le_of_pow_mem' p
    exact ⟨y, by simpa using hw_pow.symm⟩
  have hw_exp_ne : IsPurelyInseparable.elemExponent F w ≠ 0 := by
    intro hw_exp
    apply hw_not
    simpa [hw_exp] using
      (IsPurelyInseparable.elemExponent_def' F p w)
  have hw_exp : IsPurelyInseparable.elemExponent F w = 1 := by
    omega
  refine ⟨w, y, hw_pow, hy, ?_⟩
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral w),
    IsPurelyInseparable.minpoly_natDegree_eq' F p w, hw_exp, pow_one]

private theorem range_fin_cases
    {E : Type*} (w : E) {n : ℕ} (alpha : Fin n → E) :
    Set.range (Fin.cases w alpha) = ({w} : Set E) ∪ Set.range alpha := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i
  · intro hz
    rcases hz with (rfl | ⟨j, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨j.succ, rfl⟩

private theorem prepend_generated
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (w : E)
    (S : Formalization.Books.Fields.Unit12.FinitelyGeneratedFieldExtension
      (IntermediateField.adjoin F ({w} : Set E)) E) :
    IntermediateField.adjoin F (Set.range (Fin.cases w S.alpha)) = ⊤ := by
  have hgen :
      IntermediateField.adjoin F
          ((IntermediateField.adjoin F ({w} : Set E) : Set E) ∪ Set.range S.alpha) = ⊤ := by
    rw [← IntermediateField.restrictScalars_adjoin F
      (IntermediateField.adjoin F ({w} : Set E)) (Set.range S.alpha),
      S.generated, IntermediateField.restrictScalars_top]
  rw [range_fin_cases]
  calc
    IntermediateField.adjoin F ({w} ∪ Set.range S.alpha) =
        (IntermediateField.adjoin (IntermediateField.adjoin F ({w} : Set E))
          (Set.range S.alpha)).restrictScalars F := by
      symm
      exact IntermediateField.adjoin_adjoin_left (F := F) ({w} : Set E)
        (Set.range S.alpha)
    _ = IntermediateField.adjoin F
          ((IntermediateField.adjoin F ({w} : Set E) : Set E) ∪ Set.range S.alpha) :=
      IntermediateField.restrictScalars_adjoin F
        (IntermediateField.adjoin F ({w} : Set E)) (Set.range S.alpha)
    _ = ⊤ := hgen

private theorem generated_prefix_fin_cases
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (w : E) {n : ℕ} (alpha : Fin n → E) (i : Fin (n + 1)) :
    IntermediateField.adjoin F
        (Set.range (fun j : Fin i.succ =>
          Fin.cases w alpha
            (Formalization.Books.Fields.Unit12.prefixGeneratorIndex i.succ j))) =
      (IntermediateField.adjoin (IntermediateField.adjoin F ({w} : Set E))
        (Set.range (fun j : Fin i =>
          alpha (Formalization.Books.Fields.Unit12.prefixGeneratorIndex i j)))).restrictScalars F := by
  let T : Set E := Set.range (fun j : Fin i =>
    alpha (Formalization.Books.Fields.Unit12.prefixGeneratorIndex i j))
  let j0 : Fin i.succ := ⟨0, Nat.zero_lt_succ _⟩
  have hsucc (j : Fin i) :
      Formalization.Books.Fields.Unit12.prefixGeneratorIndex i.succ j.succ =
        (Formalization.Books.Fields.Unit12.prefixGeneratorIndex i j).succ := by
    rfl
  have hrange :
      Set.range (fun j : Fin i.succ =>
        Fin.cases w alpha
          (Formalization.Books.Fields.Unit12.prefixGeneratorIndex i.succ j)) =
        ({w} : Set E) ∪ T := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [Formalization.Books.Fields.Unit12.prefixGeneratorIndex, T]
      · simp [hsucc, T]
    · intro hz
      rcases hz with (rfl | ⟨k, rfl⟩)
      · refine ⟨j0, ?_⟩
        simp [j0, Formalization.Books.Fields.Unit12.prefixGeneratorIndex]
      · refine ⟨k.succ, ?_⟩
        simp [hsucc]
  rw [hrange]
  calc
    IntermediateField.adjoin F ({w} ∪ T) =
        (IntermediateField.adjoin (IntermediateField.adjoin F ({w} : Set E)) T).restrictScalars F := by
      symm
      exact IntermediateField.adjoin_adjoin_left (F := F) ({w} : Set E) T
    _ = (IntermediateField.adjoin (IntermediateField.adjoin F ({w} : Set E))
        (Set.range (fun j : Fin i =>
          alpha (Formalization.Books.Fields.Unit12.prefixGeneratorIndex i j)))).restrictScalars F := by
      rfl

private theorem prepend_pth_root_tower
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : ℕ} (_hp : p.Prime) [CharP F p]
    [FiniteDimensional F E]
    (w : E)
    (S' : Formalization.Books.Fields.Unit12.FinitelyGeneratedFieldExtension
      (IntermediateField.adjoin F ({w} : Set E)) E)
    (hbase : ∃ y : F,
      algebraMap F E y = w ^ p ∧
        (∀ z : F, z ^ p ≠ y) ∧
          Module.finrank F (IntermediateField.adjoin F ({w} : Set E)) = p)
    (hnext : ∀ i : Fin S'.n,
      ∃ y : Formalization.Books.Fields.Unit12.generatedIntermediateField
          S' i.castSucc,
        algebraMap
            (Formalization.Books.Fields.Unit12.generatedIntermediateField S' i.castSucc)
            (Formalization.Books.Fields.Unit12.generatedIntermediateField S' i.succ) y =
          (Formalization.Books.Fields.Unit12.generatorInNextField S' i) ^ p ∧
        (∀ z : Formalization.Books.Fields.Unit12.generatedIntermediateField S' i.castSucc,
          z ^ p ≠ y) ∧
        Module.finrank
            (Formalization.Books.Fields.Unit12.generatedIntermediateField S' i.castSucc)
            (Formalization.Books.Fields.Unit12.generatedIntermediateField S' i.succ) = p) :
    ∃ S : Formalization.Books.Fields.Unit12.FinitelyGeneratedFieldExtension F E,
      ∀ i : Fin S.n,
        ∃ y : Formalization.Books.Fields.Unit12.generatedIntermediateField
            S i.castSucc,
          algebraMap
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.castSucc)
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.succ) y =
            (Formalization.Books.Fields.Unit12.generatorInNextField S i) ^ p ∧
          (∀ z : Formalization.Books.Fields.Unit12.generatedIntermediateField S i.castSucc,
            z ^ p ≠ y) ∧
          Module.finrank
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.castSucc)
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.succ) = p := by
  let S : Formalization.Books.Fields.Unit12.FinitelyGeneratedFieldExtension F E :=
    { n := S'.n + 1
      alpha := Fin.cases w S'.alpha
      finite := inferInstance
      generated := by
        exact prepend_generated (F := F) (E := E) w S' }
  have hprefix (i : Fin (S'.n + 1)) :
      Formalization.Books.Fields.Unit12.generatedIntermediateField S i.succ =
        (Formalization.Books.Fields.Unit12.generatedIntermediateField S' i).restrictScalars F := by
    simpa [S, Formalization.Books.Fields.Unit12.generatedIntermediateField] using
      (generated_prefix_fin_cases (F := F) w S'.alpha i)
  refine ⟨S, ?_⟩
  change ∀ i : Fin (S'.n + 1), _
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · obtain ⟨y, hy, hyn, hyr⟩ := hbase
    let y0 : Formalization.Books.Fields.Unit12.generatedIntermediateField S
        ⟨0, Nat.zero_lt_succ _⟩ :=
      ⟨algebraMap F E y, by
        simp [Formalization.Books.Fields.Unit12.generatedIntermediateField]⟩
    refine ⟨y0, ?_, ?_, ?_⟩
    · apply Subtype.ext
      change algebraMap F E y = w ^ p
      exact hy
    · intro z hz
      have hzbot : (z : E) ∈ (⊥ : IntermediateField F E) := by
        rw [← Formalization.Books.Fields.Unit12.generatedIntermediateField_zero_eq_bot S]
        exact z.property
      obtain ⟨z0, hz0⟩ := (IntermediateField.mem_bot).1 hzbot
      apply hyn z0
      apply (algebraMap F E).injective
      have hzval := congrArg Subtype.val hz
      change (z : E) ^ p = algebraMap F E y at hzval
      simpa [hz0] using hzval
    · have h0field :
          Formalization.Books.Fields.Unit12.generatedIntermediateField S
              (Fin.castSucc (0 : Fin (S'.n + 1))) = ⊥ := by
        simpa using
          (Formalization.Books.Fields.Unit12.generatedIntermediateField_zero_eq_bot S)
      have h1field :
          Formalization.Books.Fields.Unit12.generatedIntermediateField S
              (Fin.succ (0 : Fin (S'.n + 1))) =
            IntermediateField.adjoin F ({w} : Set E) := by
        rw [hprefix (0 : Fin (S'.n + 1)),
          Formalization.Books.Fields.Unit12.generatedIntermediateField_zero_eq_bot S',
          IntermediateField.restrictScalars_bot_eq_self]
      letI : IsScalarTower F
          (Formalization.Books.Fields.Unit12.generatedIntermediateField S
            (Fin.castSucc (0 : Fin (S'.n + 1))))
          (Formalization.Books.Fields.Unit12.generatedIntermediateField S
            (Fin.succ (0 : Fin (S'.n + 1)))) :=
        IsScalarTower.of_algebraMap_eq' (by rfl)
      have hmul := Module.finrank_mul_finrank F
        (Formalization.Books.Fields.Unit12.generatedIntermediateField S
          (Fin.castSucc (0 : Fin (S'.n + 1))))
        (Formalization.Books.Fields.Unit12.generatedIntermediateField S
          (Fin.succ (0 : Fin (S'.n + 1))))
      have hrank0 : Module.finrank F
          (Formalization.Books.Fields.Unit12.generatedIntermediateField S
            (Fin.castSucc (0 : Fin (S'.n + 1)))) = 1 := by
        rw [h0field, IntermediateField.finrank_bot]
      have hrank1 : Module.finrank F
          (Formalization.Books.Fields.Unit12.generatedIntermediateField S
            (Fin.succ (0 : Fin (S'.n + 1)))) = p := by
        exact h1field.symm ▸ hyr
      rw [hrank0, one_mul, hrank1] at hmul
      exact hmul
  · obtain ⟨y', hy', hyn', hyr'⟩ := hnext j
    have hprev :
        Formalization.Books.Fields.Unit12.generatedIntermediateField S j.succ.castSucc =
          (Formalization.Books.Fields.Unit12.generatedIntermediateField S' j.castSucc).restrictScalars F := by
      simpa using hprefix j.castSucc
    have hnext' :
        Formalization.Books.Fields.Unit12.generatedIntermediateField S j.succ.succ =
          (Formalization.Books.Fields.Unit12.generatedIntermediateField S' j.succ).restrictScalars F := by
      exact hprefix j.succ
    let y : Formalization.Books.Fields.Unit12.generatedIntermediateField S j.succ.castSucc :=
      ⟨(y' : E), by
        rw [hprev]
        exact y'.property⟩
    refine ⟨y, ?_, ?_, ?_⟩
    · apply Subtype.ext
      change (y' : E) = (S'.alpha j) ^ p
      have hval := congrArg Subtype.val hy'
      change (y' : E) = (S'.alpha j) ^ p at hval
      exact hval
    · intro z hz
      have hzmem : (z : E) ∈
          Formalization.Books.Fields.Unit12.generatedIntermediateField S' j.castSucc := by
        have hset :
            (Formalization.Books.Fields.Unit12.generatedIntermediateField S j.succ.castSucc : Set E) =
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S' j.castSucc : Set E) := by
          rw [hprev]
          rfl
        have hzold : (z : E) ∈
            (Formalization.Books.Fields.Unit12.generatedIntermediateField S j.succ.castSucc : Set E) :=
          z.property
        rw [hset] at hzold
        exact hzold
      let z' : Formalization.Books.Fields.Unit12.generatedIntermediateField S' j.castSucc :=
        ⟨(z : E), hzmem⟩
      apply hyn' z'
      apply Subtype.ext
      simpa [y, z'] using congrArg Subtype.val hz
    · let eP :
          Formalization.Books.Fields.Unit12.generatedIntermediateField S j.succ.castSucc ≃+*
            Formalization.Books.Fields.Unit12.generatedIntermediateField S' j.castSucc :=
        (IntermediateField.equivOfEq hprev).toRingEquiv
      let eQ :
          Formalization.Books.Fields.Unit12.generatedIntermediateField S j.succ.succ ≃+*
            Formalization.Books.Fields.Unit12.generatedIntermediateField S' j.succ :=
        (IntermediateField.equivOfEq hnext').toRingEquiv
      have hcomm :
          (algebraMap
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S' j.castSucc)
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S' j.succ)).comp
              eP.toRingHom =
            eQ.toRingHom.comp
              (algebraMap
                (Formalization.Books.Fields.Unit12.generatedIntermediateField S j.succ.castSucc)
                (Formalization.Books.Fields.Unit12.generatedIntermediateField S j.succ.succ)) := by
        ext z
        rfl
      exact (Algebra.finrank_eq_of_equiv_equiv eP eQ hcomm).trans hyr'

private theorem finite_purely_inseparable_has_pth_root_tower_aux
    {F E : Type v} [Field F] [Field E] [Algebra F E]
    {p : ℕ} (hp : p.Prime) [CharP F p]
    [FiniteDimensional F E] [IsPurelyInseparable F E]
    (d : ℕ) (hd : Module.finrank F E = d) :
    ∃ S : Formalization.Books.Fields.Unit12.FinitelyGeneratedFieldExtension F E,
      ∀ i : Fin S.n,
        ∃ y : Formalization.Books.Fields.Unit12.generatedIntermediateField
            S i.castSucc,
          algebraMap
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.castSucc)
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.succ) y =
            (Formalization.Books.Fields.Unit12.generatorInNextField S i) ^ p ∧
          (∀ z : Formalization.Books.Fields.Unit12.generatedIntermediateField S i.castSucc,
            z ^ p ≠ y) ∧
          Module.finrank
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.castSucc)
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.succ) = p := by
  classical
  by_cases htriv : (⊥ : IntermediateField F E) = ⊤
  · let S : Formalization.Books.Fields.Unit12.FinitelyGeneratedFieldExtension F E :=
      { n := 0
        alpha := Fin.elim0
        finite := inferInstance
        generated := by
          simp [htriv] }
    refine ⟨S, ?_⟩
    intro i
    exact Fin.elim0 i
  · obtain ⟨x, -, hxbot⟩ :=
      SetLike.exists_of_lt (lt_of_le_of_ne bot_le htriv)
    have hx : x ∉ (algebraMap F E).range := by
      intro hxrange
      exact hxbot ((IntermediateField.mem_bot).2 hxrange)
    obtain ⟨w, y, hwpow, hyn, hwrank⟩ :=
      purely_inseparable_pth_root_step hp x hx
    letI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
    let L : IntermediateField F E := IntermediateField.adjoin F ({w} : Set E)
    letI : CharP L p := IntermediateField.charP L p
    letI : FiniteDimensional F L := by
      dsimp [L]
      exact IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral w)
    letI : FiniteDimensional L E :=
      Module.Finite.of_restrictScalars_finite F L E
    have hLrank : Module.finrank F L = p := by
      simpa [L] using hwrank
    have hmul : p * Module.finrank L E = d := by
      calc
        p * Module.finrank L E = Module.finrank F L * Module.finrank L E := by
          rw [hLrank]
        _ = Module.finrank F E := Module.finrank_mul_finrank F L E
        _ = d := hd
    have hltmul : Module.finrank L E < p * Module.finrank L E := by
      exact (Nat.lt_mul_iff_one_lt_left Module.finrank_pos).2 hp.one_lt
    have hLd : Module.finrank L E < d := by
      rw [← hmul]
      exact hltmul
    obtain ⟨S', hS'⟩ :=
      finite_purely_inseparable_has_pth_root_tower_aux
        (F := L) (E := E) hp (d := Module.finrank L E) rfl
    apply prepend_pth_root_tower hp w S'
    · refine ⟨y, hwpow.symm, hyn, ?_⟩
      exact hLrank
    · exact hS'
termination_by d
decreasing_by exact hLd

/-- A finite purely inseparable extension admits a tower whose successive steps
    adjoin p-th roots and have degree `p`. -/
theorem finite_purely_inseparable_has_pth_root_tower
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : ℕ} (hp : p.Prime) [CharP F p]
    [FiniteDimensional F E] [IsPurelyInseparable F E] :
    ∃ S : Formalization.Books.Fields.Unit12.FinitelyGeneratedFieldExtension F E,
      ∀ i : Fin S.n,
        ∃ y : Formalization.Books.Fields.Unit12.generatedIntermediateField
            S i.castSucc,
          algebraMap
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.castSucc)
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.succ) y =
            (Formalization.Books.Fields.Unit12.generatorInNextField S i) ^ p ∧
          (∀ z : Formalization.Books.Fields.Unit12.generatedIntermediateField
              S i.castSucc, z ^ p ≠ y) ∧
          Module.finrank
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.castSucc)
              (Formalization.Books.Fields.Unit12.generatedIntermediateField S i.succ) = p := by
  classical
  by_cases htriv : (⊥ : IntermediateField F E) = ⊤
  · let S : Formalization.Books.Fields.Unit12.FinitelyGeneratedFieldExtension F E :=
      { n := 0
        alpha := Fin.elim0
        finite := inferInstance
        generated := by
          simp [htriv] }
    refine ⟨S, ?_⟩
    intro i
    exact Fin.elim0 i
  · obtain ⟨x, -, hxbot⟩ :=
      SetLike.exists_of_lt (lt_of_le_of_ne bot_le htriv)
    have hx : x ∉ (algebraMap F E).range := by
      intro hxrange
      exact hxbot ((IntermediateField.mem_bot).2 hxrange)
    obtain ⟨w, y, hwpow, hyn, hwrank⟩ :=
      purely_inseparable_pth_root_step hp x hx
    letI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
    let L : IntermediateField F E := IntermediateField.adjoin F ({w} : Set E)
    letI : CharP L p := IntermediateField.charP L p
    letI : FiniteDimensional F L := by
      dsimp [L]
      exact IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral w)
    letI : FiniteDimensional L E :=
      Module.Finite.of_restrictScalars_finite F L E
    have hLrank : Module.finrank F L = p := by
      simpa [L] using hwrank
    have hmul : p * Module.finrank L E = Module.finrank F E := by
      calc
        p * Module.finrank L E = Module.finrank F L * Module.finrank L E := by
          rw [hLrank]
        _ = Module.finrank F E := Module.finrank_mul_finrank F L E
    have hltmul : Module.finrank L E < p * Module.finrank L E := by
      exact (Nat.lt_mul_iff_one_lt_left Module.finrank_pos).2 hp.one_lt
    have hLd : Module.finrank L E < Module.finrank F E := by
      rw [← hmul]
      exact hltmul
    obtain ⟨S', hS'⟩ :=
      finite_purely_inseparable_has_pth_root_tower_aux
        (F := L) (E := E) hp (d := Module.finrank L E) rfl
    apply prepend_pth_root_tower hp w S'
    · refine ⟨y, hwpow.symm, hyn, ?_⟩
      exact hLrank
    · exact hS'

/-! ## Separable first and degrees -/

/- `separableClosure F E` is the source's `E_sep`; Mathlib supplies both its
   separability and the purely inseparable top extension, together with the
   uniqueness criterion. -/
/-- Every algebraic field extension is uniquely separable followed by purely
    inseparable. -/
theorem separable_first_then_purely_inseparable_unique
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] :
    ∃! L : IntermediateField F E,
      Algebra.IsSeparable F L ∧ IsPurelyInseparable L E := by
  refine ⟨separableClosure F E, ⟨inferInstance, inferInstance⟩, ?_⟩
  intro L hL
  exact (eq_separableClosure_iff F E L).2 hL

/- The source's two degree definitions are exactly the following canonical
   rank definitions. -/
/-- `Field.sepDegree` and `Field.insepDegree` are the degrees of the two
    successive extensions through `separableClosure`. -/
theorem separable_and_inseparable_degree_definitions
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    Field.sepDegree F E = Module.rank F (separableClosure F E) ∧
      Field.insepDegree F E = Module.rank (separableClosure F E) E :=
  ⟨rfl, rfl⟩

/-- In characteristic zero, the separable degree is the extension degree and
    the inseparable degree is one. -/
theorem characteristic_zero_degree_consequences
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra.IsAlgebraic F E] :
    Field.sepDegree F E = Module.rank F E ∧ Field.insepDegree F E = 1 := by
  let _ : Algebra.IsSeparable F E :=
    Formalization.Books.Fields.Unit12.algebraic_extension_separable_of_char_zero
  exact ⟨Algebra.IsSeparable.sepDegree_eq F E, Algebra.IsSeparable.insepDegree_eq F E⟩

/-- The separable and inseparable degrees multiply to the full degree, also
    for infinite algebraic extensions. -/
theorem extension_degree_factorization
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    Field.sepDegree F E * Field.insepDegree F E = Module.rank F E :=
  Field.sepDegree_mul_insepDegree F E

/-- For a finite extension, the separable degree is the number of embeddings
    into any chosen algebraic closure. -/
theorem finite_extension_separable_degree_eq_embedding_card
    {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [IsAlgClosure F L]
    [FiniteDimensional F K] :
    Field.finSepDegree F K = Nat.card (K →ₐ[F] L) := by
  let _ : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
  let _ : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  exact Field.finSepDegree_eq_of_isAlgClosed F K L

/- The source's final tower law is Mathlib's canonical algebraic tower law for
   both degree notions. -/
/-- Separable and inseparable degrees are multiplicative in an algebraic tower. -/
theorem separable_and_inseparable_degree_multiplicative
    {F E K : Type u} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    [Algebra.IsAlgebraic F E] [Algebra.IsAlgebraic E K] :
    Field.sepDegree F K = Field.sepDegree E K * Field.sepDegree F E ∧
      Field.insepDegree F K = Field.insepDegree E K * Field.insepDegree F E := by
  constructor
  · calc
      Field.sepDegree F K = Field.sepDegree F E * Field.sepDegree E K :=
        (Field.sepDegree_mul_sepDegree_of_isAlgebraic F E K).symm
      _ = Field.sepDegree E K * Field.sepDegree F E := mul_comm _ _
  · calc
      Field.insepDegree F K = Field.insepDegree F E * Field.insepDegree E K :=
        (Field.insepDegree_mul_insepDegree_of_isAlgebraic F E K).symm
      _ = Field.insepDegree E K * Field.insepDegree F E := mul_comm _ _

end

end Formalization.Books.Fields.Unit14
