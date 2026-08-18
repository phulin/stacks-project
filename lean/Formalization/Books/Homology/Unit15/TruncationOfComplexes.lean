import Formalization.Books.Homology.Unit14.HomotopyAndShift
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# Homological Algebra, Chapter 15: Truncation of complexes

The source distinguishes brutal ("stupid") truncations from the canonical
truncations.  Mathlib's `stupidTrunc`, `truncLE`, and `truncGE` are the
canonical categorical constructions used below.  Componentwise equality with
zero is expressed by `IsZero`, and componentwise equality with an original
term is expressed by an isomorphism, since zero objects and categorical
quotients are only determined up to canonical isomorphism.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open ComplexShape

universe v u

namespace Formalization.Books.Homology.Unit15

/-! ## Source-facing categorical presentations -/

/-- A categorical way to say that `X` is a subcomplex of `Y`. -/
def HasMonomorphismInto {D : Type u} [Category.{v} D] (X Y : D) : Prop :=
  ∃ f : X ⟶ Y, Mono f

/-- A categorical way to say that `Y` is a quotient of `X`. -/
def HasEpimorphismOnto {D : Type u} [Category.{v} D] (X Y : D) : Prop :=
  ∃ f : X ⟶ Y, Epi f

/-- A quotient presentation of `Q` by a monomorphism from `X` to `Y`. -/
def HasQuotientPresentation {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    [HasCokernels D]
    (X Y Q : D) : Prop :=
  ∃ f : X ⟶ Y, Mono f ∧ Nonempty (cokernel f ≅ Q)

/-- An epimorphism presentation whose kernel is isomorphic to `K`. -/
def HasEpiKernelPresentation {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    [HasKernels D]
    (X Y K : D) : Prop :=
  ∃ f : X ⟶ Y, Epi f ∧ Nonempty (kernel f ≅ K)

/-- The componentwise content of a brutal truncation at an upper bound. -/
def IsStupidTruncationAtMost {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {c : ComplexShape ℤ} (K T : HomologicalComplex C c) (n : ℤ) : Prop :=
  (∀ i : ℤ, i ≤ n → Nonempty (T.X i ≅ K.X i)) ∧
    (∀ i : ℤ, n < i → IsZero (T.X i))

/-- The componentwise content of a brutal truncation at a lower bound. -/
def IsStupidTruncationAtLeast {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {c : ComplexShape ℤ} (K T : HomologicalComplex C c) (n : ℤ) : Prop :=
  (∀ i : ℤ, n ≤ i → Nonempty (T.X i ≅ K.X i)) ∧
    (∀ i : ℤ, i < n → IsZero (T.X i))

/-! ## Chain complexes -/

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Integer half-line embeddings for the chain shape -/

/-- The embedding of the nonnegative chain ray onto the degrees `≥ n`. -/
def chainGEEmbedding (n : ℤ) :
    (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun k : ℕ => n + k)
    (by
      intro a b h
      change n + (a : ℤ) = n + (b : ℤ) at h
      omega)
    (by
      intro a b
      change (b + 1 = a) ↔
        (n + (b : ℤ)) + 1 = n + (a : ℤ)
      constructor <;> intro h <;> omega)

instance (n : ℤ) : (chainGEEmbedding n).IsRelIff := by
  constructor
  intro a b h
  change (n + (b : ℤ)) + 1 = n + (a : ℤ) at h
  change b + 1 = a
  have h' : (b : ℤ) + 1 = (a : ℤ) := by omega
  exact_mod_cast h'

instance (n : ℤ) : (chainGEEmbedding n).IsTruncLE where
  mem_prev {i' j} h :=
    ⟨j + 1, by
      change n + (j : ℤ) + 1 = i' at h
      change n + ((j + 1 : ℕ) : ℤ) = i'
      omega⟩

/-- The embedding of the nonnegative chain ray onto the degrees `≤ n`. -/
def chainLEEmbedding (n : ℤ) :
    (ComplexShape.up ℕ).Embedding (ComplexShape.down ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun k : ℕ => n - k)
    (by
      intro a b h
      change n - (a : ℤ) = n - (b : ℤ) at h
      omega)
    (by
      intro a b
      change (a + 1 = b) ↔
        (n - (b : ℤ)) + 1 = n - (a : ℤ)
      constructor
      · intro h
        have h' : (a : ℤ) + 1 = (b : ℤ) := by
          exact_mod_cast h
        omega
      · intro h
        have h' : (a : ℤ) + 1 = (b : ℤ) := by
          omega
        exact_mod_cast h')

instance (n : ℤ) : (chainLEEmbedding n).IsRelIff := by
  constructor
  intro a b h
  change (n - (b : ℤ)) + 1 = n - (a : ℤ) at h
  change a + 1 = b
  have h' : (a : ℤ) + 1 = (b : ℤ) := by omega
  exact_mod_cast h'

instance (n : ℤ) : (chainLEEmbedding n).IsTruncGE where
  mem_next {j k'} h :=
    ⟨j + 1, by
      change k' + 1 = n - (j : ℤ) at h
      change n - ((j + 1 : ℕ) : ℤ) = k'
      simp only [Nat.cast_add, Nat.cast_one]
      omega⟩

/-! ### The first numbered item: `σ ≤ n` -/

/-- The degree-concentrated chain complex representing `A[-n]`. -/
noncomputable def degreeConcentrated (A : C) (n : ℤ) : ChainComplex C ℤ :=
  Formalization.Books.Homology.Unit14.ChainComplex.concentrated C A (-n)

/-- The stupid truncation `σ ≤ n` of a chain complex. -/
noncomputable def stupidTruncLE (K : ChainComplex C ℤ) (n : ℤ) :
    ChainComplex C ℤ :=
  HomologicalComplex.stupidTrunc K (chainLEEmbedding n)

private noncomputable def stupidTruncLEι_f (K : ChainComplex C ℤ) (n i : ℤ) :
    (stupidTruncLE K n).X i ⟶ K.X i :=
  by
    classical
    change (HomologicalComplex.stupidTrunc K (chainLEEmbedding n)).X i ⟶ K.X i
    exact dite (∃ k, (chainLEEmbedding n).f k = i)
      (fun hi => (K.stupidTruncXIso (chainLEEmbedding n) hi.choose_spec).hom)
      (fun _ => 0)

private noncomputable def stupidTruncLEι (K : ChainComplex C ℤ) (n : ℤ) :
    stupidTruncLE K n ⟶ K :=
  by
    refine { f := stupidTruncLEι_f K n, comm' := ?_ }
    intro i j hij
    classical
    change stupidTruncLEι_f K n i ≫ K.d i j =
      (HomologicalComplex.stupidTrunc K (chainLEEmbedding n)).d i j ≫
        stupidTruncLEι_f K n j
    by_cases hi : ∃ k, (chainLEEmbedding n).f k = i
    · obtain ⟨k, rfl⟩ := hi
      obtain ⟨l, rfl⟩ := (chainLEEmbedding n).mem_next hij
      have hj : ∃ l : ℕ, (chainLEEmbedding n).f l = (chainLEEmbedding n).f l :=
        ⟨l, rfl⟩
      have hι (t : ℕ) :
          stupidTruncLEι_f K n ((chainLEEmbedding n).f t) =
            (K.stupidTruncXIso (chainLEEmbedding n) (rfl :
              (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).hom := by
        dsimp [stupidTruncLEι_f, stupidTruncLE]
        split
        · rename_i h
          have hp : (chainLEEmbedding n).f h.choose =
              (chainLEEmbedding n).f t := h.choose_spec
          change
            (K.stupidTruncXIso (chainLEEmbedding n) hp).hom =
              (K.stupidTruncXIso (chainLEEmbedding n) (rfl :
                (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).hom
          have hst : h.choose = t := by
            dsimp [chainLEEmbedding, ComplexShape.Embedding.mk'] at hp ⊢
            omega
          simp only [hst]
        · rename_i h
          exact (h ⟨t, rfl⟩).elim
      rw [hι k, hι l]
      dsimp [stupidTruncLEι_f, stupidTruncLE]
      have hd (a b : ℕ) :
          (HomologicalComplex.stupidTrunc K (chainLEEmbedding n)).d
              ((chainLEEmbedding n).f a) ((chainLEEmbedding n).f b) =
            (K.stupidTruncXIso (chainLEEmbedding n) (rfl :
              (chainLEEmbedding n).f a = (chainLEEmbedding n).f a)).hom ≫
              K.d ((chainLEEmbedding n).f a) ((chainLEEmbedding n).f b) ≫
              (K.stupidTruncXIso (chainLEEmbedding n) (rfl :
                (chainLEEmbedding n).f b = (chainLEEmbedding n).f b)).inv := by
        change ((K.restriction (chainLEEmbedding n)).extend
          (chainLEEmbedding n)).d ((chainLEEmbedding n).f a)
            ((chainLEEmbedding n).f b) = _
        dsimp [HomologicalComplex.stupidTrunc] at *
        rw [HomologicalComplex.extend_d_eq
          (K.restriction (chainLEEmbedding n)) (chainLEEmbedding n) rfl rfl,
          HomologicalComplex.restriction_d_eq K (chainLEEmbedding n) rfl rfl]
        have hstupid (t : ℕ) :
            (K.stupidTruncXIso (chainLEEmbedding n) (rfl :
              (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).hom =
              ((K.restriction (chainLEEmbedding n)).extendXIso
                (chainLEEmbedding n) (rfl :
                  (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).hom ≫
                (K.restrictionXIso (chainLEEmbedding n) (rfl :
                  (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).hom := by
          dsimp [HomologicalComplex.stupidTruncXIso, Iso.trans_hom,
            HomologicalComplex.restrictionXIso,
            HomologicalComplex.extendXIso, CategoryTheory.eqToIso]
          rfl
        have hstupid_inv (t : ℕ) :
            (K.stupidTruncXIso (chainLEEmbedding n) (rfl :
              (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).inv =
              (K.restrictionXIso (chainLEEmbedding n) (rfl :
                (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).inv ≫
                ((K.restriction (chainLEEmbedding n)).extendXIso
                  (chainLEEmbedding n) (rfl :
                    (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).inv := by
          dsimp [HomologicalComplex.stupidTruncXIso, Iso.trans_inv,
            HomologicalComplex.restrictionXIso,
            HomologicalComplex.extendXIso, CategoryTheory.eqToIso]
          rfl
        rw [hstupid a, hstupid_inv b]
        simpa only [Category.assoc]
      rw [hd k l]
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · have hz := HomologicalComplex.isZero_stupidTrunc_X K
        (chainLEEmbedding n) i (by
          intro k hk
          exact hi ⟨k, hk⟩)
      dsimp [stupidTruncLEι_f]
      dsimp [stupidTruncLE] at *
      simp only [dif_neg hi]
      exact hz.eq_of_src _ _

theorem stupidTruncLE_components (K : ChainComplex C ℤ) (n : ℤ) :
    IsStupidTruncationAtMost K (stupidTruncLE K n) n := by
  constructor
  · intro i hi
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (chainLEEmbedding n).f k = i := by
      refine ⟨Int.toNat (n - i), ?_⟩
      dsimp [chainLEEmbedding, ComplexShape.Embedding.mk']
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ n - i)]
      omega
    exact ⟨HomologicalComplex.stupidTruncXIso K (chainLEEmbedding n) hk⟩
  · intro i hi
    apply HomologicalComplex.isZero_stupidTrunc_X K (chainLEEmbedding n) i
    intro k hk
    dsimp [chainLEEmbedding, ComplexShape.Embedding.mk'] at hk
    omega

theorem stupidTruncLE_is_subcomplex (K : ChainComplex C ℤ) (n : ℤ) :
    HasMonomorphismInto (stupidTruncLE K n) K := by
  classical
  refine ⟨stupidTruncLEι K n, ?_⟩
  apply HomologicalComplex.mono_of_mono_f
  intro i
  dsimp [stupidTruncLEι]
  by_cases hi : ∃ k, (chainLEEmbedding n).f k = i
  · change Mono (stupidTruncLEι_f K n i)
    dsimp [stupidTruncLEι_f, stupidTruncLE]
    rw [dif_pos hi]
    infer_instance
  · change Mono (stupidTruncLEι_f K n i)
    dsimp [stupidTruncLEι_f, stupidTruncLE]
    rw [dif_neg hi]
    apply (HomologicalComplex.isZero_stupidTrunc_X K (chainLEEmbedding n) i
      (by
        intro k hk
        exact hi ⟨k, hk⟩)).mono

private lemma chainLEEmbedding_succ_eq (n i : ℤ) (k : ℕ)
    (hk : (chainLEEmbedding (n - 1)).f k = i) :
    (chainLEEmbedding n).f (k + 1) = i := by
  dsimp [chainLEEmbedding, ComplexShape.Embedding.mk'] at hk ⊢
  omega

private lemma chainLEEmbedding_zero (n : ℤ) :
    (chainLEEmbedding n).f 0 = n := by
  dsimp [chainLEEmbedding, ComplexShape.Embedding.mk']
  omega

private noncomputable def stupidTruncLEStep_f (K : ChainComplex C ℤ) (n i : ℤ) :
    (stupidTruncLE K (n - 1)).X i ⟶ (stupidTruncLE K n).X i :=
  by
    classical
    change (HomologicalComplex.stupidTrunc K (chainLEEmbedding (n - 1))).X i ⟶
      (HomologicalComplex.stupidTrunc K (chainLEEmbedding n)).X i
    exact dite (∃ k, (chainLEEmbedding (n - 1)).f k = i)
      (fun hi =>
        (K.stupidTruncXIso (chainLEEmbedding (n - 1)) hi.choose_spec).hom ≫
          (K.stupidTruncXIso (chainLEEmbedding n)
            (chainLEEmbedding_succ_eq n i hi.choose hi.choose_spec)).inv)
      (fun _ => 0)

private noncomputable def stupidTruncLEStep (K : ChainComplex C ℤ) (n : ℤ) :
    stupidTruncLE K (n - 1) ⟶ stupidTruncLE K n :=
  by
    refine { f := stupidTruncLEStep_f K n, comm' := ?_ }
    intro i j hij
    classical
    change stupidTruncLEStep_f K n i ≫
        (HomologicalComplex.stupidTrunc K (chainLEEmbedding n)).d i j =
      (HomologicalComplex.stupidTrunc K (chainLEEmbedding (n - 1))).d i j ≫
        stupidTruncLEStep_f K n j
    dsimp [stupidTruncLEStep_f]
    dsimp [stupidTruncLE]
    by_cases hi : ∃ k, (chainLEEmbedding (n - 1)).f k = i
    · obtain ⟨k, rfl⟩ := hi
      have hij' : (down ℤ).Rel ((chainLEEmbedding (n - 1)).f k) j := hij
      obtain ⟨l, rfl⟩ := (chainLEEmbedding (n - 1)).mem_next hij'
      have hj : ∃ t : ℕ,
          (chainLEEmbedding (n - 1)).f t = (chainLEEmbedding (n - 1)).f l :=
        ⟨l, rfl⟩
      have hkpos : ∃ t : ℕ,
          (chainLEEmbedding (n - 1)).f t = (chainLEEmbedding (n - 1)).f k :=
        ⟨k, rfl⟩
      have htest :
          (K.stupidTruncXIso (chainLEEmbedding (n - 1)) hkpos.choose_spec).hom =
            ((K.restriction (chainLEEmbedding (n - 1))).extendXIso
              (chainLEEmbedding (n - 1)) hkpos.choose_spec).hom ≫
              (K.restrictionXIso (chainLEEmbedding (n - 1)) hkpos.choose_spec).hom := by
        dsimp [HomologicalComplex.stupidTruncXIso, Iso.trans_hom,
          HomologicalComplex.restrictionXIso,
          HomologicalComplex.extendXIso, CategoryTheory.eqToIso]
        rfl
      have htest₂ :
          (K.stupidTruncXIso (chainLEEmbedding n)
            (chainLEEmbedding_succ_eq n ((chainLEEmbedding (n - 1)).f k)
              hkpos.choose hkpos.choose_spec)).inv =
            (K.restrictionXIso (chainLEEmbedding n)
              (chainLEEmbedding_succ_eq n ((chainLEEmbedding (n - 1)).f k)
                hkpos.choose hkpos.choose_spec)).inv ≫
              ((K.restriction (chainLEEmbedding n)).extendXIso
                (chainLEEmbedding n)
                (chainLEEmbedding_succ_eq n ((chainLEEmbedding (n - 1)).f k)
                  hkpos.choose hkpos.choose_spec)).inv := by
        dsimp [HomologicalComplex.stupidTruncXIso, Iso.trans_inv,
          HomologicalComplex.restrictionXIso,
          HomologicalComplex.extendXIso, CategoryTheory.eqToIso]
        rfl
      have htest_j :
          (K.stupidTruncXIso (chainLEEmbedding (n - 1)) hj.choose_spec).hom =
            ((K.restriction (chainLEEmbedding (n - 1))).extendXIso
              (chainLEEmbedding (n - 1)) hj.choose_spec).hom ≫
              (K.restrictionXIso (chainLEEmbedding (n - 1)) hj.choose_spec).hom := by
        dsimp [HomologicalComplex.stupidTruncXIso, Iso.trans_hom,
          HomologicalComplex.restrictionXIso,
          HomologicalComplex.extendXIso, CategoryTheory.eqToIso]
        rfl
      have htest₂_j :
          (K.stupidTruncXIso (chainLEEmbedding n)
            (chainLEEmbedding_succ_eq n ((chainLEEmbedding (n - 1)).f l)
              hj.choose hj.choose_spec)).inv =
            (K.restrictionXIso (chainLEEmbedding n)
              (chainLEEmbedding_succ_eq n ((chainLEEmbedding (n - 1)).f l)
                hj.choose hj.choose_spec)).inv ≫
              ((K.restriction (chainLEEmbedding n)).extendXIso
                (chainLEEmbedding n)
                (chainLEEmbedding_succ_eq n ((chainLEEmbedding (n - 1)).f l)
                  hj.choose hj.choose_spec)).inv := by
        dsimp [HomologicalComplex.stupidTruncXIso, Iso.trans_inv,
          HomologicalComplex.restrictionXIso,
          HomologicalComplex.extendXIso, CategoryTheory.eqToIso]
        rfl
      simp only [dif_pos hkpos, dif_pos hj]
      simp only [htest, htest₂, htest_j, htest₂_j]
      change _ ≫
          ((K.restriction (chainLEEmbedding n)).extend (chainLEEmbedding n)).d
            ((chainLEEmbedding (n - 1)).f k)
            ((chainLEEmbedding (n - 1)).f l) =
        ((K.restriction (chainLEEmbedding (n - 1))).extend
          (chainLEEmbedding (n - 1))).d ((chainLEEmbedding (n - 1)).f k)
            ((chainLEEmbedding (n - 1)).f l) ≫ _
      rw [HomologicalComplex.extend_d_eq
        (K.restriction (chainLEEmbedding (n - 1))) (chainLEEmbedding (n - 1))
          rfl rfl,
        HomologicalComplex.extend_d_eq
          (K.restriction (chainLEEmbedding n)) (chainLEEmbedding n)
            (chainLEEmbedding_succ_eq n ((chainLEEmbedding (n - 1)).f k) k rfl)
            (chainLEEmbedding_succ_eq n ((chainLEEmbedding (n - 1)).f l) l rfl)]
      rw [HomologicalComplex.restriction_d_eq K (chainLEEmbedding (n - 1)) rfl rfl,
        HomologicalComplex.restriction_d_eq K (chainLEEmbedding n)
          (chainLEEmbedding_succ_eq n ((chainLEEmbedding (n - 1)).f k) k rfl)
          (chainLEEmbedding_succ_eq n ((chainLEEmbedding (n - 1)).f l) l rfl)]
      have hstupid₁ (t : ℕ) :
          (K.stupidTruncXIso (chainLEEmbedding (n - 1)) (rfl :
            (chainLEEmbedding (n - 1)).f t = (chainLEEmbedding (n - 1)).f t)).hom =
            ((K.restriction (chainLEEmbedding (n - 1))).extendXIso
              (chainLEEmbedding (n - 1)) (rfl :
                (chainLEEmbedding (n - 1)).f t = (chainLEEmbedding (n - 1)).f t)).hom ≫
              (K.restrictionXIso (chainLEEmbedding (n - 1)) (rfl :
                (chainLEEmbedding (n - 1)).f t = (chainLEEmbedding (n - 1)).f t)).hom := by
        dsimp [HomologicalComplex.stupidTruncXIso, Iso.trans_hom,
          HomologicalComplex.restrictionXIso,
          HomologicalComplex.extendXIso, CategoryTheory.eqToIso]
        rfl
      have hstupid₁_inv (t : ℕ) :
          (K.stupidTruncXIso (chainLEEmbedding (n - 1)) (rfl :
            (chainLEEmbedding (n - 1)).f t = (chainLEEmbedding (n - 1)).f t)).inv =
            (K.restrictionXIso (chainLEEmbedding (n - 1)) (rfl :
              (chainLEEmbedding (n - 1)).f t = (chainLEEmbedding (n - 1)).f t)).inv ≫
              ((K.restriction (chainLEEmbedding (n - 1))).extendXIso
                (chainLEEmbedding (n - 1)) (rfl :
                  (chainLEEmbedding (n - 1)).f t = (chainLEEmbedding (n - 1)).f t)).inv := by
        dsimp [HomologicalComplex.stupidTruncXIso, Iso.trans_inv,
          HomologicalComplex.restrictionXIso,
          HomologicalComplex.extendXIso, CategoryTheory.eqToIso]
        rfl
      have hstupid₂ (t : ℕ) :
          (K.stupidTruncXIso (chainLEEmbedding n) (rfl :
            (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).hom =
            ((K.restriction (chainLEEmbedding n)).extendXIso
              (chainLEEmbedding n) (rfl :
                (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).hom ≫
              (K.restrictionXIso (chainLEEmbedding n) (rfl :
                (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).hom := by
        dsimp [HomologicalComplex.stupidTruncXIso, Iso.trans_hom,
          HomologicalComplex.restrictionXIso,
          HomologicalComplex.extendXIso, CategoryTheory.eqToIso]
        rfl
      have hstupid₂_inv (t : ℕ) :
          (K.stupidTruncXIso (chainLEEmbedding n) (rfl :
            (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).inv =
            (K.restrictionXIso (chainLEEmbedding n) (rfl :
              (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).inv ≫
              ((K.restriction (chainLEEmbedding n)).extendXIso
                (chainLEEmbedding n) (rfl :
                  (chainLEEmbedding n).f t = (chainLEEmbedding n).f t)).inv := by
        dsimp [HomologicalComplex.stupidTruncXIso, Iso.trans_inv,
          HomologicalComplex.restrictionXIso,
          HomologicalComplex.extendXIso, CategoryTheory.eqToIso]
        rfl
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
        Category.comp_id]
    · have hz := HomologicalComplex.isZero_stupidTrunc_X K
        (chainLEEmbedding (n - 1)) i (by
          intro k hk
          exact hi ⟨k, hk⟩)
      simp only [dif_neg hi]
      exact hz.eq_of_src _ _

private noncomputable def degreeConcentratedAtIso (A : C) (n : ℤ) :
    (degreeConcentrated A n).X n ≅ A :=
  eqToIso (by
    simpa [degreeConcentrated] using
      (Formalization.Books.Homology.Unit14.ChainComplex.concentrated_at A (-n)))

private noncomputable def stupidTruncLEπ_f (K : ChainComplex C ℤ) (n i : ℤ) :
    (stupidTruncLE K n).X i ⟶ (degreeConcentrated (K.X n) n).X i :=
  by
    classical
    change (HomologicalComplex.stupidTrunc K (chainLEEmbedding n)).X i ⟶
      (degreeConcentrated (K.X n) n).X i
    exact dite (i = n)
      (fun hi => by
        simpa [hi] using
          ((K.stupidTruncXIso (chainLEEmbedding n)
            (by simpa [hi] using chainLEEmbedding_zero n)).hom ≫
            (degreeConcentratedAtIso (K.X n) n).inv))
      (fun _ => 0)

private noncomputable def stupidTruncLEπ (K : ChainComplex C ℤ) (n : ℤ) :
    stupidTruncLE K n ⟶ degreeConcentrated (K.X n) n :=
  by
    refine { f := stupidTruncLEπ_f K n, comm' := ?_ }
    intro i j hij
    classical
    change stupidTruncLEπ_f K n i ≫
        (degreeConcentrated (K.X n) n).d i j =
      (HomologicalComplex.stupidTrunc K (chainLEEmbedding n)).d i j ≫
        stupidTruncLEπ_f K n j
    dsimp [stupidTruncLEπ_f]
    dsimp [stupidTruncLE] at *
    by_cases hi : i = n
    · have hj : j ≠ n := by
        intro hj
        have hij' := hij
        rw [hi, hj] at hij'
        simp [ComplexShape.down, ComplexShape.down'] at hij'
      simp only [dif_pos hi, dif_neg hj]
      have hd : (degreeConcentrated (K.X n) n).d i j = 0 := by
        simp [degreeConcentrated, Formalization.Books.Homology.Unit14.ChainComplex.concentrated,
        Formalization.Books.Homology.Unit14.ChainComplex.shiftFunctor,
        Formalization.Books.Homology.Unit13.chainComplexSingle, hi, hj] <;> rfl
      rw [hd]
      simp
    · simp only [dif_neg hi]
      by_cases hj : j = n
      · have hni : n < i := by
          have hij' := hij
          rw [hj] at hij'
          simp [ComplexShape.down, ComplexShape.down'] at hij'
          omega
        have hz := HomologicalComplex.isZero_stupidTrunc_X K
            (chainLEEmbedding n) i (by
              intro k hk
              dsimp [chainLEEmbedding, ComplexShape.Embedding.mk'] at hk
              omega)
        simp only [dif_pos hj]
        exact hz.eq_of_src _ _
      · simp only [dif_neg hj]
        simp

private lemma mono_iso_inv {X Y : C} (e : X ≅ Y) : Mono e.inv := by
  constructor
  intro Z g h w
  simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using
    congrArg (fun t => t ≫ e.hom) w

private lemma mono_iso_hom {X Y : C} (e : X ≅ Y) : Mono e.hom := by
  constructor
  intro Z g h w
  simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using
    congrArg (fun t => t ≫ e.inv) w

private lemma epi_iso_inv {X Y : C} (e : X ≅ Y) : Epi e.inv := by
  constructor
  intro Z g h w
  simpa only [Category.assoc, e.hom_inv_id_assoc] using
    congrArg (fun t => e.hom ≫ t) w

private lemma epi_iso_hom {X Y : C} (e : X ≅ Y) : Epi e.hom := by
  constructor
  intro Z g h w
  simpa only [Category.assoc, e.inv_hom_id_assoc] using
    congrArg (fun t => e.inv ≫ t) w

/-- The source's quotient identity for successive lower brutal truncations. -/
theorem stupidTruncLE_quotient (K : ChainComplex C ℤ) (n : ℤ) :
    HasQuotientPresentation (stupidTruncLE K (n - 1)) (stupidTruncLE K n)
      (degreeConcentrated (K.X n) n) := by
  classical
  let f := stupidTruncLEStep K n
  let p := stupidTruncLEπ K n
  dsimp [stupidTruncLE] at *
  have hzero : f ≫ p = 0 := by
    ext i
    by_cases hi : i = n
    · subst i
      have hz := HomologicalComplex.isZero_stupidTrunc_X K
          (chainLEEmbedding (n - 1)) n (by
            intro k hk
            dsimp [chainLEEmbedding, ComplexShape.Embedding.mk'] at hk
            omega)
      exact hz.eq_of_src _ _
    · change stupidTruncLEStep_f K n i ≫ stupidTruncLEπ_f K n i = 0
      unfold stupidTruncLEπ_f
      rw [dif_neg hi]
      exact comp_zero
  let S : ShortComplex (ChainComplex C ℤ) := ShortComplex.mk f p hzero
  have hS : S.Exact := by
    apply HomologicalComplex.exact_of_degreewise_exact S
    intro i
    have hzero_i : f.f i ≫ p.f i = 0 := by
      simpa using congrArg (fun q => q.f i) hzero
    change (ShortComplex.mk (f.f i) (p.f i) hzero_i).Exact
    by_cases hi : i < n
    · have hfi : ∃ k, (chainLEEmbedding (n - 1)).f k = i := by
        refine ⟨Int.toNat (n - 1 - i), ?_⟩
        dsimp [chainLEEmbedding, ComplexShape.Embedding.mk']
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ n - 1 - i)]
        omega
      apply (ShortComplex.exact_iff_epi _ (by
        change stupidTruncLEπ_f K n i = 0
        unfold stupidTruncLEπ_f
        rw [dif_neg (by omega : i ≠ n)]
        rfl )).2
      change Epi (stupidTruncLEStep_f K n i)
      unfold stupidTruncLEStep_f
      rw [dif_pos hfi]
      change Epi (_ ≫ _)
      exact epi_comp' (epi_iso_hom _) (epi_iso_inv _)
    · by_cases hin : i = n
      · subst i
        have hfi : (f.f n) = 0 := by
          change stupidTruncLEStep_f K n n = 0
          unfold stupidTruncLEStep_f
          have hnot : ¬ ∃ k, (chainLEEmbedding (n - 1)).f k = n := by
            intro h
            obtain ⟨k, hk⟩ := h
            dsimp [chainLEEmbedding, ComplexShape.Embedding.mk'] at hk
            omega
          rw [dif_neg hnot]
          rfl
        apply (ShortComplex.exact_iff_mono _ hfi).2
        change Mono (stupidTruncLEπ_f K n n)
        unfold stupidTruncLEπ_f
        rw [dif_pos rfl]
        change Mono (_ ≫ _)
        exact mono_comp' (mono_iso_hom _) (mono_iso_inv _)
      · have hz : IsZero ((stupidTruncLE K n).X i) := by
          apply HomologicalComplex.isZero_stupidTrunc_X K (chainLEEmbedding n) i
          intro k hk
          dsimp [chainLEEmbedding, ComplexShape.Embedding.mk'] at hk
          omega
        exact ShortComplex.exact_of_isZero_X₂ _ hz
  have hp : Epi p := by
    apply HomologicalComplex.epi_of_epi_f
    intro i
    by_cases hi : i = n
    · subst i
      change Epi (stupidTruncLEπ_f K n n)
      unfold stupidTruncLEπ_f
      rw [dif_pos rfl]
      change Epi (_ ≫ _)
      exact epi_comp' (epi_iso_hom _) (epi_iso_inv _)
    · dsimp [p, stupidTruncLEπ, stupidTruncLEπ_f]
      change Epi (stupidTruncLEπ_f K n i)
      unfold stupidTruncLEπ_f
      rw [dif_neg hi]
      change Epi (0 : _ ⟶ _)
      apply (Formalization.Books.Homology.Unit14.ChainComplex.concentrated_isZero
        (K.X n) (-n) i (by simp [degreeConcentrated]; omega)).epi
  have hf : Mono f := by
    apply HomologicalComplex.mono_of_mono_f
    intro i
    change Mono (stupidTruncLEStep_f K n i)
    unfold stupidTruncLEStep_f
    by_cases hi : ∃ k, (chainLEEmbedding (n - 1)).f k = i
    · rw [dif_pos hi]
      change Mono (_ ≫ _)
      exact mono_comp' (mono_iso_hom _) (mono_iso_inv _)
    · rw [dif_neg hi]
      change Mono (0 :
        (HomologicalComplex.stupidTrunc K (chainLEEmbedding (n - 1))).X i ⟶
          (HomologicalComplex.stupidTrunc K (chainLEEmbedding n)).X i)
      exact (HomologicalComplex.isZero_stupidTrunc_X K
        (chainLEEmbedding (n - 1)) i (by
          intro k hk
          exact hi ⟨k, hk⟩)).mono
        (0 : (HomologicalComplex.stupidTrunc K (chainLEEmbedding (n - 1))).X i ⟶
          (HomologicalComplex.stupidTrunc K (chainLEEmbedding n)).X i)
  refine ⟨f, hf, ?_⟩
  exact ⟨IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel f) hS.gIsCokernel⟩

/-! ### The second numbered item: `σ ≥ n` -/

/-- The stupid truncation `σ ≥ n` of a chain complex. -/
noncomputable def stupidTruncGE (K : ChainComplex C ℤ) (n : ℤ) :
    ChainComplex C ℤ :=
  HomologicalComplex.stupidTrunc K (chainGEEmbedding n)

theorem stupidTruncGE_components (K : ChainComplex C ℤ) (n : ℤ) :
    IsStupidTruncationAtLeast K (stupidTruncGE K n) n := by
  constructor
  · intro i hi
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (chainGEEmbedding n).f k = i := by
      refine ⟨Int.toNat (i - n), ?_⟩
      dsimp [chainGEEmbedding, ComplexShape.Embedding.mk']
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ i - n)]
      omega
    exact ⟨HomologicalComplex.stupidTruncXIso K (chainGEEmbedding n) hk⟩
  · intro i hi
    apply HomologicalComplex.isZero_stupidTrunc_X K (chainGEEmbedding n) i
    intro k hk
    dsimp [chainGEEmbedding, ComplexShape.Embedding.mk'] at hk
    omega

theorem stupidTruncGE_is_quotient (K : ChainComplex C ℤ) (n : ℤ) :
    HasEpimorphismOnto K (stupidTruncGE K n) := by
  sorry

/-- The successive lower brutal truncation map is an epimorphism with the
degree-`n` complex as its kernel. -/
theorem stupidTruncGE_transition (K : ChainComplex C ℤ) (n : ℤ) :
    HasEpiKernelPresentation (stupidTruncGE K n) (stupidTruncGE K (n + 1))
      (degreeConcentrated (K.X n) n) := by
  sorry

/-! ### The third numbered item: canonical `τ ≥ n` -/

/-- The canonical truncation `τ ≥ n` of a chain complex.  Mathlib's
`truncLE` uses the cycle object at the boundary degree. -/
noncomputable def canonicalTruncGE (K : ChainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : ChainComplex C ℤ :=
  HomologicalComplex.truncLE K (chainGEEmbedding n)

/-- The canonical map `τ ≥ n K ⟶ K`. -/
noncomputable def canonicalTruncGEι (K : ChainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : canonicalTruncGE K n ⟶ K :=
  HomologicalComplex.ιTruncLE K (chainGEEmbedding n)

theorem canonicalTruncGE_boundary (K : ChainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] :
    Nonempty ((canonicalTruncGE K n).X n ≅ K.cycles n) := by
  sorry

theorem canonicalTruncGE_homology_above (K : ChainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : n ≤ i) :
    QuasiIsoAt (canonicalTruncGEι K n) i := by
  sorry

theorem canonicalTruncGE_homology_below (K : ChainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : i < n) :
    IsZero ((canonicalTruncGE K n).homology i) := by
  sorry

/-! ### The fourth numbered item: canonical `τ ≤ n` -/

/-- The canonical truncation `τ ≤ n` of a chain complex.  Mathlib's
`truncGE` uses the opcycle (cokernel) object at the boundary degree. -/
noncomputable def canonicalTruncLE (K : ChainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : ChainComplex C ℤ :=
  HomologicalComplex.truncGE K (chainLEEmbedding n)

/-- The canonical map `K ⟶ τ ≤ n K`. -/
noncomputable def canonicalTruncLEπ (K : ChainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : K ⟶ canonicalTruncLE K n :=
  HomologicalComplex.πTruncGE K (chainLEEmbedding n)

theorem canonicalTruncLE_boundary (K : ChainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] :
    Nonempty ((canonicalTruncLE K n).X n ≅ K.opcycles n) := by
  sorry

theorem canonicalTruncLE_homology_below (K : ChainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : i ≤ n) :
    QuasiIsoAt (canonicalTruncLEπ K n) i := by
  sorry

theorem canonicalTruncLE_homology_above (K : ChainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : n < i) :
    IsZero ((canonicalTruncLE K n).homology i) := by
  sorry

end ChainComplex

/-! ## Cochain complexes -/

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### The first numbered item: `σ ≥ n` -/

/-- The degree-concentrated cochain complex representing `A[-n]`. -/
noncomputable def degreeConcentrated (A : C) (n : ℤ) : CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit14.CochainComplex.concentrated C A (-n)

/-- The stupid truncation `σ ≥ n` of a cochain complex. -/
noncomputable def stupidTruncGE (K : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex C ℤ :=
  HomologicalComplex.stupidTrunc K (ComplexShape.embeddingUpIntGE n)

theorem stupidTruncGE_components (K : CochainComplex C ℤ) (n : ℤ) :
    IsStupidTruncationAtLeast K (stupidTruncGE K n) n := by
  sorry

theorem stupidTruncGE_is_subcomplex (K : CochainComplex C ℤ) (n : ℤ) :
    HasMonomorphismInto (stupidTruncGE K n) K := by
  sorry

/-- The source's quotient identity for successive upper brutal truncations. -/
theorem stupidTruncGE_quotient (K : CochainComplex C ℤ) (n : ℤ) :
    HasQuotientPresentation (stupidTruncGE K (n + 1)) (stupidTruncGE K n)
      (degreeConcentrated (K.X n) n) := by
  sorry

/-! ### The second numbered item: `σ ≤ n` -/

/-- The stupid truncation `σ ≤ n` of a cochain complex. -/
noncomputable def stupidTruncLE (K : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex C ℤ :=
  HomologicalComplex.stupidTrunc K (ComplexShape.embeddingUpIntLE n)

theorem stupidTruncLE_components (K : CochainComplex C ℤ) (n : ℤ) :
    IsStupidTruncationAtMost K (stupidTruncLE K n) n := by
  sorry

theorem stupidTruncLE_is_quotient (K : CochainComplex C ℤ) (n : ℤ) :
    HasEpimorphismOnto K (stupidTruncLE K n) := by
  sorry

/-- The successive upper brutal truncation map is an epimorphism with the
degree-`n` complex as its kernel. -/
theorem stupidTruncLE_transition (K : CochainComplex C ℤ) (n : ℤ) :
    HasEpiKernelPresentation (stupidTruncLE K n) (stupidTruncLE K (n - 1))
      (degreeConcentrated (K.X n) n) := by
  sorry

/-! ### The third numbered item: canonical `τ ≤ n` -/

/-- The canonical truncation `τ ≤ n` of a cochain complex. -/
noncomputable def canonicalTruncLE (K : CochainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : CochainComplex C ℤ :=
  _root_.CochainComplex.truncLE K n

/-- The canonical map `τ ≤ n K ⟶ K`. -/
noncomputable def canonicalTruncLEι (K : CochainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : canonicalTruncLE K n ⟶ K :=
  _root_.CochainComplex.ιTruncLE K n

theorem canonicalTruncLE_boundary (K : CochainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] :
    Nonempty ((canonicalTruncLE K n).X n ≅ K.cycles n) := by
  sorry

theorem canonicalTruncLE_homology_below (K : CochainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : i ≤ n) :
    QuasiIsoAt (canonicalTruncLEι K n) i := by
  sorry

theorem canonicalTruncLE_homology_above (K : CochainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : n < i) :
    IsZero ((canonicalTruncLE K n).homology i) := by
  sorry

/-! ### The fourth numbered item: canonical `τ ≥ n` -/

/-- The canonical truncation `τ ≥ n` of a cochain complex. -/
noncomputable def canonicalTruncGE (K : CochainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : CochainComplex C ℤ :=
  _root_.CochainComplex.truncGE K n

/-- The canonical map `K ⟶ τ ≥ n K`. -/
noncomputable def canonicalTruncGEπ (K : CochainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] : K ⟶ canonicalTruncGE K n :=
  _root_.CochainComplex.πTruncGE K n

theorem canonicalTruncGE_boundary (K : CochainComplex C ℤ) (n : ℤ)
    [∀ i, K.HasHomology i] :
    Nonempty ((canonicalTruncGE K n).X n ≅ K.opcycles n) := by
  sorry

theorem canonicalTruncGE_homology_above (K : CochainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : n ≤ i) :
    QuasiIsoAt (canonicalTruncGEπ K n) i := by
  sorry

theorem canonicalTruncGE_homology_below (K : CochainComplex C ℤ) (n i : ℤ)
    [∀ j, K.HasHomology j] (h : i < n) :
    IsZero ((canonicalTruncGE K n).homology i) := by
  sorry

end CochainComplex

end Formalization.Books.Homology.Unit15
