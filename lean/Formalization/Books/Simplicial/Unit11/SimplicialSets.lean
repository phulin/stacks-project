import Formalization.Books.Simplicial.Unit04.SimplicialPresheaves
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Simplicial Methods, Chapter 11: Simplicial sets

The source's simplicial sets are Mathlib's `SSet`, namely the category of
`Type`-valued presheaves on `SimplexCategory`.  The source's face and
degeneracy maps are the canonical `SimplicialObject.δ` and
`SimplicialObject.σ` families.  A simplex in degree `n` is therefore simply
an element of `U _⦋n⦌`.

Mathlib's `SSet.degenerate` is defined using maps from a lower-dimensional
simplex, and `SSet.degenerate_eq_iUnion_range_σ` identifies it with the
source's one-step degeneracies.  We use that canonical definition rather than
introducing a parallel predicate.
-/

namespace Formalization.Books.Simplicial.Unit11

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open scoped _root_.Simplicial

universe u

/-! ## Terminology and the standard simplex -/

/-
The source's terminology is represented directly by the existing types and
maps: `x : U _⦋n⦌` is an `n`-simplex, `U.δ i x` is its `i`th face, and
`U.σ i x` is its `i`th degeneracy.  The next theorem records the source's
definition of degeneracy in the exact one-step form.
-/

theorem mem_degenerate_iff_exists_degeneracy
    {U : SSet.{u}} {n : ℕ} (x : U _⦋n + 1⦌) :
    x ∈ U.degenerate (n + 1) ↔
      ∃ i : Fin (n + 1), ∃ y : U _⦋n⦌, U.σ i y = x := by
  rw [SSet.degenerate_eq_iUnion_range_σ]
  simp only [Set.mem_iUnion, Set.mem_range]

/-!
`SSet.stdSimplex` is the canonical cosimplicial object whose value at
`[n]` is the source's `Δ[n]`.  Its object equivalence and map formula make
the source's definition by ordered maps explicit.
-/

def standard_simplex_obj_equiv (n m : ℕ) :
    (Δ[n] : SSet.{u}) _⦋m⦌ ≃
      (SimplexCategory.mk m ⟶ SimplexCategory.mk n) :=
  SSet.stdSimplex.objEquiv

theorem standard_simplex_map_obj_equiv_symm
    {n k l : ℕ} (f : SimplexCategory.mk k ⟶ SimplexCategory.mk l)
    (g : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :
    (Δ[n] : SSet.{u}).map f.op (SSet.stdSimplex.objEquiv.symm g) =
      SSet.stdSimplex.objEquiv.symm (f ≫ g) := by
  rfl

/-!
The following two statements are the source's assertions about degeneracies
of `Δ[n]`.  They are consequences of Mathlib's stronger dimension interface,
and the top-dimensional uniqueness statement is already available verbatim.
-/

theorem standard_simplex_all_simplices_degenerate_of_gt
    {n m : ℕ} (h : n < m) (x : (Δ[n] : SSet.{u}) _⦋m⦌) :
    x ∈ (Δ[n] : SSet.{u}).degenerate m := by
  rw [SSet.degenerate_eq_univ_of_hasDimensionLT
    (Δ[n] : SSet.{u}) (n + 1) m (Nat.succ_le_of_lt h)]
  trivial

theorem standard_simplex_nonDegenerate_empty_of_gt
    {n m : ℕ} (h : n < m) :
    (Δ[n] : SSet.{u}).nonDegenerate m = ∅ :=
  SSet.nonDegenerate_eq_empty_of_hasDimensionLT
    (Δ[n] : SSet.{u}) (n + 1) m (Nat.succ_le_of_lt h)

theorem standard_simplex_unique_nonDegenerate_top (n : ℕ) :
    (Δ[n] : SSet.{u}).nonDegenerate n =
      {SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk n))} :=
  SSet.stdSimplex.nonDegenerate_top_dim n

/-! ## Maps out of a standard simplex -/

/-!
The source's canonical bijection is Mathlib's `SSet.yonedaEquiv`.  It sends
a map to its value on the canonical identity simplex, which is the unique
nondegenerate top-dimensional simplex above.
-/

def simplex_map_equiv (U : SSet.{u}) (n : ℕ) :
    (Δ[n] ⟶ U) ≃ U _⦋n⦌ :=
  SSet.yonedaEquiv

theorem simplex_map_equiv_apply (U : SSet.{u}) (n : ℕ)
    (f : Δ[n] ⟶ U) :
    SSet.yonedaEquiv f =
      f.app (op (SimplexCategory.mk n))
        (SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk n))) := by
  rfl

/-! ## The over-category example -/

/-!
The category `Δ/[n]` in the source is Mathlib's `Over [n]`, and its
projection to `Δ` is `Over.forget`.  The fibers are discrete and have the
expected simplex objects.  The category-theoretic content of the displayed
presheaf formula is the Yoneda equivalence `simplex_map_equiv` above.
-/

def simplexOverProjection (n : ℕ) :
    CategoryTheory.Over (SimplexCategory.mk n) ⥤ SimplexCategory :=
  CategoryTheory.Over.forget _

/-! The source's lift of `φ : [k] ⟶ [l]` at `ψ : [l] ⟶ [n]` has domain
`ψ ∘ φ`, which is the following canonical morphism in the over-category. -/

def simplexOverLift {n k l : ℕ}
    (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk l)
    (ψ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :
    CategoryTheory.Over.mk (φ ≫ ψ) ⟶ CategoryTheory.Over.mk ψ :=
  CategoryTheory.Over.homMk φ rfl

theorem simplexOverLift_projection {n k l : ℕ}
    (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk l)
    (ψ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :
    (simplexOverProjection n).map (simplexOverLift φ ψ) = φ := by
  rfl

theorem simplexOverLift_unique {n k l : ℕ}
    (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk l)
    (ψ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :
    ∃! χ : CategoryTheory.Over.mk (φ ≫ ψ) ⟶ CategoryTheory.Over.mk ψ,
      (simplexOverProjection n).map χ = φ := by
  refine ⟨simplexOverLift φ ψ, simplexOverLift_projection φ ψ, ?_⟩
  intro χ hχ
  apply CategoryTheory.Over.OverMorphism.ext
  exact hχ

private theorem simplexOverFiber_object_description_aux (n k : ℕ)
    (x : Functor.Fiber (simplexOverProjection n)
      (SimplexCategory.mk k)) :
    ∃ ψ : SimplexCategory.mk k ⟶ SimplexCategory.mk n,
      x.1 = CategoryTheory.Over.mk ψ := by
  rcases x with ⟨⟨left, right, hom⟩, hx⟩
  change left = SimplexCategory.mk k at hx
  cases hx
  refine ⟨hom, ?_⟩
  rfl

instance simplexOverFiber_isDiscrete (n k : ℕ) :
    IsDiscrete (Functor.Fiber (simplexOverProjection n)
      (SimplexCategory.mk k)) := by
  refine { subsingleton := ?_, eq_of_hom := ?_ }
  · intro X Y
    constructor
    intro f g
    obtain ⟨ψ, hX⟩ := simplexOverFiber_object_description_aux n k X
    obtain ⟨χ, hY⟩ := simplexOverFiber_object_description_aux n k Y
    have hX' : X = (⟨CategoryTheory.Over.mk ψ, by rfl⟩ :
        Functor.Fiber (simplexOverProjection n) (SimplexCategory.mk k)) :=
      Subtype.ext hX
    have hY' : Y = (⟨CategoryTheory.Over.mk χ, by rfl⟩ :
        Functor.Fiber (simplexOverProjection n) (SimplexCategory.mk k)) :=
      Subtype.ext hY
    cases hX'
    cases hY'
    apply Functor.Fiber.hom_ext
    apply CategoryTheory.Over.OverMorphism.ext
    have hf := @CategoryTheory.IsHomLift.fac _ _ _ _
      (simplexOverProjection n) _ _ _ _ (𝟙 (SimplexCategory.mk k)) f.1 f.2
    simp [simplexOverProjection] at hf
    change (𝟙 (SimplexCategory.mk k)) =
      (𝟙 (SimplexCategory.mk k)) ≫ f.1.left at hf
    have hfl : f.1.left = 𝟙 (SimplexCategory.mk k) := by
      simpa using hf.symm
    have hg := @CategoryTheory.IsHomLift.fac _ _ _ _
      (simplexOverProjection n) _ _ _ _ (𝟙 (SimplexCategory.mk k)) g.1 g.2
    simp [simplexOverProjection] at hg
    change (𝟙 (SimplexCategory.mk k)) =
      (𝟙 (SimplexCategory.mk k)) ≫ g.1.left at hg
    have hgl : g.1.left = 𝟙 (SimplexCategory.mk k) := by
      simpa using hg.symm
    exact hfl.trans hgl.symm
  · intro X Y f
    obtain ⟨ψ, hX⟩ := simplexOverFiber_object_description_aux n k X
    obtain ⟨χ, hY⟩ := simplexOverFiber_object_description_aux n k Y
    have hX' : X = (⟨CategoryTheory.Over.mk ψ, by rfl⟩ :
        Functor.Fiber (simplexOverProjection n) (SimplexCategory.mk k)) :=
      Subtype.ext hX
    have hY' : Y = (⟨CategoryTheory.Over.mk χ, by rfl⟩ :
        Functor.Fiber (simplexOverProjection n) (SimplexCategory.mk k)) :=
      Subtype.ext hY
    cases hX'
    cases hY'
    apply Subtype.ext
    congr
    have hf := @CategoryTheory.IsHomLift.fac _ _ _ _
      (simplexOverProjection n) _ _ _ _ (𝟙 (SimplexCategory.mk k)) f.1 f.2
    simp [simplexOverProjection] at hf
    change (𝟙 (SimplexCategory.mk k)) =
      (𝟙 (SimplexCategory.mk k)) ≫ f.1.left at hf
    have hfl : f.1.left = 𝟙 (SimplexCategory.mk k) := by
      simpa using hf.symm
    have hw := CategoryTheory.Over.w f.1
    simpa [hfl] using hw.symm

theorem simplexOverFiber_object_description (n k : ℕ)
    (x : Functor.Fiber (simplexOverProjection n)
      (SimplexCategory.mk k)) :
    ∃ ψ : SimplexCategory.mk k ⟶ SimplexCategory.mk n,
      x.1 = CategoryTheory.Over.mk ψ := by
  exact simplexOverFiber_object_description_aux n k x

theorem simplexOverFiber_objects (n k : ℕ) :
    Nonempty
      (Functor.Fiber (simplexOverProjection n) (SimplexCategory.mk k) ≃
        (Δ[n] : SSet.{u}) _⦋k⦌) := by
  refine ⟨{
    toFun := fun x =>
      SSet.stdSimplex.objEquiv.symm
        (eqToHom x.2.symm ≫ x.1.hom)
    invFun := fun y =>
      (⟨CategoryTheory.Over.mk (SSet.stdSimplex.objEquiv y), by rfl⟩ :
        Functor.Fiber (simplexOverProjection n) (SimplexCategory.mk k))
    left_inv := ?_
    right_inv := ?_ }⟩
  · intro x
    rcases x with ⟨⟨left, right, hom⟩, hx⟩
    change left = SimplexCategory.mk k at hx
    cases hx
    apply Subtype.ext
    simp [simplexOverProjection]
    congr
    have htransport :
        (eqToHom (by rfl) : SimplexCategory.mk k ⟶ SimplexCategory.mk k) =
          𝟙 (SimplexCategory.mk k) := by simp
    simp [htransport]
  · intro y
    simp [simplexOverProjection]
    change SSet.stdSimplex.objEquiv.symm
      ((𝟙 (SimplexCategory.mk k)) ≫ SSet.stdSimplex.objEquiv y) = y
    simp

/-! ## Products -/

/-!
For simplicial sets Mathlib's chosen categorical product is written `⊗`; its
degree-`n` object is the ordinary product `U _⦋n⦌ × V _⦋n⦌`.  This is the
canonical product used for the source's `U × V`.
-/

theorem product_hasDimensionLE
    (U V : SSet.{u}) (a b : ℕ)
    [U.HasDimensionLE a] [V.HasDimensionLE b] :
    (U ⊗ V).HasDimensionLE (a + b) := by
  infer_instance

theorem product_simplex_degenerate_of_gt
    (U V : SSet.{u}) (a b : ℕ)
    [U.HasDimensionLE a] [V.HasDimensionLE b]
    {n : ℕ} (h : a + b < n) (x : (U ⊗ V) _⦋n⦌) :
    x ∈ (U ⊗ V).degenerate n := by
  rw [SSet.degenerate_eq_univ_of_hasDimensionLT
    (U ⊗ V) (a + b + 1) n (Nat.succ_le_of_lt h)]
  trivial

/-! ## Finite bounded subcategories of the category of elements -/

/-!
The category of elements `U.Elements` is the indexing category for the
degreewise compatibility conditions of a simplicial set.  When `U` has
dimension `< d`, the following full subcategory contains a finite initial
part of that category.  The quadratic bound is a convenient uniform bound
for the common-predecessor argument: two monotone maps with codomains of
 length `< d` have a common degeneracy step before degree `d^2`.
-/

abbrev boundedElements (U : SSet.{u}) (d : ℕ) :=
  ObjectProperty.FullSubcategory (C := U.Elements)
    (fun e => e.1.unop.len < d * d + 1)

abbrev boundedElementsInclusion (U : SSet.{u}) (d : ℕ) :
    boundedElements U d ⥤ U.Elements :=
  ObjectProperty.ι (fun e : U.Elements => e.1.unop.len < d * d + 1)

private lemma simplicialSet_sigma_injective
    (U : SSet.{u}) {n : ℕ} (i : Fin (n + 1)) :
    Function.Injective (U.σ i) := by
  intro x y h
  have h' := congrArg (fun z => U.δ (Fin.castSucc i) z) h
  simpa using h'

private lemma common_degeneracy_step
    {A B : SimplexCategory} {k : ℕ}
    (φ : SimplexCategory.mk (k + 1) ⟶ A)
    (ψ : SimplexCategory.mk (k + 1) ⟶ B)
    (h : (A.len + 1) * (B.len + 1) ≤ k) :
    ∃ (i : Fin (k + 1))
      (φ' : SimplexCategory.mk k ⟶ A)
      (ψ' : SimplexCategory.mk k ⟶ B),
      φ = SimplexCategory.σ i ≫ φ' ∧
        ψ = SimplexCategory.σ i ≫ ψ' := by
  have hplateau : ∃ i : Fin (k + 1),
      φ.toOrderHom (Fin.castSucc i) = φ.toOrderHom i.succ ∧
        ψ.toOrderHom (Fin.castSucc i) = ψ.toOrderHom i.succ := by
    by_contra hn
    let code : Fin (k + 2) → Fin ((A.len + 1) * (B.len + 1)) := fun j =>
      ⟨(φ.toOrderHom j).val * (B.len + 1) + (ψ.toOrderHom j).val, by
        have hφ : (φ.toOrderHom j).val ≤ A.len :=
          Nat.le_of_lt_succ (φ.toOrderHom j).isLt
        have hψ : (ψ.toOrderHom j).val ≤ B.len :=
          Nat.le_of_lt_succ (ψ.toOrderHom j).isLt
        have hψlt : (ψ.toOrderHom j).val < B.len + 1 :=
          Nat.lt_succ_of_le hψ
        calc
          (φ.toOrderHom j).val * (B.len + 1) + (ψ.toOrderHom j).val
              < (φ.toOrderHom j).val * (B.len + 1) + (B.len + 1) :=
                Nat.add_lt_add_left hψlt _
          _ = ((φ.toOrderHom j).val + 1) * (B.len + 1) := by
            simp [Nat.add_mul]
          _ ≤ (A.len + 1) * (B.len + 1) := by
            exact Nat.mul_le_mul_right (B.len + 1) (Nat.succ_le_succ hφ)⟩
    have hcode : StrictMono code := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      have hφ := φ.toOrderHom.monotone (Fin.castSucc_le_succ i)
      have hψ := ψ.toOrderHom.monotone (Fin.castSucc_le_succ i)
      have hne : φ.toOrderHom (Fin.castSucc i) ≠ φ.toOrderHom i.succ ∨
          ψ.toOrderHom (Fin.castSucc i) ≠ ψ.toOrderHom i.succ := by
        by_cases hφeq : φ.toOrderHom (Fin.castSucc i) = φ.toOrderHom i.succ
        · by_cases hψeq : ψ.toOrderHom (Fin.castSucc i) = ψ.toOrderHom i.succ
          · exact False.elim (hn ⟨i, hφeq, hψeq⟩)
          · exact Or.inr hψeq
        · exact Or.inl hφeq
      dsimp [code]
      change
        (φ.toOrderHom (Fin.castSucc i)).val * (B.len + 1) +
            (ψ.toOrderHom (Fin.castSucc i)).val <
          (φ.toOrderHom i.succ).val * (B.len + 1) +
            (ψ.toOrderHom i.succ).val
      rcases hne with hφne | hψne
      · have hφlt : φ.toOrderHom (Fin.castSucc i) < φ.toOrderHom i.succ :=
          lt_of_le_of_ne hφ hφne
        have hφlt' : (φ.toOrderHom (Fin.castSucc i)).val <
            (φ.toOrderHom i.succ).val := hφlt
        have hψlt : (ψ.toOrderHom (Fin.castSucc i)).val < B.len + 1 :=
          (ψ.toOrderHom (Fin.castSucc i)).isLt
        calc
          (φ.toOrderHom (Fin.castSucc i)).val * (B.len + 1) +
                (ψ.toOrderHom (Fin.castSucc i)).val <
              (φ.toOrderHom (Fin.castSucc i)).val * (B.len + 1) +
                (B.len + 1) := Nat.add_lt_add_left hψlt _
          _ = ((φ.toOrderHom (Fin.castSucc i)).val + 1) * (B.len + 1) := by
            simp [Nat.add_mul]
          _ ≤ (φ.toOrderHom i.succ).val * (B.len + 1) := by
            exact Nat.mul_le_mul_right (B.len + 1) (Nat.succ_le_of_lt hφlt')
          _ ≤ (φ.toOrderHom i.succ).val * (B.len + 1) +
                (ψ.toOrderHom i.succ).val := by omega
      · have hψlt : ψ.toOrderHom (Fin.castSucc i) < ψ.toOrderHom i.succ :=
          lt_of_le_of_ne hψ hψne
        have hφval : (φ.toOrderHom (Fin.castSucc i)).val ≤
            (φ.toOrderHom i.succ).val := hφ
        have hψval : (ψ.toOrderHom (Fin.castSucc i)).val <
            (ψ.toOrderHom i.succ).val := hψlt
        calc
          (φ.toOrderHom (Fin.castSucc i)).val * (B.len + 1) +
                (ψ.toOrderHom (Fin.castSucc i)).val ≤
              (φ.toOrderHom i.succ).val * (B.len + 1) +
                (ψ.toOrderHom (Fin.castSucc i)).val := by
            exact Nat.add_le_add_right
              (Nat.mul_le_mul_right (B.len + 1) hφval) _
          _ < (φ.toOrderHom i.succ).val * (B.len + 1) +
                (ψ.toOrderHom i.succ).val := Nat.add_lt_add_left hψval _
    have hcard := Fintype.card_le_of_injective code hcode.injective
    have hcard' : k + 2 ≤ (A.len + 1) * (B.len + 1) := by
      simpa using hcard
    omega
  obtain ⟨i, hφ, hψ⟩ := hplateau
  obtain ⟨φ', hφ'⟩ := SimplexCategory.eq_σ_comp_of_not_injective'
    φ i hφ
  obtain ⟨ψ', hψ'⟩ := SimplexCategory.eq_σ_comp_of_not_injective'
    ψ i hψ
  exact ⟨i, φ', ψ', hφ', hψ'⟩

private lemma common_factorization_mk
    (U : SSet.{u}) (d : ℕ) {A B : SimplexCategory} {k : ℕ}
    (φ : SimplexCategory.mk k ⟶ A)
    (ψ : SimplexCategory.mk k ⟶ B)
    (a : U.obj (op A)) (b : U.obj (op B))
    (h : U.map φ.op a = U.map ψ.op b)
    (hA : A.len < d) (hB : B.len < d) :
    ∃ (W : SimplexCategory)
      (s : SimplexCategory.mk k ⟶ W)
      (φ' : W ⟶ A) (ψ' : W ⟶ B),
      W.len < d * d + 1 ∧
        φ = s ≫ φ' ∧ ψ = s ≫ ψ' ∧
          U.map φ'.op a = U.map ψ'.op b := by
  revert φ ψ a b h
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro φ ψ a b h
      by_cases hk : k < d * d + 1
      · exact ⟨SimplexCategory.mk k, 𝟙 _, φ, ψ, by simp [hk], by simp,
          by simp, h⟩
      · have hkpos : 0 < k := by omega
        obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
        have hA' : A.len + 1 ≤ d := Nat.succ_le_of_lt hA
        have hB' : B.len + 1 ≤ d := Nat.succ_le_of_lt hB
        have hprod : (A.len + 1) * (B.len + 1) ≤ d * d :=
          Nat.mul_le_mul hA' hB'
        have hstep : (A.len + 1) * (B.len + 1) ≤ r := by omega
        obtain ⟨i, φ₁, ψ₁, hφ, hψ⟩ :=
          common_degeneracy_step φ ψ hstep
        have h' : U.map φ₁.op a = U.map ψ₁.op b := by
          apply (simplicialSet_sigma_injective U i)
          change U.map (SimplexCategory.σ i).op
              (U.map φ₁.op a) =
            U.map (SimplexCategory.σ i).op
              (U.map ψ₁.op b)
          simpa [hφ, hψ, op_comp, Functor.map_comp, comp_apply] using h
        obtain ⟨W, s, φ', ψ', hW, hφ', hψ', hab⟩ :=
          ih r (by omega) φ₁ ψ₁ a b h'
        refine ⟨W, SimplexCategory.σ i ≫ s, φ', ψ', hW, ?_, ?_, hab⟩
        · rw [hφ, hφ', Category.assoc]
        · rw [hψ, hψ', Category.assoc]

private lemma common_factorization
    (U : SSet.{u}) (d : ℕ) {A B Z : SimplexCategory}
    (φ : Z ⟶ A) (ψ : Z ⟶ B)
    (a : U.obj (op A)) (b : U.obj (op B))
    (h : U.map φ.op a = U.map ψ.op b)
    (hA : A.len < d) (hB : B.len < d) :
    ∃ (W : SimplexCategory)
      (s : Z ⟶ W) (φ' : W ⟶ A) (ψ' : W ⟶ B),
      W.len < d * d + 1 ∧
        φ = s ≫ φ' ∧ ψ = s ≫ ψ' ∧
          U.map φ'.op a = U.map ψ'.op b := by
  simpa only [SimplexCategory.mk_len] using
    (common_factorization_mk U d φ ψ a b h hA hB)

private lemma boundedElements_costructured_nonempty
    (U : SSet.{u}) (d : ℕ) [U.HasDimensionLT d]
    (x : U.Elements) :
    Nonempty (CostructuredArrow (boundedElementsInclusion U d) x) := by
  rcases x with ⟨⟨Z⟩, x⟩
  have hx := SSet.exists_nonDegenerate (X := U) (n := Z.len) x
  obtain ⟨m, f, hf, y, hy⟩ := hx
  have hm : m < d := U.dim_lt_of_nonDegenerate y d
  have hd : 0 < d := by omega
  have hm' : m < d * d + 1 := by
    exact hm.trans (Nat.lt_succ_of_le (Nat.le_mul_of_pos_left d hd))
  let c : boundedElements U d :=
    ⟨⟨op (SimplexCategory.mk m), y.1⟩, hm'⟩
  let q : (boundedElementsInclusion U d).obj c ⟶ ⟨op Z, x⟩ :=
    CategoryOfElements.homMk
      ((boundedElementsInclusion U d).obj c) ⟨op Z, x⟩ f.op hy.symm
  exact ⟨CostructuredArrow.mk q⟩

private lemma boundedElements_costructured_zigzag
    (U : SSet.{u}) (d : ℕ) [U.HasDimensionLT d]
    (x : U.Elements) :
    ∀ a b : CostructuredArrow (boundedElementsInclusion U d) x,
      Zigzag a b := by
  intro a b
  let A := a.left.obj.1.unop
  let B := b.left.obj.1.unop
  let Z := x.1.unop
  let a₀ : U.obj (op (SimplexCategory.mk A.len)) := by
    simpa only [SimplexCategory.mk_len] using a.left.obj.2
  let b₀ : U.obj (op (SimplexCategory.mk B.len)) := by
    simpa only [SimplexCategory.mk_len] using b.left.obj.2
  let x₀ : U.obj (op (SimplexCategory.mk Z.len)) := by
    simpa only [SimplexCategory.mk_len] using x.2
  let α : Z ⟶ SimplexCategory.mk A.len := by
    simpa [A, Z, boundedElementsInclusion] using a.hom.val.unop
  let β : Z ⟶ SimplexCategory.mk B.len := by
    simpa [B, Z, boundedElementsInclusion] using b.hom.val.unop
  have ha_hom : U.map α.op a₀ = x₀ := by
    simpa [α, a₀, x₀] using CategoryOfElements.map_snd a.hom
  have hb_hom : U.map β.op b₀ = x₀ := by
    simpa [β, b₀, x₀] using CategoryOfElements.map_snd b.hom
  obtain ⟨ma, fa, hfa, ya, hya⟩ :=
    SSet.exists_nonDegenerate (X := U) (n := A.len) a₀
  obtain ⟨mb, fb, hfb, yb, hyb⟩ :=
    SSet.exists_nonDegenerate (X := U) (n := B.len) b₀
  have hma : ma < d := U.dim_lt_of_nonDegenerate ya d
  have hmb : mb < d := U.dim_lt_of_nonDegenerate yb d
  have hcomp :
      U.map (α ≫ fa).op ya = U.map (β ≫ fb).op yb := by
    simp only [op_comp, Functor.map_comp, comp_apply]
    rw [← hya, ha_hom, hb_hom.symm, ← hyb]
  obtain ⟨W, s, pa, pb, hW, hpa, hpb, hab⟩ :=
    common_factorization U d (α ≫ fa) (β ≫ fb) ya yb hcomp hma hmb
  have hcore_a :
      U.map (s.op) (U.map pa.op ya) = x₀ := by
    calc
      U.map (s.op) (U.map pa.op ya) = U.map (s ≫ pa).op ya := by
        simp only [op_comp, Functor.map_comp, comp_apply]
      _ = U.map (α ≫ fa).op ya := by rw [← hpa]
      _ = x₀ := by
        simp only [op_comp, Functor.map_comp, comp_apply]
        rw [← hya, ha_hom]
  have hcore_b :
      U.map (s.op) (U.map pb.op yb) = x₀ := by
    calc
      U.map (s.op) (U.map pb.op yb) = U.map (s ≫ pb).op yb := by
        simp only [op_comp, Functor.map_comp, comp_apply]
      _ = U.map (β ≫ fb).op yb := by rw [← hpb]
      _ = x₀ := by
        simp only [op_comp, Functor.map_comp, comp_apply]
        rw [← hyb, hb_hom]
  have hd : 0 < d := by omega
  have hma' : ma < d * d + 1 :=
    hma.trans (Nat.lt_succ_of_le (Nat.le_mul_of_pos_left d hd))
  have hmb' : mb < d * d + 1 :=
    hmb.trans (Nat.lt_succ_of_le (Nat.le_mul_of_pos_left d hd))
  let ca : boundedElements U d :=
    ⟨⟨op (SimplexCategory.mk ma), ya.1⟩, hma'⟩
  let cb : boundedElements U d :=
    ⟨⟨op (SimplexCategory.mk mb), yb.1⟩, hmb'⟩
  let ua₀ : (boundedElementsInclusion U d).obj ca ⟶ a.left.obj :=
    CategoryOfElements.homMk
      ((boundedElementsInclusion U d).obj ca) a.left.obj fa.op hya.symm
  let ub₀ : (boundedElementsInclusion U d).obj cb ⟶ b.left.obj :=
    CategoryOfElements.homMk
      ((boundedElementsInclusion U d).obj cb) b.left.obj fb.op hyb.symm
  let ua : ca ⟶ a.left := ObjectProperty.homMk ua₀
  let ub : cb ⟶ b.left := ObjectProperty.homMk ub₀
  let a' : CostructuredArrow (boundedElementsInclusion U d) x :=
    CostructuredArrow.mk ((boundedElementsInclusion U d).map ua ≫ a.hom)
  let b' : CostructuredArrow (boundedElementsInclusion U d) x :=
    CostructuredArrow.mk ((boundedElementsInclusion U d).map ub ≫ b.hom)
  have ha' : a' ⟶ a := CostructuredArrow.homMk' a ua
  have hb' : b' ⟶ b := CostructuredArrow.homMk' b ub
  let c : boundedElements U d :=
    ⟨⟨op W, U.map pa.op ya⟩, hW⟩
  let va₀ : (boundedElementsInclusion U d).obj ca ⟶
      (boundedElementsInclusion U d).obj c :=
    CategoryOfElements.homMk
      ((boundedElementsInclusion U d).obj ca)
      ((boundedElementsInclusion U d).obj c) pa.op rfl
  let vb₀ : (boundedElementsInclusion U d).obj cb ⟶
      (boundedElementsInclusion U d).obj c :=
    CategoryOfElements.homMk
      ((boundedElementsInclusion U d).obj cb)
      ((boundedElementsInclusion U d).obj c) pb.op hab.symm
  let va : ca ⟶ c := ObjectProperty.homMk va₀
  let vb : cb ⟶ c := ObjectProperty.homMk vb₀
  let q : (boundedElementsInclusion U d).obj c ⟶ x :=
    CategoryOfElements.homMk
      ((boundedElementsInclusion U d).obj c) x s.op hcore_a
  let c' : CostructuredArrow (boundedElementsInclusion U d) x :=
    CostructuredArrow.mk q
  have haC : a' ⟶ c' := by
    refine CostructuredArrow.homMk va ?_
    dsimp [a', c', va, va₀, ua, ua₀, q, boundedElementsInclusion]
    apply CategoryOfElements.ext _ _
    change pa.op ≫ s.op = fa.op ≫ a.hom.val
    have hop := congrArg Opposite.op hpa.symm
    change (s ≫ pa).op = (α ≫ fa).op at hop
    rw [op_comp, op_comp] at hop
    exact hop
  have hbC : b' ⟶ c' := by
    refine CostructuredArrow.homMk vb ?_
    dsimp [b', c', vb, vb₀, ub, ub₀, q, boundedElementsInclusion]
    apply CategoryOfElements.ext _ _
    change pb.op ≫ s.op = fb.op ≫ b.hom.val
    have hop := congrArg Opposite.op hpb.symm
    change (s ≫ pb).op = (β ≫ fb).op at hop
    rw [op_comp, op_comp] at hop
    exact hop
  exact (Zigzag.of_inv ha').trans
    ((Zigzag.of_hom haC).trans
      ((Zigzag.of_inv hbC).trans (Zigzag.of_hom hb')))

theorem boundedElementsInclusion_initial
    (U : SSet.{u}) (d : ℕ) [U.HasDimensionLT d] :
    Functor.Initial (boundedElementsInclusion U d) := by
  refine { out := fun x => ?_ }
  exact @zigzag_isConnected _ _
    (boundedElements_costructured_nonempty U d x)
    (boundedElements_costructured_zigzag U d x)

end Formalization.Books.Simplicial.Unit11
