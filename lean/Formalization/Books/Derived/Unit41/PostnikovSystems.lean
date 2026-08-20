import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Formalization.Books.Derived.Unit04.ElementaryResults
import Formalization.Books.Derived.Unit33.DerivedColimits
import Formalization.Books.Homology.Unit15.TruncationOfComplexes

/-!
# Derived Categories, Chapter 41: Postnikov systems

Finite complexes are represented by `HomologicalComplex` with the finite
downward shape.  A Postnikov system records its objects, the maps to the
terms of the complex, and the distinguished triangle between two successive
terms.  The theorem interfaces below retain the source's existence,
extension, uniqueness, and vanishing statements without attempting their
proofs.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open ComplexShape
open Formalization.Books.Derived.Unit04
open Formalization.Books.Derived.Unit33
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u w

namespace Formalization.Books.Derived.Unit41

/-! ## Finite complexes -/

/-- The finite downward complex shape on `Fin (n + 1)`. -/
def finitePostnikovShape (n : ℕ) : ComplexShape (Fin (n + 1)) where
  Rel i j := j.val + 1 = i.val
  next_eq := by
    intro i j j' hij hij'
    apply Fin.ext
    omega
  prev_eq := by
    intro i i' j hij hij'
    apply Fin.ext
    omega

/-- A finite complex `X_n → ⋯ → X_0` in a category with zero morphisms. -/
abbrev FinitePostnikovComplex
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C] (n : ℕ) :=
  HomologicalComplex C (finitePostnikovShape n)

/-- The index `i` viewed in `Fin (n + 1)`. -/
def finitePostnikovIndex
    {n : ℕ} (i : Fin n) : Fin (n + 1) :=
  ⟨i.val, by omega⟩

/-- The successor index used for the arrow `X_(i+1) → X_i`. -/
def finitePostnikovSuccIndex
    {n : ℕ} (i : Fin n) : Fin (n + 1) :=
  ⟨i.val + 1, by omega⟩

/-- The last index of a finite complex. -/
def finitePostnikovLastIndex (n : ℕ) : Fin (n + 1) :=
  ⟨n, by omega⟩

/-- The degree-zero index of a finite complex. -/
def finitePostnikovZeroIndex (n : ℕ) : Fin (n + 1) :=
  ⟨0, by omega⟩

/-- The index `j - (i + 1)` when `i + 1 ≤ j`. -/
def finitePostnikovSubIndex
    {n : ℕ} (i : Fin n) (j : Fin (n + 1))
    (h : i.val + 1 ≤ j.val) : Fin (n + 1) :=
  ⟨j.val - (i.val + 1), by omega⟩

/-- The differential `X_(i+1) → X_i` of a finite complex. -/
abbrev finitePostnikovDifferential
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {n : ℕ} (K : FinitePostnikovComplex C n) (i : Fin n) :
    K.X (finitePostnikovSuccIndex i) ⟶ K.X (finitePostnikovIndex i) :=
  K.d (finitePostnikovSuccIndex i) (finitePostnikovIndex i)

/-! ## The finite Postnikov-system structure and its maps -/

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

/-- The data of a Postnikov system for a finite complex.

`toX i` is the map `Y_i → X_i`; for `i < n`, the corresponding distinguished
triangle is `Y_(i+1) → X_(i+1) → Y_i → Y_(i+1)[1]`. -/
structure PostnikovSystem
    {n : ℕ} (K : FinitePostnikovComplex C n) where
  Y : Fin (n + 1) → C
  toX : ∀ i, Y i ⟶ K.X i
  baseIso : Y (finitePostnikovZeroIndex n) ≅ K.X (finitePostnikovZeroIndex n)
  baseIso_hom : baseIso.hom = toX _
  fromX : ∀ i : Fin n, K.X (finitePostnikovSuccIndex i) ⟶
    Y (finitePostnikovIndex i)
  connecting : ∀ i : Fin n,
    Y (finitePostnikovIndex i) ⟶
      (shiftFunctor C (1 : ℤ)).obj (Y (finitePostnikovSuccIndex i))
  distinguished : ∀ i : Fin n,
    Triangle.mk (toX (finitePostnikovSuccIndex i)) (fromX i) (connecting i) ∈
      distTriang C
  compatibility : ∀ i : Fin n,
    fromX i ≫ toX (finitePostnikovIndex i) = finitePostnikovDifferential K i

/-- The distinguished triangle at a step of a Postnikov system. -/
def postnikovTriangle
    {n : ℕ} {K : FinitePostnikovComplex C n} (P : PostnikovSystem K)
    (i : Fin n) : Triangle C :=
  Triangle.mk (P.toX (finitePostnikovSuccIndex i)) (P.fromX i) (P.connecting i)

/-- The rotated and shifted distinguished triangle displayed in the source:
`Y_i[i] → Y_(i+1)[i+1] → X_(i+1)[i+1] → Y_i[i+1]`. -/
def postnikovShiftedTriangle
    {n : ℕ} {K : FinitePostnikovComplex C n} (P : PostnikovSystem K)
    (i : Fin n) : Triangle C :=
  (Triangle.shiftFunctor C (i.val : ℤ)).obj
    ((rotate C).obj ((rotate C).obj (postnikovTriangle P i)))

/-- A morphism of Postnikov systems over a morphism of finite complexes. -/
structure PostnikovSystemHom
    {n : ℕ} {K K' : FinitePostnikovComplex C n}
    {P : PostnikovSystem K} {P' : PostnikovSystem K'}
    (f : K ⟶ K') where
  y : ∀ i, P.Y i ⟶ P'.Y i
  toX_naturality : ∀ i,
    P.toX i ≫ f.f i = y i ≫ P'.toX i
  triangleMap : ∀ i : Fin n,
    postnikovTriangle P i ⟶ postnikovTriangle P' i
  triangleMap_hom₁ : ∀ i : Fin n,
    (triangleMap i).hom₁ = y (finitePostnikovSuccIndex i)
  triangleMap_hom₂ : ∀ i : Fin n,
    (triangleMap i).hom₂ = f.f (finitePostnikovSuccIndex i)
  triangleMap_hom₃ : ∀ i : Fin n,
    (triangleMap i).hom₃ = y (finitePostnikovIndex i)

/-- An isomorphism of Postnikov systems, including an isomorphism of the
underlying finite complexes. -/
structure PostnikovSystemIso
    {n : ℕ} {K K' : FinitePostnikovComplex C n}
    {P : PostnikovSystem K} {P' : PostnikovSystem K'}
    (f : K ⟶ K') where
  hom : PostnikovSystemHom (P := P) (P' := P') f
  f_isIso : IsIso f
  y_isIso : ∀ i, IsIso (hom.y i)

/-- The maps `Y_i → Y_(i+1)[1]` form the source's Postnikov tower. -/
abbrev postnikovTowerMap
    {n : ℕ} {K : FinitePostnikovComplex C n} (P : PostnikovSystem K)
    (i : Fin n) := P.connecting i

/-! ## The direct-sum special case and the low-length assertions -/

/-- All differentials of a finite complex vanish. -/
def IsZeroPostnikovComplex
    {n : ℕ} (K : FinitePostnikovComplex C n) : Prop :=
  ∀ i : Fin n, finitePostnikovDifferential K i = 0

/-- The finite direct sum `⊕ i, X_i[i]` from the zero-differential remark. -/
noncomputable def zeroDifferentialTotal
    {n : ℕ} (K : FinitePostnikovComplex C n) : C :=
  ⨁ fun i : Fin (n + 1) =>
    (shiftFunctor C (i.val : ℤ)).obj (K.X i)

/-- In the zero-differential case the last totalization can be chosen as the
finite direct sum of the shifted terms. -/
theorem exists_zero_differential_postnikov_system
    {n : ℕ} (K : FinitePostnikovComplex C n)
    (hK : IsZeroPostnikovComplex K) :
    ∃ P : PostnikovSystem K,
      Nonempty
        ((shiftFunctor C (n : ℤ)).obj (P.Y (finitePostnikovLastIndex n)) ≅
          zeroDifferentialTotal K) := by
  let coneY (i : Fin n) (Z : C) : C :=
    Classical.choose (distinguished_cocone_triangle₁
      (0 : K.X (finitePostnikovSuccIndex i) ⟶ Z))
  let coneU (i : Fin n) (Z : C) : coneY i Z ⟶
      K.X (finitePostnikovSuccIndex i) :=
    Classical.choose (Classical.choose_spec
      (distinguished_cocone_triangle₁
        (0 : K.X (finitePostnikovSuccIndex i) ⟶ Z)))
  let coneV (i : Fin n) (Z : C) : Z ⟶
      (shiftFunctor C (1 : ℤ)).obj (coneY i Z) :=
    Classical.choose (Classical.choose_spec
      (Classical.choose_spec
        (distinguished_cocone_triangle₁
          (0 : K.X (finitePostnikovSuccIndex i) ⟶ Z))))
  let hCone (i : Fin n) (Z : C) :
      Triangle.mk (coneU i Z) (0 : K.X (finitePostnikovSuccIndex i) ⟶ Z)
          (coneV i Z) ∈ distTriang C :=
    Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec
        (distinguished_cocone_triangle₁
          (0 : K.X (finitePostnikovSuccIndex i) ⟶ Z))))
  let Y : Fin (n + 1) → C :=
    Fin.induction (motive := fun _ => C) (K.X 0)
      (fun i Z => coneY i Z)
  have hY_succ (i : Fin n) :
      Y (Fin.succ i) = coneY i (Y (Fin.castSucc i)) := by
    rfl
  have h0 : Y 0 = K.X 0 := by
    rfl
  let toX : ∀ i, Y i ⟶ K.X i :=
    Fin.induction (motive := fun i => Y i ⟶ K.X i) (eqToHom h0)
      (fun i _ =>
        eqToHom (show Y (Fin.succ i) = coneY i (Y (Fin.castSucc i)) by rfl) ≫
          coneU i (Y (Fin.castSucc i)) ≫
          eqToHom (congrArg K.X (show finitePostnikovSuccIndex i = Fin.succ i by
            apply Fin.ext
            rfl)))
  let fromX : ∀ i : Fin n, K.X (finitePostnikovSuccIndex i) ⟶
      Y (finitePostnikovIndex i) := fun i => 0
  let connecting : ∀ i : Fin n, Y (finitePostnikovIndex i) ⟶
      (shiftFunctor C (1 : ℤ)).obj (Y (finitePostnikovSuccIndex i)) :=
    fun i =>
      eqToHom (congrArg Y (show finitePostnikovIndex i = Fin.castSucc i by
        apply Fin.ext
        rfl)) ≫
        coneV i (Y (Fin.castSucc i)) ≫
        (shiftFunctor C (1 : ℤ)).map
          (eqToHom ((show Y (Fin.succ i) = coneY i (Y (Fin.castSucc i)) by
            rfl).symm.trans
            (congrArg Y (show Fin.succ i = finitePostnikovSuccIndex i by
              apply Fin.ext
              rfl))))
  have htoX_general (i : Fin n) (j : Fin (n + 1))
      (hj : j = Fin.succ i) :
      toX j =
        eqToHom (congrArg Y hj) ≫
          eqToHom (show Y (Fin.succ i) = coneY i (Y (Fin.castSucc i)) by rfl) ≫
          coneU i (Y (Fin.castSucc i)) ≫
          eqToHom (congrArg K.X ((show finitePostnikovSuccIndex i = Fin.succ i by
            apply Fin.ext
            rfl).trans hj.symm)) := by
    subst j
    simp [toX]
  have htoX_zero (j : Fin (n + 1)) (hj : j = (0 : Fin (n + 1))) :
      toX j = eqToHom (congrArg Y hj) ≫ eqToHom h0 ≫
        eqToHom (congrArg K.X hj.symm) := by
    subst j
    simp [toX]
  have hdist (i : Fin n) :
      Triangle.mk (toX (finitePostnikovSuccIndex i)) (fromX i)
          (connecting i) ∈ distTriang C := by
    have hi : finitePostnikovSuccIndex i = Fin.succ i := by
      apply Fin.ext
      rfl
    have hidx : finitePostnikovIndex i = Fin.castSucc i := by
      apply Fin.ext
      rfl
    let e₁ : Y (finitePostnikovSuccIndex i) ≅
        coneY i (Y (Fin.castSucc i)) :=
      eqToIso (congrArg Y hi) ≪≫
        eqToIso (show Y (Fin.succ i) = coneY i (Y (Fin.castSucc i)) by rfl)
    let e₂ : K.X (finitePostnikovSuccIndex i) ≅
        K.X (finitePostnikovSuccIndex i) := Iso.refl _
    let e₃ : Y (finitePostnikovIndex i) ≅ Y (Fin.castSucc i) :=
      eqToIso (congrArg Y hidx)
    apply isomorphic_distinguished _ (hCone i (Y (Fin.castSucc i))) _
      (Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_)
    · dsimp [Triangle.mk, e₁, e₂]
      rw [htoX_general i (finitePostnikovSuccIndex i) hi]
      simp [Category.assoc, eqToHom_trans]
    · dsimp [Triangle.mk, e₂, e₃, fromX]
      simp
    · dsimp [Triangle.mk, e₁, e₃, connecting]
      simp [Category.assoc, eqToHom_trans]
  let P : PostnikovSystem K :=
    let hz : finitePostnikovZeroIndex n = (0 : Fin (n + 1)) := by
      apply Fin.ext
      rfl
    let baseIso : Y (finitePostnikovZeroIndex n) ≅
        K.X (finitePostnikovZeroIndex n) :=
      eqToIso (congrArg Y hz) ≪≫ eqToIso h0 ≪≫
        eqToIso (congrArg K.X hz.symm)
    { Y := Y
      toX := toX
      baseIso := baseIso
      baseIso_hom := by
        rw [show toX (finitePostnikovZeroIndex n) =
          eqToHom (congrArg Y hz) ≫ eqToHom h0 ≫
            eqToHom (congrArg K.X hz.symm) by
          exact htoX_zero (finitePostnikovZeroIndex n) hz]
        simp [baseIso, eqToHom_trans]
      fromX := fromX
      connecting := connecting
      distinguished := hdist
      compatibility := by
        intro i
        simp [fromX, hK i] }
  refine ⟨P, ?_⟩
  have hsplit (i : Fin n) :
      Y (Fin.castSucc i) ⊞ (shiftFunctor C (1 : ℤ)).obj
          (K.X (finitePostnikovSuccIndex i)) ≅
        (shiftFunctor C (1 : ℤ)).obj (Y (finitePostnikovSuccIndex i)) := by
    let T := Triangle.mk (coneU i (Y (Fin.castSucc i)))
      (0 : K.X (finitePostnikovSuccIndex i) ⟶ Y (Fin.castSucc i))
      (coneV i (Y (Fin.castSucc i)))
    let T' := (rotate C).obj ((rotate C).obj T)
    have hT' : T' ∈ distTriang C :=
      rot_of_distTriang _ (rot_of_distTriang _ (hCone i (Y (Fin.castSucc i))))
    have hzero : T'.mor₃ = 0 := by
      change -(shiftFunctor C (1 : ℤ)).map
          (0 : K.X (finitePostnikovSuccIndex i) ⟶ Y (Fin.castSucc i)) = 0
      simp
    let e := Classical.choose (exists_iso_binaryBiproduct_of_distTriang T' hT' hzero)
    let q : coneY i (Y (Fin.castSucc i)) =
        Y (finitePostnikovSuccIndex i) :=
      (show Y (Fin.succ i) = coneY i (Y (Fin.castSucc i)) by rfl).symm.trans
        (congrArg Y (show Fin.succ i = finitePostnikovSuccIndex i by
          apply Fin.ext
          rfl))
    exact e.symm ≪≫ eqToIso (congrArg (shiftFunctor C (1 : ℤ)).obj q)
  let S : Fin (n + 1) → C :=
    Fin.induction (K.X 0) (fun i Z =>
      Z ⊞ (shiftFunctor C (((i.val + 1 : ℕ) : ℤ))).obj
        (K.X (finitePostnikovSuccIndex i)))
  let biprodMapIso (F : C ⥤ C) [F.Additive] (A B : C) :
      F.obj (A ⊞ B) ≅ F.obj A ⊞ F.obj B :=
    { hom := Functor.biprodComparison F A B
      inv := Functor.biprodComparison' F A B
      hom_inv_id := by
        dsimp [Functor.biprodComparison, Functor.biprodComparison']
        rw [biprod.lift_desc, ← F.map_comp, ← F.map_comp, ← F.map_add,
          biprod.total, F.map_id]
      inv_hom_id := Functor.biprodComparison'_comp_biprodComparison F A B }
  have hE : ∀ i : Fin (n + 1),
      (shiftFunctor C (i.val : ℤ)).obj (Y i) ≅ S i := by
    intro i
    induction i using Fin.induction with
    | zero =>
        exact (shiftFunctorZero C ℤ).app (Y 0) ≪≫ eqToIso h0
    | succ i e =>
        have hi : finitePostnikovSuccIndex i = Fin.succ i := by
          apply Fin.ext
          rfl
        let a := shiftFunctorAdd' C (1 : ℤ) (i.val : ℤ)
          ((i.val + 1 : ℕ) : ℤ) (by omega)
        exact eqToIso (congrArg ((shiftFunctor C (((i.val + 1 : ℕ) : ℤ))).obj)
            (congrArg Y hi.symm)) ≪≫
          a.app (Y (finitePostnikovSuccIndex i)) ≪≫
          (shiftFunctor C (i.val : ℤ)).mapIso (hsplit i).symm ≪≫
          biprodMapIso (shiftFunctor C (i.val : ℤ))
            (Y (Fin.castSucc i))
            ((shiftFunctor C (1 : ℤ)).obj
              (K.X (finitePostnikovSuccIndex i))) ≪≫
          biprod.mapIso e
            (a.app (K.X (finitePostnikovSuccIndex i))).symm
  have appendIso {m : ℕ} (f : Fin (m + 2) → C) :
      (⨁ fun k : Fin (m + 1) => f k.castSucc) ⊞ f (Fin.last (m + 1)) ≅ ⨁ f := by
    refine
      { hom := biprod.desc
          (biproduct.desc fun k : Fin (m + 1) => biproduct.ι f k.castSucc)
          (biproduct.ι f (Fin.last (m + 1)))
        inv := biprod.lift
          (biproduct.lift fun k : Fin (m + 1) => biproduct.π f k.castSucc)
          (biproduct.π f (Fin.last (m + 1)))
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst]
        simp only [Category.id_comp]
        apply biprod.hom_ext'
        · simp [Category.assoc]
          apply biproduct.hom_ext'
          intro k
          simp [Category.assoc]
          apply biproduct.hom_ext
          intro j
          rw [Category.assoc, biproduct.lift_π]
          by_cases h : k = j
          · subst j
            simp
          · have hcast : k.castSucc ≠ j.castSucc := by
              intro h'
              apply h
              exact Fin.ext (by simpa using congrArg Fin.val h')
            rw [biproduct.ι_π_ne f hcast]
            rw [biproduct.ι_π_ne (fun k => f k.castSucc) h]
        · simp [Category.assoc]
          apply biproduct.hom_ext
          intro k
          rw [Category.assoc, biproduct.lift_π]
          simpa using (biproduct.ι_π_ne f (k.castSucc_ne_last.symm))
      · apply biprod.hom_ext'
        · simp [Category.assoc]
          apply biproduct.hom_ext'
          intro k
          simp [Category.assoc, k.castSucc_ne_last]
        · simp [Category.assoc]
    · apply biproduct.hom_ext'
      intro k
      obtain ⟨k, rfl⟩ | rfl := k.eq_castSucc_or_eq_last
      · classical
        rw [biprod.lift_desc, comp_add]
        simp only [Category.assoc, biproduct.lift_desc]
        rw [Preadditive.comp_sum]
        rw [Finset.sum_eq_single k]
        · simp
        · intro b hb hbk
          by_cases h : k = b
          · subst b
            exact (hbk rfl).elim
          · simp [h, Ne.symm h]
        · simp
      · apply biproduct.hom_ext
        intro k
        obtain ⟨k, rfl⟩ | rfl := k.eq_castSucc_or_eq_last
        · classical
          simp [Category.assoc, biprod.lift_desc, biproduct.lift_desc,
            Preadditive.comp_sum, Preadditive.sum_comp, add_comp, comp_add,
            biproduct.ι_π_assoc, comp_dite]
          apply Finset.sum_eq_zero
          intro x hx
          by_cases h : Fin.last (m + 1) = x.castSucc
          · exact (x.castSucc_ne_last h.symm).elim
          · simp [h]
        · classical
          simp [Category.assoc, biprod.lift_desc, biproduct.lift_desc,
            Preadditive.comp_sum, Preadditive.sum_comp, add_comp, comp_add,
            biproduct.ι_π_assoc, comp_dite]
  let A : Fin (n + 1) → C := fun j =>
    (shiftFunctor C (j.val : ℤ)).obj (K.X j)
  let R : ∀ j : Fin (n + 1), C := fun j =>
    ⨁ fun k : Fin (j.val + 1) => A ⟨k.val, by omega⟩
  have singleIso (f : Fin 1 → C) : f 0 ≅ ⨁ f := by
    refine
      { hom := biproduct.ι f 0
        inv := biproduct.π f 0
        hom_inv_id := by simp
        inv_hom_id := by
          apply biproduct.hom_ext'
          intro i
          have hi : i = 0 := Fin.ext (by omega)
          subst i
          simp }
  have hR : ∀ j : Fin (n + 1), S j ≅ R j := by
    intro j
    induction j using Fin.induction with
    | zero =>
        simpa [S, R, A] using
          ((shiftFunctorZero C ℤ).app (K.X 0)).symm ≪≫
            singleIso (fun k : Fin 1 => A ⟨k.val, by omega⟩)
    | succ i e =>
        let f : Fin (i.val + 2) → C := fun k => A ⟨k.val, by omega⟩
        have hiX : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) =
            finitePostnikovSuccIndex i := by
          apply Fin.ext
          rfl
        let eX : f (Fin.last (i.val + 1)) ≅
            (shiftFunctor C (((i.val + 1 : ℕ) : ℤ))).obj
              (K.X (finitePostnikovSuccIndex i)) :=
          eqToIso (congrArg
            (fun j : Fin (n + 1) =>
              (shiftFunctor C (((i.val + 1 : ℕ) : ℤ))).obj (K.X j)) hiX)
        simpa [S, R, A, f] using
          (biprod.mapIso (Iso.refl _) eX.symm) ≪≫
            (biprod.mapIso e (Iso.refl _)) ≪≫ appendIso f
  have hS : S (finitePostnikovLastIndex n) ≅ zeroDifferentialTotal K := by
    let e : ∀ k : Fin (n + 1), A ⟨k.val, by omega⟩ ≅ A k := fun k =>
      let hk : (⟨k.val, by omega⟩ : Fin (n + 1)) = k := by
        apply Fin.ext
        rfl
      eqToIso (congrArg A hk)
    simpa [R, A, zeroDifferentialTotal] using
      hR (finitePostnikovLastIndex n) ≪≫
        biproduct.mapIso (f := fun k : Fin (n + 1) => A ⟨k.val, by omega⟩)
          (g := A) e
  have hlast :
      (shiftFunctor C (n : ℤ)).obj (Y (finitePostnikovLastIndex n)) ≅
        S (finitePostnikovLastIndex n) := by
    exact hE (finitePostnikovLastIndex n)
  exact ⟨hlast ≪≫ hS⟩

/-- Every shifted triangle in the Postnikov tower is distinguished. -/
theorem postnikovShiftedTriangle_distinguished
    {n : ℕ} {K : FinitePostnikovComplex C n} (P : PostnikovSystem K)
    (i : Fin n) :
    postnikovShiftedTriangle P i ∈ distTriang C := by
  let _ := (inferInstance : IsTriangulated C)
  classical
  exact Triangle.shift_distinguished _
    (rot_of_distTriang _ (rot_of_distTriang _ (P.distinguished i))) (i.val : ℤ)

/-- Existence of a Postnikov system for a complex of length zero. -/
theorem postnikovSystem_exists_length_zero
    (K : FinitePostnikovComplex C 0) :
    Nonempty (PostnikovSystem K) := by
  let _ := (inferInstance : IsTriangulated C)
  refine ⟨{ Y := K.X, toX := fun _ => 𝟙 _, baseIso := Iso.refl _, baseIso_hom := by simp, fromX := fun i => Fin.elim0 i, connecting := fun i => Fin.elim0 i, distinguished := fun i => Fin.elim0 i, compatibility := fun i => Fin.elim0 i }⟩

/-- Any map of length-zero complexes extends to a map of chosen systems. -/
theorem postnikovSystemHom_exists_length_zero
    {K K' : FinitePostnikovComplex C 0}
    (f : K ⟶ K') (P : PostnikovSystem K) (P' : PostnikovSystem K') :
    Nonempty (PostnikovSystemHom (P := P) (P' := P') f) := by
  let _ := (inferInstance : IsTriangulated C)
  let y : ∀ i, P.Y i ⟶ P'.Y i := fun i =>
    eqToHom (congrArg P.Y (Fin.ext (by omega) : i = finitePostnikovZeroIndex 0)) ≫
      P.baseIso.hom ≫ f.f (finitePostnikovZeroIndex 0) ≫ P'.baseIso.inv ≫
      eqToHom (congrArg P'.Y (Fin.ext (by omega) : finitePostnikovZeroIndex 0 = i))
  refine ⟨{ y := y, toX_naturality := ?_, triangleMap := fun i => Fin.elim0 i, triangleMap_hom₁ := fun i => Fin.elim0 i, triangleMap_hom₂ := fun i => Fin.elim0 i, triangleMap_hom₃ := fun i => Fin.elim0 i }⟩
  intro i
  have hi : i = finitePostnikovZeroIndex 0 := Fin.ext (by omega)
  subst i
  dsimp [y]
  rw [← P.baseIso_hom, ← P'.baseIso_hom]
  simp

/-- The length-zero extension is unique. -/
theorem postnikovSystemHom_unique_length_zero
    {K K' : FinitePostnikovComplex C 0}
    (f : K ⟶ K') (P : PostnikovSystem K) (P' : PostnikovSystem K')
    (φ ψ : PostnikovSystemHom (P := P) (P' := P') f) :
    φ = ψ := by
  let _ := (inferInstance : IsTriangulated C)
  cases φ with
  | mk y nat tm h1 h2 h3 =>
    cases ψ with
    | mk y' nat' tm' h1' h2' h3' =>
      have hy : y = y' := by
        funext i
        have hi : i = finitePostnikovZeroIndex 0 := Fin.ext (by omega)
        subst i
        apply (cancel_mono P'.baseIso.hom).1
        rw [P'.baseIso_hom]
        exact (nat _).symm.trans (nat' _)
      have htm : tm = tm' := Subsingleton.elim _ _
      subst y'
      subst tm'
      rfl

/-- Existence of a Postnikov system for a complex of length one. -/
theorem postnikovSystem_exists_length_one
    (K : FinitePostnikovComplex C 1) :
    Nonempty (PostnikovSystem K) := by
  let _ := (inferInstance : IsTriangulated C)
  obtain ⟨Y₁, u, v, hT⟩ :=
    distinguished_cocone_triangle₁ (finitePostnikovDifferential K (0 : Fin 1))
  let Y : Fin 2 → C := Fin.cases (K.X 0) (fun _ => Y₁)
  have h0 : Y 0 = K.X 0 := by
    dsimp [Y]
  have hY : Y (Fin.succ (0 : Fin 1)) = Y₁ := by
    change Fin.cases (K.X 0) (fun _ => Y₁) (Fin.succ (0 : Fin 1)) = Y₁
    rfl
  have hs : finitePostnikovSuccIndex (0 : Fin 1) = Fin.succ (0 : Fin 1) := by
    apply Fin.ext
    rfl
  have hX : K.X (finitePostnikovSuccIndex (0 : Fin 1)) =
      K.X (Fin.succ (0 : Fin 1)) :=
    congrArg K.X hs
  let toX : ∀ j, Y j ⟶ K.X j := fun j =>
    Fin.cases (eqToHom h0)
      (fun k => Fin.cases (eqToHom hY ≫ u ≫ eqToHom hX)
        (fun l => Fin.elim0 l) k) j
  have htoX_general (j : Fin 2) (hj : j = Fin.succ (0 : Fin 1)) :
      toX j =
        eqToHom (congrArg Y hj) ≫ eqToHom hY ≫ u ≫
          eqToHom (congrArg K.X (hs.trans hj.symm)) := by
    subst j
    change Fin.cases (eqToHom h0)
      (fun k => Fin.cases (eqToHom hY ≫ u ≫ eqToHom hX)
        (fun l => Fin.elim0 l) k)
      (Fin.succ (0 : Fin 1)) =
      eqToHom (congrArg Y rfl) ≫ eqToHom hY ≫ u ≫
        eqToHom (congrArg K.X (hs.trans rfl))
    rw [Fin.cases_succ]
    simp
  have hzidx : finitePostnikovIndex (0 : Fin 1) = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have hK0 : K.X (finitePostnikovIndex (0 : Fin 1)) = K.X 0 :=
    congrArg K.X hzidx
  have hy0 : Y (finitePostnikovIndex (0 : Fin 1)) = Y 0 :=
    congrArg Y hzidx
  have hY0 : Y (finitePostnikovIndex (0 : Fin 1)) =
      K.X (finitePostnikovIndex (0 : Fin 1)) :=
    hy0.trans (h0.trans hK0.symm)
  have htoX_succ : toX (finitePostnikovSuccIndex (0 : Fin 1)) =
      (eqToIso (congrArg Y hs) ≪≫ eqToIso hY).hom ≫ u := by
    simpa [eqToHom_trans] using
      (htoX_general (finitePostnikovSuccIndex (0 : Fin 1)) hs)
  have htoX_zero_general (j : Fin 2) (hj : j = (0 : Fin 2)) :
      toX j = eqToHom (congrArg Y hj) ≫ eqToHom h0 ≫
        eqToHom (congrArg K.X hj.symm) := by
    subst j
    change Fin.cases (eqToHom h0)
      (fun k => Fin.cases (eqToHom hY ≫ u ≫ eqToHom hX)
        (fun l => Fin.elim0 l) k) 0 =
      eqToHom (congrArg Y rfl) ≫ eqToHom h0 ≫
        eqToHom (congrArg K.X rfl)
    rw [Fin.cases_zero]
    simp
  have htoX_zero :
      toX (finitePostnikovIndex (0 : Fin 1)) = eqToHom hY0 := by
    simpa [eqToHom_trans] using
      (htoX_zero_general (finitePostnikovIndex (0 : Fin 1)) hzidx)
  let fromX : ∀ i : Fin 1, K.X (finitePostnikovSuccIndex i) ⟶
      Y (finitePostnikovIndex i) :=
    fun i => Fin.cases
      (finitePostnikovDifferential K (0 : Fin 1) ≫ eqToHom hY0.symm)
      (fun j => Fin.elim0 j) i
  let c0 : Y (finitePostnikovIndex (0 : Fin 1)) ⟶
      (shiftFunctor C (1 : ℤ)).obj (Y (finitePostnikovSuccIndex (0 : Fin 1))) :=
    eqToHom hY0 ≫ v ≫
      (shiftFunctor C (1 : ℤ)).map (eqToHom (congrArg Y hs).symm)
  let connecting : ∀ i : Fin 1, Y (finitePostnikovIndex i) ⟶
      (shiftFunctor C (1 : ℤ)).obj (Y (finitePostnikovSuccIndex i)) :=
    fun i => Fin.cases c0 (fun j => Fin.elim0 j) i
  have hz0 : finitePostnikovZeroIndex 1 = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have base_iso_data (j : Fin 2) (hj : j = (0 : Fin 2)) :
      ∃ e : Y j = K.X j, toX j = eqToHom e := by
    subst j
    refine ⟨h0, ?_⟩
    simp [toX]
  obtain ⟨e, he⟩ := base_iso_data (finitePostnikovZeroIndex 1) hz0
  let baseIso : Y (finitePostnikovZeroIndex 1) ≅
      K.X (finitePostnikovZeroIndex 1) :=
    { hom := toX (finitePostnikovZeroIndex 1)
      inv := eqToHom e.symm
      hom_inv_id := by rw [he]; simp
      inv_hom_id := by rw [he]; simp }
  refine ⟨{ Y := Y, toX := toX, baseIso := baseIso, baseIso_hom := he, fromX := fromX, connecting := connecting, distinguished := ?_, compatibility := ?_ }⟩
  · intro i
    fin_cases i
    let e₁ : Y (finitePostnikovSuccIndex (0 : Fin 1)) ≅ Y₁ :=
      eqToIso (congrArg Y hs) ≪≫ eqToIso hY
    let e₂ : K.X (finitePostnikovSuccIndex (0 : Fin 1)) ≅
        K.X (finitePostnikovSuccIndex (0 : Fin 1)) := Iso.refl _
    let e₃ : Y (finitePostnikovIndex (0 : Fin 1)) ≅
        K.X (finitePostnikovIndex (0 : Fin 1)) := eqToIso hY0
    apply isomorphic_distinguished _ hT _
      (Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_)
    · dsimp [Triangle.mk, e₁, e₂]
      rw [htoX_succ]
      simp
    · dsimp [Triangle.mk, e₂, e₃, fromX]
      simp [Category.assoc, eqToHom_trans]
    · dsimp [Triangle.mk, e₁, e₃, connecting, c0]
      have hq : Y₁ = Y (finitePostnikovSuccIndex (0 : Fin 1)) :=
        hY.symm.trans (congrArg Y hs).symm
      have hcancel :
          (shiftFunctor C (1 : ℤ)).map (eqToHom hq) ≫
              (shiftFunctor C (1 : ℤ)).map
                (eqToHom (congrArg Y hs) ≫ eqToHom hY) =
            𝟙 ((shiftFunctor C (1 : ℤ)).obj Y₁) := by
        rw [← Functor.map_comp]
        simp [eqToHom_trans]
      simp only [Category.assoc]
      rw [hcancel]
      simp
  · intro i
    fin_cases i
    dsimp [fromX]
    rw [htoX_zero]
    simp [Category.assoc]

private lemma homIsZero_of_iso
    {X X' Y Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (h : HomIsZero X' Y) : HomIsZero X Y' := by
  intro f
  have hf : eX.inv ≫ f ≫ eY.inv = 0 := h _
  have hf' : f ≫ eY.inv = 0 := by
    calc
      f ≫ eY.inv = eX.hom ≫ (eX.inv ≫ f ≫ eY.inv) := by simp
      _ = 0 := by rw [hf, comp_zero]
  apply (cancel_mono eY.inv).1
  simpa using hf'

private lemma homIsZero_shift_of_neg
    {X Y : C} (a b : ℤ) (hab : a + b = 0)
    (h : HomIsZero ((shiftFunctor C a).obj X) Y) :
    HomIsZero X ((shiftFunctor C b).obj Y) := by
  letI : (shiftEquiv' C a b hab).functor.Additive := by
    change (shiftFunctor C a).Additive
    infer_instance
  intro f
  let e := (shiftEquiv' C a b hab).toAdjunction.homEquiv X Y
  have hf : e.symm f = 0 := h _
  apply e.symm.injective
  have : e.symm f = e.symm 0 := by
    calc
      e.symm f = 0 := hf
      _ = e.symm 0 := by
        symm
        change ((shiftEquiv' C a b hab).toAdjunction.homEquiv X Y).symm 0 = 0
        exact CategoryTheory.Adjunction.homAddEquiv_symm_zero
          ((shiftEquiv' C a b hab).toAdjunction) X Y
  exact this

private lemma homIsZero_shift_add_left
    {X Y : C} (a b : ℤ) (h : HomIsZero ((shiftFunctor C (a + b)).obj X) Y) :
    HomIsZero ((shiftFunctor C b).obj ((shiftFunctor C a).obj X)) Y := by
  let eX : (shiftFunctor C b).obj ((shiftFunctor C a).obj X) ≅
      (shiftFunctor C (a + b)).obj X :=
    ((shiftFunctorAdd' C a b (a + b) rfl).app X).symm
  exact homIsZero_of_iso eX (Iso.refl Y) h

private lemma eqToHom_comp_family
    {I : Type*} {F G : I → C} (u : ∀ i, F i ⟶ G i)
    {i j : I} (h : i = j) :
    eqToHom (congrArg F h) ≫ u j ≫ eqToHom (congrArg G h.symm) = u i := by
  subst j
  simp

private lemma eqToHom_comp_binary
    {I : Type*} {F : I → C} (u : ∀ i j, F i ⟶ F j)
    {i i' j j' : I} (hi : i = i') (hj : j = j') :
    eqToHom (congrArg F hi) ≫ u i' j' ≫
        eqToHom (congrArg F hj.symm) = u i j := by
  subst i'
  subst j'
  simp

/-- Any map of length-one complexes extends to a map of chosen systems. -/
theorem postnikovSystemHom_exists_length_one
    {K K' : FinitePostnikovComplex C 1}
    (f : K ⟶ K') (P : PostnikovSystem K) (P' : PostnikovSystem K') :
    Nonempty (PostnikovSystemHom (P := P) (P' := P') f) := by
  let _ := (inferInstance : IsTriangulated C)
  let i₁ : Fin 2 := finitePostnikovSuccIndex (0 : Fin 1)
  have hidx : finitePostnikovIndex (0 : Fin 1) = finitePostnikovZeroIndex 1 := by
    apply Fin.ext
    rfl
  let eP : P.Y (finitePostnikovIndex (0 : Fin 1)) ≅ K.X (finitePostnikovIndex (0 : Fin 1)) :=
    eqToIso (congrArg P.Y hidx) ≪≫ P.baseIso ≪≫
      eqToIso (congrArg K.X hidx.symm)
  let eP' : P'.Y (finitePostnikovIndex (0 : Fin 1)) ≅ K'.X (finitePostnikovIndex (0 : Fin 1)) :=
    eqToIso (congrArg P'.Y hidx) ≪≫ P'.baseIso ≪≫
      eqToIso (congrArg K'.X hidx.symm)
  have heP : eP.hom = P.toX (finitePostnikovIndex (0 : Fin 1)) := by
    dsimp [eP]
    rw [P.baseIso_hom]
    exact eqToHom_comp_family P.toX hidx
  have heP' : eP'.hom = P'.toX (finitePostnikovIndex (0 : Fin 1)) := by
    dsimp [eP']
    rw [P'.baseIso_hom]
    exact eqToHom_comp_family P'.toX hidx
  let y₀ : P.Y (finitePostnikovIndex (0 : Fin 1)) ⟶ P'.Y (finitePostnikovIndex (0 : Fin 1)) :=
    eP.hom ≫ f.f (finitePostnikovIndex (0 : Fin 1)) ≫ eP'.inv
  have hcompat :
      P.fromX (0 : Fin 1) ≫ P.toX (finitePostnikovIndex (0 : Fin 1)) =
        finitePostnikovDifferential K 0 := by
    exact P.compatibility (0 : Fin 1)
  have hcompat' :
      P'.fromX (0 : Fin 1) ≫ P'.toX (finitePostnikovIndex (0 : Fin 1)) =
        finitePostnikovDifferential K' 0 := by
    exact P'.compatibility (0 : Fin 1)
  have hchain :
      finitePostnikovDifferential K 0 ≫ f.f (finitePostnikovIndex (0 : Fin 1)) =
        f.f i₁ ≫ finitePostnikovDifferential K' 0 := by
    simpa [finitePostnikovDifferential, i₁] using
      f.comm' i₁ (finitePostnikovIndex (0 : Fin 1)) (by
        dsimp [finitePostnikovShape, i₁]
        rfl)
  have hcomm :
      P.fromX (0 : Fin 1) ≫ y₀ = f.f i₁ ≫ P'.fromX (0 : Fin 1) := by
    apply (cancel_mono eP'.hom).1
    dsimp [y₀]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id, Category.comp_id]
    rw [heP, ← Category.assoc, hcompat, hchain, ← hcompat', ← heP']
  let T := postnikovTriangle P (0 : Fin 1)
  let T' := postnikovTriangle P' (0 : Fin 1)
  obtain ⟨y₁, hy₁, hy₃⟩ := complete_distinguished_triangle_morphism₁
    T T' (P.distinguished (0 : Fin 1)) (P'.distinguished (0 : Fin 1))
    (f.f i₁) y₀ hcomm
  dsimp [T, T', postnikovTriangle] at y₁ hy₁ hy₃
  change P.Y (finitePostnikovSuccIndex (0 : Fin 1)) ⟶
      P'.Y (finitePostnikovSuccIndex (0 : Fin 1)) at y₁
  change P.toX (finitePostnikovSuccIndex (0 : Fin 1)) ≫ f.f i₁ =
      y₁ ≫ P'.toX (finitePostnikovSuccIndex (0 : Fin 1)) at hy₁
  have hzero : (0 : Fin 2) = finitePostnikovIndex (0 : Fin 1) := by
    apply Fin.ext
    rfl
  have hs : i₁ = Fin.succ (0 : Fin 1) := by
    apply Fin.ext
    rfl
  let yzero : P.Y (0 : Fin 2) ⟶ P'.Y (0 : Fin 2) :=
    eqToHom (congrArg P.Y hzero) ≫ y₀ ≫
      eqToHom (congrArg P'.Y hzero.symm)
  let hk_of (k : Fin 1) : i₁ = Fin.succ k := by
    have hk0 : k = 0 := Fin.eq_zero k
    subst k
    exact hs
  let ys : ∀ k : Fin 1, P.Y (Fin.succ k) ⟶ P'.Y (Fin.succ k) := fun k =>
    eqToHom (congrArg P.Y (hk_of k).symm) ≫ y₁ ≫
      eqToHom (congrArg P'.Y (hk_of k))
  let y : ∀ i, P.Y i ⟶ P'.Y i := Fin.cases yzero ys
  have hy_zero : y (0 : Fin 2) =
      eqToHom (congrArg P.Y hzero) ≫ y₀ ≫
        eqToHom (congrArg P'.Y hzero.symm) := by
    dsimp [y, yzero]
  have hy_succ : y i₁ = y₁ := by
    have hy_one : y (Fin.succ (0 : Fin 1)) =
        eqToHom (congrArg P.Y hs.symm) ≫ y₁ ≫
          eqToHom (congrArg P'.Y hs) := by
      calc
        y (Fin.succ (0 : Fin 1)) = ys 0 := by
          change Fin.cases yzero ys (Fin.succ (0 : Fin 1)) = ys 0
          rfl
        _ = eqToHom (congrArg P.Y hs.symm) ≫ y₁ ≫
            eqToHom (congrArg P'.Y hs) := by
          dsimp [ys, hk_of]
    have hy_family := eqToHom_comp_family y hs
    calc
      y i₁ = eqToHom (congrArg P.Y hs) ≫
          y (Fin.succ (0 : Fin 1)) ≫
            eqToHom (congrArg P'.Y hs.symm) := hy_family.symm
      _ = eqToHom (congrArg P.Y hs) ≫
          (eqToHom (congrArg P.Y hs.symm) ≫ y₁ ≫
            eqToHom (congrArg P'.Y hs)) ≫
              eqToHom (congrArg P'.Y hs.symm) := by rw [hy_one]
      _ = y₁ := by simp
  have hy_index : y (finitePostnikovIndex (0 : Fin 1)) = y₀ := by
    have hy_family := eqToHom_comp_family y hzero
    apply (cancel_mono (eqToHom (congrArg P'.Y hzero.symm))).1
    apply (cancel_epi (eqToHom (congrArg P.Y hzero))).1
    exact hy_family.trans hy_zero
  let tm : ∀ i : Fin 1, postnikovTriangle P i ⟶ postnikovTriangle P' i := fun i =>
    Fin.cases
      (Triangle.homMk T T' y₁ (f.f i₁) y₀ hy₁
        (by
          change P.fromX (0 : Fin 1) ≫ y₀ = f.f i₁ ≫ P'.fromX (0 : Fin 1)
          exact hcomm) hy₃)
      (fun j => Fin.elim0 j) i
  refine ⟨⟨y, ?_, tm, ?_, ?_, ?_⟩⟩
  · intro i
    fin_cases i
    · change P.toX (0 : Fin 2) ≫ f.f 0 = y 0 ≫ P'.toX 0
      rw [hy_zero]
      dsimp [y₀]
      have hP0 := eqToHom_comp_family P.toX hzero
      have hP'0 := eqToHom_comp_family P'.toX hzero
      have hf0 := eqToHom_comp_family f.f hzero
      rw [← hP0, ← hf0, ← hP'0, ← heP, ← heP']
      simp [Category.assoc]
    · change P.toX (1 : Fin 2) ≫ f.f 1 = y 1 ≫ P'.toX 1
      have hs : (1 : Fin 2) = i₁ := by
        dsimp [i₁]
        rfl
      rw [hs]
      rw [hy_succ]
      simpa [T, T', i₁, postnikovTriangle] using hy₁
  · intro i
    fin_cases i
    dsimp [tm]
    exact hy_succ.symm
  · intro i
    fin_cases i
    dsimp [tm]
    rfl
  · intro i
    fin_cases i
    dsimp [tm]
    exact hy_index.symm

/-- The source's warning that length-one extensions need not be unique. -/
def HasLengthOnePostnikovExtensionNonuniqueness : Prop :=
  ∃ (K K' : FinitePostnikovComplex C 1) (f : K ⟶ K')
    (P : PostnikovSystem K) (P' : PostnikovSystem K')
    (φ ψ : PostnikovSystemHom (P := P) (P' := P') f),
    φ ≠ ψ

/-- Existence of a Postnikov system for a complex of length two. -/
theorem postnikovSystem_exists_length_two
    (K : FinitePostnikovComplex C 2) :
    Nonempty (PostnikovSystem K) := by
  classical
  let e : ∀ i : Fin 2, Fin 3 := fun i => ⟨i.val, by omega⟩
  let d01 : ∀ i j : Fin 2, K.X (e i) ⟶ K.X (e j) := fun i j =>
    if h : finitePostnikovShape 1 |>.Rel i j then
      K.d (e i) (e j)
    else 0
  let K01 : FinitePostnikovComplex C 1 :=
    { X := fun i => K.X (e i)
      d := d01
      shape := by
        intro i j hij
        dsimp [d01]
        exact if_neg hij
      d_comp_d' := by
        intro i j k hij hjk
        have hij' : j.val + 1 = i.val := hij
        have hjk' : k.val + 1 = j.val := hjk
        omega }
  obtain ⟨P01⟩ := postnikovSystem_exists_length_one K01
  have he0 : e (finitePostnikovIndex (0 : Fin 1)) =
      finitePostnikovIndex (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have he1 : e (finitePostnikovSuccIndex (0 : Fin 1)) =
      finitePostnikovIndex (1 : Fin 2) := by
    apply Fin.ext
    rfl
  have hd01 : d01 (finitePostnikovSuccIndex (0 : Fin 1))
      (finitePostnikovIndex (0 : Fin 1)) =
      K.d (e (finitePostnikovSuccIndex (0 : Fin 1)))
        (e (finitePostnikovIndex (0 : Fin 1))) := by
    dsimp [d01]
    rw [if_pos (show (finitePostnikovShape 1).Rel
      (finitePostnikovSuccIndex (0 : Fin 1))
      (finitePostnikovIndex (0 : Fin 1)) by rfl)]
  let d21 : K.X (finitePostnikovSuccIndex (1 : Fin 2)) ⟶
      K.X (finitePostnikovIndex (1 : Fin 2)) :=
    finitePostnikovDifferential K (1 : Fin 2)
  let d21' : K.X (finitePostnikovSuccIndex (1 : Fin 2)) ⟶
      K01.X (finitePostnikovSuccIndex (0 : Fin 1)) :=
    d21 ≫ eqToHom (congrArg K.X he1.symm)
  have hd21 : d21' ≫ P01.fromX (0 : Fin 1) = 0 := by
    letI : IsIso (P01.toX (finitePostnikovIndex (0 : Fin 1))) := by
      have hzero : finitePostnikovIndex (0 : Fin 1) =
          finitePostnikovZeroIndex 1 := by
        apply Fin.ext
        change (0 : ℕ) = 0
        rfl
      rw [hzero, ← P01.baseIso_hom]
      infer_instance
    letI : IsIso (eqToHom (congrArg K.X he0)) := inferInstance
    apply (cancel_mono (P01.toX (finitePostnikovIndex (0 : Fin 1)))).1
    have hcomp := K.d_comp_d
      (finitePostnikovSuccIndex (1 : Fin 2))
      (finitePostnikovIndex (1 : Fin 2))
      (finitePostnikovIndex (0 : Fin 2))
    rw [Category.assoc, P01.compatibility]
    simp only [zero_comp]
    apply (cancel_mono (eqToHom (congrArg K.X he0))).1
    dsimp [finitePostnikovDifferential, K01, d01]
    rw [if_pos (show (finitePostnikovShape 1).Rel
      (finitePostnikovSuccIndex (0 : Fin 1))
      (finitePostnikovIndex (0 : Fin 1)) by rfl)]
    dsimp [d21', d21]
    simp only [Category.assoc, zero_comp]
    rw [eqToHom_comp_binary K.d he1.symm he0.symm]
    exact hcomp
  let T01 := postnikovTriangle P01 (0 : Fin 1)
  have hT01 : T01 ∈ distTriang C := P01.distinguished (0 : Fin 1)
  obtain ⟨α, hα⟩ := T01.coyoneda_exact₂ hT01 d21' hd21
  obtain ⟨Y₂, u₂, v₂, hT₂⟩ := distinguished_cocone_triangle₁ α
  let Y : Fin 3 → C := fun j =>
    Fin.cases (P01.Y (finitePostnikovIndex (0 : Fin 1)))
      (fun k => Fin.cases (P01.Y (finitePostnikovSuccIndex (0 : Fin 1)))
        (fun _ => Y₂) k) j
  have hY0 : Y (finitePostnikovIndex (0 : Fin 2)) =
      P01.Y (finitePostnikovIndex (0 : Fin 1)) := by rfl
  have hY1 : Y (finitePostnikovIndex (1 : Fin 2)) =
      P01.Y (finitePostnikovSuccIndex (0 : Fin 1)) := by rfl
  have hY2 : Y (finitePostnikovLastIndex 2) = Y₂ := by rfl
  have hidx1 : finitePostnikovSuccIndex (0 : Fin 2) =
      finitePostnikovIndex (1 : Fin 2) := by
    apply Fin.ext
    rfl
  have he1s : e (finitePostnikovSuccIndex (0 : Fin 1)) =
      finitePostnikovSuccIndex (0 : Fin 2) :=
    he1.trans hidx1.symm
  have hY1s : Y (finitePostnikovSuccIndex (0 : Fin 2)) =
      P01.Y (finitePostnikovSuccIndex (0 : Fin 1)) :=
    (congrArg Y hidx1).trans hY1
  have hsucc2 : finitePostnikovSuccIndex (1 : Fin 2) =
      finitePostnikovLastIndex 2 := by
    apply Fin.ext
    rfl
  have hidx2 : finitePostnikovSuccIndex (1 : Fin 2) =
      Fin.succ (Fin.succ (0 : Fin 1)) := by rfl
  have hss : Fin.succ (Fin.succ (0 : Fin 1)) =
      finitePostnikovLastIndex 2 := by rfl
  have hY2s : Y (finitePostnikovSuccIndex (1 : Fin 2)) = Y₂ :=
    (congrArg Y hsucc2).trans hY2
  have hY2ss : Y (Fin.succ (Fin.succ (0 : Fin 1))) = Y₂ := by rfl
  have hzero : finitePostnikovZeroIndex 2 =
      finitePostnikovIndex (0 : Fin 2) := by
    apply Fin.ext
    dsimp [finitePostnikovZeroIndex, finitePostnikovIndex]
  have hYzero : Y (finitePostnikovZeroIndex 2) =
      P01.Y (finitePostnikovIndex (0 : Fin 1)) :=
    (congrArg Y hzero).trans hY0
  have hezero : e (finitePostnikovIndex (0 : Fin 1)) =
      finitePostnikovZeroIndex 2 := by
    apply Fin.ext
    omega
  have hzero1 : finitePostnikovZeroIndex 1 =
      finitePostnikovIndex (0 : Fin 1) := by
    apply Fin.ext
    dsimp [finitePostnikovZeroIndex, finitePostnikovIndex]
  have hYzeroA : Y (finitePostnikovZeroIndex 2) =
      P01.Y (finitePostnikovZeroIndex 1) :=
    hYzero.trans (congrArg P01.Y hzero1.symm)
  have hezeroA : e (finitePostnikovZeroIndex 1) =
      finitePostnikovZeroIndex 2 :=
    (congrArg e hzero1).trans hezero
  let toX : ∀ j, Y j ⟶ K.X j := fun j =>
    Fin.cases
      (eqToHom hYzeroA ≫ P01.toX (finitePostnikovZeroIndex 1) ≫
        eqToHom (congrArg K.X hezeroA))
      (fun k => Fin.cases
        (eqToHom hY1 ≫ P01.toX (finitePostnikovSuccIndex (0 : Fin 1)) ≫
          eqToHom (congrArg K.X he1))
        (fun l => by
          have hl : l = (0 : Fin 1) := Fin.ext (by omega)
          subst l
          exact eqToHom hY2ss ≫ u₂ ≫
            eqToHom (congrArg K.X hidx2)) k) j
  let fromX : ∀ i : Fin 2, K.X (finitePostnikovSuccIndex i) ⟶
      Y (finitePostnikovIndex i) := fun i =>
    Fin.cases
      (eqToHom (congrArg K.X he1s.symm) ≫ P01.fromX (0 : Fin 1) ≫
        eqToHom hY0.symm)
      (fun k => by
        have hk : k = (0 : Fin 1) := Fin.ext (by omega)
        subst k
        exact α ≫ eqToHom hY1.symm) i
  let connecting : ∀ i : Fin 2, Y (finitePostnikovIndex i) ⟶
      (shiftFunctor C (1 : ℤ)).obj (Y (finitePostnikovSuccIndex i)) := fun i =>
    Fin.cases
      (eqToHom hY0 ≫ P01.connecting (0 : Fin 1) ≫
        (shiftFunctor C (1 : ℤ)).map (eqToHom hY1s.symm))
      (fun k => by
        have hk : k = (0 : Fin 1) := Fin.ext (by omega)
        subst k
        exact eqToHom hY1 ≫ v₂ ≫
          (shiftFunctor C (1 : ℤ)).map (eqToHom hY2s.symm)) i
  let baseIso : Y (finitePostnikovZeroIndex 2) ≅
      K.X (finitePostnikovZeroIndex 2) :=
    eqToIso hYzeroA ≪≫ P01.baseIso ≪≫ eqToIso (congrArg K.X hezeroA)
  have hbase : baseIso.hom = toX (finitePostnikovZeroIndex 2) := by
    dsimp [baseIso, toX, Iso.trans]
    change eqToHom hYzeroA ≫ P01.baseIso.hom ≫
        eqToHom (congrArg K.X hezeroA) =
      eqToHom hYzeroA ≫ P01.toX (finitePostnikovZeroIndex 1) ≫
        eqToHom (congrArg K.X hezeroA)
    rw [P01.baseIso_hom]
  have htoX1 : toX (finitePostnikovSuccIndex (0 : Fin 2)) =
      eqToHom hY1s ≫ P01.toX (finitePostnikovSuccIndex (0 : Fin 1)) ≫
        eqToHom (congrArg K.X he1s) := by
    rfl
  have hY1T : Y (finitePostnikovIndex (1 : Fin 2)) = T01.obj₁ := by
    simpa [T01, postnikovTriangle] using hY1
  have hY1Ts : Y (finitePostnikovIndex (Fin.succ (0 : Fin 1))) = T01.obj₁ := by
    simpa using hY1T
  have hY2Ts : Y (finitePostnikovSuccIndex (Fin.succ (0 : Fin 1))) = Y₂ := by
    simpa using hY2s
  have htoX_general (j : Fin 3)
      (hj : j = Fin.succ (Fin.succ (0 : Fin 1))) :
      toX j =
        eqToHom (congrArg Y hj) ≫ eqToHom hY2ss ≫ u₂ ≫
          eqToHom (congrArg K.X
            (hidx2.trans hj.symm)) := by
    subst j
    change Fin.cases _
      (fun k => Fin.cases _
        (fun l => by
          have hl : l = (0 : Fin 1) := Fin.ext (by omega)
          subst l
          exact eqToHom hY2ss ≫ u₂ ≫
            eqToHom (congrArg K.X hidx2)) k)
      (Fin.succ (Fin.succ (0 : Fin 1))) =
      eqToHom (congrArg Y rfl) ≫ eqToHom hY2ss ≫ u₂ ≫
        eqToHom (congrArg K.X
          (hidx2.trans rfl))
    rw [Fin.cases_succ, Fin.cases_succ]
    have hidx2eq : hidx2.trans rfl = hidx2 := Subsingleton.elim _ _
    rw [hidx2eq]
    simp [Category.assoc, eqToHom_trans]
  have hY2to : Y (finitePostnikovSuccIndex (1 : Fin 2)) = Y₂ :=
    (congrArg Y hidx2).trans hY2ss
  have hK2to : finitePostnikovSuccIndex (1 : Fin 2) =
      finitePostnikovSuccIndex (1 : Fin 2) :=
    hidx2.trans hidx2.symm
  have hj1 : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by rfl
  have hY2target : Y₂ =
      Y (finitePostnikovSuccIndex (1 : Fin 2)) :=
    hY2Ts.symm.trans
      (congrArg Y ((congrArg finitePostnikovSuccIndex hj1).symm))
  have hfromX_general (j : Fin 2)
      (hj : j = Fin.succ (0 : Fin 1)) :
      fromX j =
        eqToHom (congrArg (fun q => K.X (finitePostnikovSuccIndex q)) hj) ≫
          α ≫ eqToHom hY1Ts.symm ≫
            eqToHom (congrArg Y ((congrArg finitePostnikovIndex hj).symm)) := by
    subst j
    change @Fin.cases 1
      (fun i : Fin 2 => K.X (finitePostnikovSuccIndex i) ⟶
        Y (finitePostnikovIndex i))
      (eqToHom (congrArg K.X he1s.symm) ≫ P01.fromX (0 : Fin 1) ≫
        eqToHom hY0.symm)
      (fun k => by
        have hk : k = (0 : Fin 1) := Fin.ext (by omega)
        subst k
        exact α ≫ eqToHom hY1Ts.symm)
      (Fin.succ (0 : Fin 1)) =
      eqToHom (congrArg (fun q => K.X (finitePostnikovSuccIndex q)) rfl) ≫
        α ≫ eqToHom hY1Ts.symm ≫ eqToHom (congrArg Y rfl)
    rw [Fin.cases_succ]
    simp [eqToHom_trans]
  have hfromX1 : fromX (1 : Fin 2) =
      α ≫ eqToHom hY1T.symm := by
    simpa [eqToHom_trans] using
      hfromX_general (1 : Fin 2) (by rfl)
  have hconnecting_general (j : Fin 2)
      (hj : j = Fin.succ (0 : Fin 1)) :
      connecting j =
        eqToHom (congrArg Y (congrArg finitePostnikovIndex hj)) ≫
          eqToHom hY1Ts ≫ v₂ ≫
            (shiftFunctor C (1 : ℤ)).map (eqToHom
              (hY2Ts.symm.trans
                (congrArg Y ((congrArg finitePostnikovSuccIndex hj).symm)))) := by
    subst j
    change Fin.cases
      _
      (fun k => by
        have hk : k = (0 : Fin 1) := Fin.ext (by omega)
        subst k
        exact eqToHom hY1Ts ≫ v₂ ≫
          (shiftFunctor C (1 : ℤ)).map (eqToHom hY2Ts.symm))
      (Fin.succ (0 : Fin 1)) =
      eqToHom (congrArg Y rfl) ≫ eqToHom hY1Ts ≫ v₂ ≫
        (shiftFunctor C (1 : ℤ)).map (eqToHom
          (hY2Ts.symm.trans (congrArg Y rfl)))
    rw [Fin.cases_succ]
    simp [eqToHom_trans]
  refine ⟨{ Y := Y, toX := toX, baseIso := baseIso, baseIso_hom := hbase, fromX := fromX, connecting := connecting, distinguished := ?_, compatibility := ?_ }⟩
  · intro i
    fin_cases i
    · let e₁ : Y (finitePostnikovSuccIndex (0 : Fin 2)) ≅
          T01.obj₁ := eqToIso hY1s
      let e₂ : K.X (finitePostnikovSuccIndex (0 : Fin 2)) ≅
          T01.obj₂ := eqToIso (congrArg K.X he1s.symm)
      let e₃ : Y (finitePostnikovIndex (0 : Fin 2)) ≅
          T01.obj₃ := eqToIso hY0
      apply isomorphic_distinguished _ hT01 _
        (Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_)
      · dsimp [Triangle.mk, e₁, e₂]
        change toX (finitePostnikovSuccIndex (0 : Fin 2)) ≫
            eqToHom (congrArg K.X he1s.symm) =
          eqToHom hY1s ≫ P01.toX (finitePostnikovSuccIndex (0 : Fin 1))
        rw [htoX1]
        simp [Category.assoc, eqToHom_trans]
      · dsimp [Triangle.mk, e₂, e₃]
        change fromX (0 : Fin 2) ≫ eqToHom hY0 =
          eqToHom (congrArg K.X he1s.symm) ≫ P01.fromX (0 : Fin 1)
        simp [fromX, Category.assoc, eqToHom_trans]
      · dsimp [Triangle.mk, e₁, e₃]
        change connecting (0 : Fin 2) ≫
            (shiftFunctor C (1 : ℤ)).map (eqToHom hY1s) =
          eqToHom hY0 ≫ T01.mor₃
        dsimp [connecting]
        have hcancel :
            (shiftFunctor C (1 : ℤ)).map (eqToHom hY1s.symm) ≫
                (shiftFunctor C (1 : ℤ)).map (eqToHom hY1s) =
              𝟙 ((shiftFunctor C (1 : ℤ)).obj
                (P01.Y (finitePostnikovSuccIndex (0 : Fin 1)))) := by
          rw [← Functor.map_comp]
          simp [eqToHom_trans]
        simp only [Category.assoc]
        rw [hcancel]
        simp only [Category.comp_id]
        change eqToHom hY0 ≫ P01.connecting (0 : Fin 1) =
          eqToHom hY0 ≫ P01.connecting (0 : Fin 1)
        rfl
    · let e₁ : Y (finitePostnikovSuccIndex (1 : Fin 2)) ≅ Y₂ :=
          eqToIso hY2target.symm
      let e₂ : K.X (finitePostnikovSuccIndex (1 : Fin 2)) ≅
          K.X (finitePostnikovSuccIndex (1 : Fin 2)) :=
        eqToIso (congrArg K.X hK2to)
      let e₃ : Y (finitePostnikovIndex (1 : Fin 2)) ≅
          T01.obj₁ := eqToIso hY1Ts
      apply isomorphic_distinguished _ hT₂ _
        (Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_)
      · dsimp [Triangle.mk, e₁, e₂]
        rw [htoX_general (finitePostnikovSuccIndex (1 : Fin 2)) hidx2]
        simp [Category.assoc, eqToHom_trans]
      · dsimp [Triangle.mk, e₂, e₃]
        rw [hfromX1]
        simp [Category.assoc, eqToHom_trans]
      · dsimp [Triangle.mk, e₁, e₃]
        rw [hconnecting_general (1 : Fin 2) hj1]
        cases hY2target
        simp only [Category.assoc]
        rw [← Functor.map_comp]
        simp [eqToHom_trans]
  · intro i
    fin_cases i
    · change fromX (0 : Fin 2) ≫
          toX (finitePostnikovIndex (0 : Fin 2)) =
        finitePostnikovDifferential K (0 : Fin 2)
      have hfromX0 : fromX (0 : Fin 2) =
          eqToHom (congrArg K.X he1s.symm) ≫ P01.fromX (0 : Fin 1) ≫
            eqToHom hY0.symm := by
        rfl
      have hYzeroB : Y (finitePostnikovIndex (0 : Fin 2)) =
          P01.Y (finitePostnikovIndex (0 : Fin 1)) :=
        (congrArg Y hzero.symm).trans hYzero
      have htoX0 : toX (finitePostnikovIndex (0 : Fin 2)) =
          eqToHom hYzeroB ≫ P01.toX (finitePostnikovIndex (0 : Fin 1)) ≫
            eqToHom (congrArg K.X he0) := by
        cases hzero
        rfl
      rw [hfromX0, htoX0]
      simp only [Category.assoc]
      have hYcancel :
          eqToHom hY0.symm ≫ eqToHom hYzeroB =
            𝟙 (P01.Y (finitePostnikovIndex (0 : Fin 1))) := by
        have hp : hY0.symm.trans hYzeroB = (rfl :
            P01.Y (finitePostnikovIndex (0 : Fin 1)) =
              P01.Y (finitePostnikovIndex (0 : Fin 1))) := by
          apply Subsingleton.elim
        rw [eqToHom_trans, hp, eqToHom_refl]
      simp only [← Category.assoc, hYcancel, Category.id_comp,
        Category.comp_id]
      simp only [Category.assoc]
      rw [← Category.assoc (P01.fromX (0 : Fin 1))
        (P01.toX (finitePostnikovIndex (0 : Fin 1)))]
      rw [P01.compatibility (0 : Fin 1)]
      dsimp [finitePostnikovDifferential, K01, d01]
      rw [if_pos (show (finitePostnikovShape 1).Rel
        (finitePostnikovSuccIndex (0 : Fin 1))
        (finitePostnikovIndex (0 : Fin 1)) by rfl)]
      exact eqToHom_comp_binary K.d he1s.symm he0.symm
    · change fromX (1 : Fin 2) ≫
          toX (finitePostnikovIndex (1 : Fin 2)) =
        finitePostnikovDifferential K (1 : Fin 2)
      have htoX1' : toX (finitePostnikovIndex (1 : Fin 2)) =
          eqToHom hY1T ≫ P01.toX (finitePostnikovSuccIndex (0 : Fin 1)) ≫
            eqToHom (congrArg K.X he1) := by
        cases hY1T
        rfl
      have hα' : d21' =
          α ≫ P01.toX (finitePostnikovSuccIndex (0 : Fin 1)) := by
        change d21' =
          α ≫ P01.toX (finitePostnikovSuccIndex (0 : Fin 1)) at hα
        exact hα
      rw [hfromX1, htoX1']
      simp only [Category.assoc]
      have hY1cancel :
          eqToHom hY1T.symm ≫ eqToHom hY1T =
            𝟙 T01.obj₁ := by
        have hp : hY1T.symm.trans hY1T = (rfl :
            T01.obj₁ = T01.obj₁) := by
          apply Subsingleton.elim
        rw [eqToHom_trans, hp, eqToHom_refl]
      simp only [← Category.assoc, hY1cancel, Category.id_comp,
        Category.comp_id]
      change α ≫ P01.toX (finitePostnikovSuccIndex (0 : Fin 1)) ≫
          eqToHom (congrArg K.X he1) =
        finitePostnikovDifferential K (1 : Fin 2)
      rw [← Category.assoc α
        (P01.toX (finitePostnikovSuccIndex (0 : Fin 1)))]
      rw [← hα']
      dsimp [d21']
      simp
      rfl

/-- The source's warning that length-two maps need not extend is represented
by the exact existential failure predicate; no particular counterexample is
specified in the source section. -/
def HasLengthTwoPostnikovExtensionFailure : Prop :=
  ∃ (K K' : FinitePostnikovComplex C 2) (f : K ⟶ K')
    (P : PostnikovSystem K) (P' : PostnikovSystem K'),
    ¬ Nonempty (PostnikovSystemHom (P := P) (P' := P') f)

/-- The source's warning that existence can fail beyond length two. -/
def HasPostnikovExistenceFailure (n : ℕ) : Prop :=
  ∃ K : FinitePostnikovComplex C n, ¬ Nonempty (PostnikovSystem K)

/-- The source's warning that, for every length greater than two, existence
can fail for some complex. -/
def HasPostnikovExistenceFailureBeyondTwo : Prop :=
  ∀ n : ℕ, 2 < n → HasPostnikovExistenceFailure (C := C) n

/-! ## Vanishing hypotheses for maps of Postnikov systems -/

/-- The vanishing condition labelled `(P)` in the source. -/
def PostnikovVanishing
    {n : ℕ} (K K' : FinitePostnikovComplex C n) : Prop :=
  ∀ (i j : Fin (n + 1)), j.val + 1 < i.val →
    HomIsZero
      ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 1)).obj (K.X i))
      (K'.X j)

/-- The shifted vanishing statement obtained for the `Y'_j`. -/
theorem postnikovSystem_vanishing_to_Y
    {n : ℕ} {K K' : FinitePostnikovComplex C n}
    (P' : PostnikovSystem K')
    (hP : PostnikovVanishing K K') :
    ∀ (i j : Fin (n + 1)), j.val + 1 < i.val →
      HomIsZero
        ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 1)).obj (K.X i))
        (P'.Y j) := by
  intro i j hij
  induction j using Fin.induction with
  | zero =>
      let hzero := hP i (finitePostnikovZeroIndex n) (by simpa [finitePostnikovZeroIndex] using hij)
      have hidx0 : finitePostnikovZeroIndex n = (0 : Fin (n + 1)) := by
        apply Fin.ext
        rfl
      cases hidx0
      intro f
      apply (cancel_mono P'.baseIso.hom).1
      rw [P'.baseIso_hom]
      calc
        f ≫ P'.toX (finitePostnikovZeroIndex n) = 0 :=
          hzero (f ≫ P'.toX (finitePostnikovZeroIndex n))
        _ = 0 ≫ P'.toX (finitePostnikovZeroIndex n) := by rw [zero_comp]
  | succ j ih =>
      let T := postnikovTriangle P' j
      have hT : T ∈ distTriang C := P'.distinguished j
      change j.val + 2 < i.val at hij
      have hij' : j.val + 2 < i.val := by simpa using hij
      have hto₀ := ih (by
        change j.val + 1 < i.val
        omega)
      have hidx : finitePostnikovIndex j = j.castSucc := by
        apply Fin.ext
        rfl
      have hto : HomIsZero
          ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 1)).obj (K.X i))
          (P'.Y (finitePostnikovIndex j)) := by
        rw [hidx]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hto₀
      have hto' : HomIsZero
          ((shiftFunctor C (1 : ℤ)).obj
            ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 2)).obj (K.X i)))
          (P'.Y (finitePostnikovIndex j)) := by
        exact homIsZero_shift_add_left (i.val - j.val - 2 : ℤ) 1
          (by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hto)
      have hprev : HomIsZero
          ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 2)).obj (K.X i))
          ((shiftFunctor C (-1 : ℤ)).obj (P'.Y (finitePostnikovIndex j))) :=
        homIsZero_shift_of_neg 1 (-1) (by omega) hto'
      have hprev' : HomIsZero
          ((shiftFunctor C ((i.val : ℤ) - ((Fin.succ j).val : ℤ) - 1)).obj (K.X i))
          (Triangle.invRotate T).obj₁ := by
        have hobj : (Triangle.invRotate T).obj₁ =
            (shiftFunctor C (-1 : ℤ)).obj (P'.Y (finitePostnikovIndex j)) := by
          change (shiftFunctor C (-1 : ℤ)).obj T.obj₃ = _
          simp [T, postnikovTriangle, hidx]
        rw [hobj]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hprev
      intro f
      have hcond : (finitePostnikovSuccIndex j).val + 1 < i.val := by
        change j.val + 2 < i.val
        exact hij'
      have hf : f ≫ T.mor₁ = 0 := by
        apply (hP i (finitePostnikovSuccIndex j) hcond)
      obtain ⟨g, hg⟩ := (Triangle.invRotate T).coyoneda_exact₂
        (inv_rot_of_distTriang _ hT) f hf
      rw [hg, hprev' g]
      simp only [zero_comp]
      rfl

private theorem postnikovSystem_exists_vanishing_to_Y
    {n : ℕ} {K K' : FinitePostnikovComplex C n}
    (P' : PostnikovSystem K')
    (hK : ∀ (i j : Fin (n + 1)), j.val + 2 < i.val →
      HomIsZero
        ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 2)).obj (K.X i))
        (K'.X j)) :
    ∀ (i j : Fin (n + 1)), j.val + 2 < i.val →
      HomIsZero
        ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 2)).obj (K.X i))
        (P'.Y j) := by
  intro i j hij
  induction j using Fin.induction with
  | zero =>
      let hzero := hK i (finitePostnikovZeroIndex n)
        (by simpa [finitePostnikovZeroIndex] using hij)
      have hidx0 : finitePostnikovZeroIndex n = (0 : Fin (n + 1)) := by
        apply Fin.ext
        rfl
      cases hidx0
      intro f
      apply (cancel_mono P'.baseIso.hom).1
      rw [P'.baseIso_hom]
      calc
        f ≫ P'.toX (finitePostnikovZeroIndex n) = 0 :=
          hzero (f ≫ P'.toX (finitePostnikovZeroIndex n))
        _ = 0 ≫ P'.toX (finitePostnikovZeroIndex n) := by rw [zero_comp]
  | succ j ih =>
      let T := postnikovTriangle P' j
      have hT : T ∈ distTriang C := P'.distinguished j
      change j.val + 3 < i.val at hij
      have hij' : j.val + 3 < i.val := by simpa using hij
      have hto₀ := ih (by
        change j.val + 2 < i.val
        omega)
      have hidx : finitePostnikovIndex j = j.castSucc := by
        apply Fin.ext
        rfl
      have hto : HomIsZero
          ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 2)).obj (K.X i))
          (P'.Y (finitePostnikovIndex j)) := by
        rw [hidx]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hto₀
      have hto' : HomIsZero
          ((shiftFunctor C (1 : ℤ)).obj
            ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 3)).obj (K.X i)))
          (P'.Y (finitePostnikovIndex j)) := by
        exact homIsZero_shift_add_left (i.val - j.val - 3 : ℤ) 1
          (by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hto)
      have hprev : HomIsZero
          ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 3)).obj (K.X i))
          ((shiftFunctor C (-1 : ℤ)).obj (P'.Y (finitePostnikovIndex j))) :=
        homIsZero_shift_of_neg 1 (-1) (by omega) hto'
      have hprev' : HomIsZero
          ((shiftFunctor C ((i.val : ℤ) - ((Fin.succ j).val : ℤ) - 2)).obj (K.X i))
          (Triangle.invRotate T).obj₁ := by
        have hobj : (Triangle.invRotate T).obj₁ =
            (shiftFunctor C (-1 : ℤ)).obj (P'.Y (finitePostnikovIndex j)) := by
          change (shiftFunctor C (-1 : ℤ)).obj T.obj₃ = _
          simp [T, postnikovTriangle, hidx]
        rw [hobj]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hprev
      intro f
      obtain ⟨g, hg⟩ := (Triangle.invRotate T).coyoneda_exact₂
        (inv_rot_of_distTriang _ hT) f (by
          have hf := hK i (finitePostnikovSuccIndex j)
            (by
              simpa [finitePostnikovSuccIndex] using hij')
          change f ≫ P'.toX (finitePostnikovSuccIndex j) = 0
          exact hf _)
      rw [hg, hprev' g]
      simp only [zero_comp]
      rfl

/-- Under `(P)`, a map of complexes extends to a map of Postnikov systems. -/
theorem postnikovSystemHom_exists_of_vanishing
    {n : ℕ} {K K' : FinitePostnikovComplex C n}
    (f : K ⟶ K') (P : PostnikovSystem K) (P' : PostnikovSystem K')
    (hP : PostnikovVanishing K K') :
    Nonempty (PostnikovSystemHom (P := P) (P' := P') f) := by
  sorry

/-! ## The three uniqueness hypotheses -/

/-- The first uniqueness hypothesis in the source. -/
def PostnikovHomUniqueLeft
    {n : ℕ} (K K' : FinitePostnikovComplex C n)
    (P' : PostnikovSystem K') : Prop :=
  ∀ (i : Fin (n + 1)), 0 < i.val →
    HomIsZero
      ((shiftFunctor C (i.val : ℤ)).obj (K.X i))
      ((shiftFunctor C (n : ℤ)).obj (P'.Y (finitePostnikovLastIndex n)))

/-- The second uniqueness hypothesis in the source. -/
def PostnikovHomUniqueRight
    {n : ℕ} (K K' : FinitePostnikovComplex C n)
    (P : PostnikovSystem K) : Prop :=
  ∀ (i : Fin n),
    HomIsZero
      ((shiftFunctor C (n : ℤ)).obj (P.Y (finitePostnikovLastIndex n)))
      ((shiftFunctor C ((n - (i.val + 1) : ℕ) : ℤ)).obj
        (K'.X ⟨n - (i.val + 1), by omega⟩))

/-- The two-sided uniqueness hypothesis in the source. -/
def PostnikovHomUniqueTwoSided
    {n : ℕ} (K K' : FinitePostnikovComplex C n) : Prop :=
  ∀ (i : Fin n) (j : Fin (n + 1)) (hij : i.val + 1 ≤ j.val),
    HomIsZero
        ((shiftFunctor C (-((i.val + 1 : ℤ)) + 1)).obj
          (K.X (finitePostnikovSubIndex i j hij)))
        (K'.X j) ∧
      HomIsZero (K.X j)
        ((shiftFunctor C (-((i.val + 1 : ℤ)))).obj
          (K'.X (finitePostnikovSubIndex i j hij)))

/-- Under any one of the three source hypotheses, a map of Postnikov systems
is unique. -/
theorem postnikovSystemHom_unique_of_vanishing
    {n : ℕ} {K K' : FinitePostnikovComplex C n}
    (f : K ⟶ K') (P : PostnikovSystem K) (P' : PostnikovSystem K')
    (h : PostnikovHomUniqueLeft K K' P' ∨
      PostnikovHomUniqueRight K K' P ∨
      PostnikovHomUniqueTwoSided K K')
    (φ ψ : PostnikovSystemHom (P := P) (P' := P') f) :
    φ = ψ := by
  sorry

/-! ## Existence and uniqueness from vanishing of the complex terms -/

/-- The stronger vanishing condition used to construct a Postnikov system. -/
def PostnikovExistenceVanishing
    {n : ℕ} (K : FinitePostnikovComplex C n) : Prop :=
  ∀ (i j : Fin (n + 1)), j.val + 2 < i.val →
    HomIsZero
      ((shiftFunctor C ((i.val : ℤ) - (j.val : ℤ) - 2)).obj (K.X i))
      (K.X j)

/-- The stronger vanishing condition implies existence. -/
theorem postnikovSystem_exists_of_vanishing
    {n : ℕ} (K : FinitePostnikovComplex C n)
    (hK : PostnikovExistenceVanishing K) :
    Nonempty (PostnikovSystem K) := by
  sorry

/-- A pair of systems over the same complex is isomorphic when `(P)` holds. -/
theorem postnikovSystem_isomorphic_of_vanishing
    {n : ℕ} {K : FinitePostnikovComplex C n}
    (P P' : PostnikovSystem K)
    (hK : PostnikovVanishing K K) :
    Nonempty
      (PostnikovSystemIso (P := P) (P' := P') (𝟙 K)) := by
  sorry

/-! ## The abelian-category example and its homotopy colimit -/

/-- The chain complex obtained by embedding an `ℕ`-indexed chain complex into
the cochain complexes indexed by `ℤ`, with the `n`th term in degree `-n`. -/
noncomputable def chainComplexTotalization
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : ChainComplex A ℕ) : CochainComplex A ℤ :=
  (ComplexShape.embeddingDownNat.extendFunctor A).obj K

/- The source's finite complex keeps `A_n` itself at its left boundary.  The
project's Chapter 15 `stupidTruncGE` is the established strict-truncation
interface; the smart `truncGE` would replace that boundary by opcycles. -/
noncomputable def finiteChainTotalization
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : ChainComplex A ℕ) (n : ℕ) : CochainComplex A ℤ :=
  Formalization.Books.Homology.Unit15.CochainComplex.stupidTruncGE
    (chainComplexTotalization K) (-(n : ℤ))

/-- The chain complex of the terms `A_n` viewed in the derived category. -/
noncomputable def derivedChainComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (K : ChainComplex A ℕ) : ChainComplex (DerivedCategory A) ℕ where
  X n := (DerivedCategory.singleFunctor A 0).obj (K.X n)
  d i j := (DerivedCategory.singleFunctor A 0).map (K.d i j)
  shape i j hij := by
    rw [K.shape i j hij, Functor.map_zero]
  d_comp_d' i j k _ _ := by
    rw [← (DerivedCategory.singleFunctor A 0).map_comp, K.d_comp_d,
      Functor.map_zero]

/-- The finite derived object represented by the first `n + 1` terms of the
chain complex.  The strict segment has `A_n` in degree `-n`; shifting it by
`-n` gives the source's `(A_n → ⋯ → A_0)[-n]`. -/
noncomputable def abelianPostnikovTerm
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
  (K : ChainComplex A ℕ) (n : ℕ) : DerivedCategory A :=
  (shiftFunctor (DerivedCategory A) (-(n : ℤ))).obj
    ((DerivedCategory.Q (C := A)).obj (finiteChainTotalization K n))

/-- The infinite extension of the finite Postnikov-system structure. -/
structure InfinitePostnikovSystem
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ k : ℤ, (shiftFunctor D k).Additive]
    [Pretriangulated D] [IsTriangulated D]
    (K : ChainComplex D ℕ) where
  Y : ℕ → D
  toX : ∀ i, Y i ⟶ K.X i
  baseIso : Y 0 ≅ K.X 0
  baseIso_hom : baseIso.hom = toX 0
  fromX : ∀ i, K.X (i + 1) ⟶ Y i
  connecting : ∀ i, Y i ⟶ (shiftFunctor D (1 : ℤ)).obj (Y (i + 1))
  distinguished : ∀ i,
    Triangle.mk (toX (i + 1)) (fromX i) (connecting i) ∈ distTriang D
  compatibility : ∀ i, fromX i ≫ toX i = K.d (i + 1) i

/-- The triangle at stage `i` of an infinite Postnikov system. -/
def InfinitePostnikovSystem.triangle
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ k : ℤ, (shiftFunctor D k).Additive]
    [Pretriangulated D] [IsTriangulated D]
    {K : ChainComplex D ℕ} (P : InfinitePostnikovSystem K) (i : ℕ) :
    Triangle D :=
  Triangle.mk (P.toX (i + 1)) (P.fromX i) (P.connecting i)

/-- The transition map `Y_i[i] → Y_(i+1)[i+1]` in the infinite tower. -/
noncomputable def InfinitePostnikovSystem.totalizationTransition
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ k : ℤ, (shiftFunctor D k).Additive]
    [Pretriangulated D] [IsTriangulated D]
    {K : ChainComplex D ℕ} (P : InfinitePostnikovSystem K) (i : ℕ) :
    (shiftFunctor D (i : ℤ)).obj (P.Y i) ⟶
      (shiftFunctor D ((i + 1 : ℕ) : ℤ)).obj (P.Y (i + 1)) :=
  P.connecting i⟦(i : ℤ)⟧' ≫
    (shiftFunctorAdd' D (1 : ℤ) (i : ℤ) ((i + 1 : ℕ) : ℤ) (by omega)).inv.app
      (P.Y (i + 1))

/-- The sequential system of shifted `Y_i` appearing in the hocolim formula. -/
noncomputable def InfinitePostnikovSystem.totalizationSystem
    {D : Type u} [Category.{v} D] [AdditiveCategory D]
    [HasShift D ℤ] [∀ k : ℤ, (shiftFunctor D k).Additive]
    [Pretriangulated D] [IsTriangulated D]
    {K : ChainComplex D ℕ} (P : InfinitePostnikovSystem K) : ℕ ⥤ D :=
  Functor.ofSequence (fun i => P.totalizationTransition i)

/-- The precise data in the abelian-category example, including the
finite truncation description and its derived homotopy-colimit identity. -/
structure AbelianPostnikovExample
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    (K : ChainComplex A ℕ) where
  system : InfinitePostnikovSystem (derivedChainComplex K)
  Y_spec : ∀ n, Nonempty (system.Y n ≅ abelianPostnikovTerm K n)
  hocolim_spec :
    ∃ (hA : HasCountableCoproducts A) (hAB4 : @CountableAB4 A _ hA),
      letI : HasCountableCoproducts A := hA
      letI : CountableAB4 A := hAB4
      ∃ T : DerivedCategory A,
        IsDerivedColimit system.totalizationSystem T ∧
          Nonempty
            (T ≅ (DerivedCategory.Q (C := A)).obj (chainComplexTotalization K))

/-- The abelian chain-complex example from the source. -/
theorem exists_abelian_postnikov_example
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    (K : ChainComplex A ℕ) :
    Nonempty (AbelianPostnikovExample K) := by
  sorry


end Formalization.Books.Derived.Unit41
