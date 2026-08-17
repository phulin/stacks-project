import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.IndYoneda
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered

namespace Formalization.Books.Categories.Unit22

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21

open scoped DirectSum
open scoped ZeroObject

universe u v u' v' w w'

noncomputable section

/-! # 22. Essentially constant systems

The source distinguishes a filtered cocone which is essentially constant from the
stronger condition that all sufficiently late transition maps are isomorphisms.
The definitions below retain the chosen cocone or cone, since that is the data
used by the factorization condition in the book.
-/

/-- A filtered diagram is ind-essentially constant with respect to a cocone. -/
def IsEssentiallyConstantInd
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] [IsFiltered I]
    (M : I ⥤ C) (c : Cocone M) : Prop :=
  ∃ (i : I) (s : c.pt ⟶ M.obj i),
    s ≫ c.ι.app i = 𝟙 c.pt ∧
      ∀ j : I, ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k),
        M.map g = c.ι.app j ≫ s ≫ M.map f

/-- A cofiltered diagram is pro-essentially constant with respect to a cone. -/
def IsEssentiallyConstantPro
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] [IsCofiltered I]
    (M : I ⥤ C) (c : Cone M) : Prop :=
  ∃ (i : I) (r : M.obj i ⟶ c.pt),
    c.π.app i ≫ r = 𝟙 c.pt ∧
      ∀ j : I, ∃ (k : I) (f : k ⟶ i) (g : k ⟶ j),
        M.map g = M.map f ≫ r ≫ c.π.app j

/-- A filtered diagram is ind-essentially constant if it has such a cocone. -/
def IsEssentiallyConstantIndDiagram
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] [IsFiltered I]
    (M : I ⥤ C) : Prop :=
  ∃ c : Cocone M, IsEssentiallyConstantInd M c

/-- A cofiltered diagram is pro-essentially constant if it has such a cone. -/
def IsEssentiallyConstantProDiagram
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C] [IsCofiltered I]
    (M : I ⥤ C) : Prop :=
  ∃ c : Cone M, IsEssentiallyConstantPro M c

/-- The source's notion for a system over a directed preorder. -/
def IsEssentiallyConstantSystem
    {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C]
    (M : System I C) : Prop :=
  ∃ hI : IsDirectedSet I,
    letI : Nonempty I := hI.1
    letI : IsDirectedOrder I := hI.2
    IsEssentiallyConstantIndDiagram M

/-- The source's dual notion for an inverse system over a directed preorder. -/
def IsEssentiallyConstantInverseSystem
    {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C]
    (M : InverseSystem I C) : Prop :=
  ∃ hI : IsDirectedSet I,
    letI : Nonempty I := hI.1
    letI : IsDirectedOrder I := hI.2
    IsEssentiallyConstantProDiagram M

/-- A system is eventually isomorphically constant from a threshold.

This is the source-specific packaging of Mathlib's established
`Functor.IsEventuallyConstantFrom` predicate. -/
abbrev EventuallyIsIso
    {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C]
    (M : System I C) : Prop :=
  ∃ i₀ : I, Functor.IsEventuallyConstantFrom M i₀

/-- Essential constancy plus monomorphic transition maps forces eventual isomorphisms. -/
theorem eventuallyIsIso_of_essentiallyConstantSystem_of_mono
    {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C]
    {M : System I C} (hM : IsEssentiallyConstantSystem M)
    (hmono : ∀ ⦃i i' : I⦄ (h : i ≤ i'), Mono (M.map (homOfLE h))) :
    EventuallyIsIso M := by
  rcases hM with ⟨hI, hM⟩
  letI : Nonempty I := hI.1
  letI : IsDirectedOrder I := hI.2
  rcases hM with ⟨c, i, s, hs, hfactor⟩
  refine ⟨i, ?_⟩
  rcases hfactor i with ⟨k₀, a₀, b₀, hab₀⟩
  have hba₀ : b₀ = a₀ := Subsingleton.elim _ _
  have hba₀' : homOfLE (leOfHom a₀) = a₀ := homOfLE_leOfHom a₀
  haveI : Mono (M.map a₀) := by
    rw [← hba₀']
    exact hmono (leOfHom a₀)
  have hproj : c.ι.app i ≫ s = 𝟙 _ := by
    apply (cancel_mono (M.map a₀)).1
    rw [Category.assoc, ← hab₀, hba₀, Category.id_comp]
  intro j f
  let h : i ≤ j := leOfHom f
  have hf : homOfLE h = f := by
    simpa [h] using (homOfLE_leOfHom f)
  haveI : Mono (M.map f) := by
    rw [← hf]
    exact hmono h
  rcases hfactor j with ⟨k, a, b, hab⟩
  let q : M.obj j ⟶ M.obj i := c.ι.app j ≫ s
  have hq : M.map f ≫ q = 𝟙 _ := by
    dsimp [q]
    rw [← Category.assoc, c.w f, hproj]
  have hfb : f ≫ b = a := Subsingleton.elim _ _
  have hba : homOfLE (leOfHom b) = b := homOfLE_leOfHom b
  haveI : Mono (M.map b) := by
    rw [← hba]
    exact hmono (leOfHom b)
  have hq' : q ≫ M.map f = 𝟙 _ := by
    apply (cancel_mono (M.map b)).1
    simp only [Category.assoc, Category.id_comp]
    rw [← M.map_comp, hfb, hab]
    dsimp [q]
    rw [Category.assoc]
  exact IsIso.mk ⟨q, hq, hq'⟩

/-! ## The two source examples -/

/-- The transition map `(a,b) ↦ (a+b,0)` in the first example. -/
def zSquaredTransition :
    AddCommGrpCat.of (ℤ × ℤ) ⟶ AddCommGrpCat.of (ℤ × ℤ) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun p : ℤ × ℤ => (p.1 + p.2, 0)) (by
      intro x y
      ext <;> simp [add_comm, add_left_comm]))

/-- The projection to the claimed essentially constant value `ℤ`. -/
def zSquaredProjection :
    AddCommGrpCat.of (ℤ × ℤ) ⟶ AddCommGrpCat.of ℤ :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun p : ℤ × ℤ => p.1 + p.2) (by
      intro x y
      simp [add_comm, add_left_comm]))

/-- The repeated transition system in the first example. -/
def zSquaredSystem : ℕ ⥤ AddCommGrpCat :=
  Functor.ofSequence (fun _ : ℕ => zSquaredTransition)

/-- The cocone exhibiting the value `ℤ` in the first example. -/
def zSquaredCocone : Cocone zSquaredSystem where
  pt := AddCommGrpCat.of ℤ
  ι :=
    { app := fun _ => zSquaredProjection
      naturality := by
        exact
          (NatTrans.ofSequence (F := zSquaredSystem)
            (G := (Functor.const ℕ).obj (AddCommGrpCat.of ℤ))
            (fun _ => zSquaredProjection) (by
              intro n
              change
                (Functor.ofSequence (fun _ : ℕ => zSquaredTransition)).map
                    (homOfLE (Nat.le_add_right n 1)) ≫ zSquaredProjection =
                  zSquaredProjection ≫ 𝟙 _
              rw [Functor.ofSequence_map_homOfLE_succ]
              ext x
              change x.1 + x.2 + 0 = x.1 + x.2
              simp)).naturality }

/-- The first example is essentially constant with value `ℤ`. -/
theorem zSquaredSystem_is_essentiallyConstant :
    IsEssentiallyConstantInd zSquaredSystem zSquaredCocone := by
  let s : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (ℤ × ℤ) :=
    AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun z : ℤ => (z, 0)) (by
        intro x y
        ext <;> simp))
  have hmap : ∀ k : ℕ,
      (Functor.ofSequence (fun _ : ℕ => zSquaredTransition)).map
        (homOfLE (show 0 ≤ k + 1 by omega)) = zSquaredTransition := by
    intro k
    induction k with
    | zero => rw [Functor.ofSequence_map_homOfLE_succ]
    | succ k ih =>
        rw [show
          (Functor.ofSequence (fun _ : ℕ => zSquaredTransition)).map
              (homOfLE (show 0 ≤ k + 2 by omega)) =
            (Functor.ofSequence (fun _ : ℕ => zSquaredTransition)).map
                (homOfLE (show 0 ≤ k + 1 by omega)) ≫
              (Functor.ofSequence (fun _ : ℕ => zSquaredTransition)).map
                (homOfLE (show k + 1 ≤ k + 2 by omega)) by
          rw [← (Functor.ofSequence (fun _ : ℕ => zSquaredTransition)).map_comp]
          congr 1]
        rw [ih, Functor.ofSequence_map_homOfLE_succ]
        apply AddCommGrpCat.ext
        intro z
        change (z.1 + z.2 + 0, 0) = (z.1 + z.2, 0)
        rw [add_zero]
  refine ⟨0, s, ?_, ?_⟩
  · dsimp [zSquaredCocone]
    exact AddCommGrpCat.ext (by
      intro z
      change z + 0 = z
      rw [add_zero])
  · intro j
    refine ⟨j + 1, homOfLE (show 0 ≤ j + 1 by omega),
        homOfLE (show j ≤ j + 1 by omega), ?_⟩
    change
      (Functor.ofSequence (fun _ : ℕ => zSquaredTransition)).map
          (homOfLE (show j ≤ j + 1 by omega)) =
        zSquaredProjection ≫ s ≫
          (Functor.ofSequence (fun _ : ℕ => zSquaredTransition)).map
            (homOfLE (show 0 ≤ j + 1 by omega))
    rw [Functor.ofSequence_map_homOfLE_succ, hmap j]
    apply AddCommGrpCat.ext
    intro z
    change
      (AddCommGrpCat.Hom.hom zSquaredTransition) z =
        (AddCommGrpCat.Hom.hom
          (zSquaredProjection ≫ s ≫ zSquaredTransition)) z
    rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp]
    simp [zSquaredTransition, zSquaredProjection, s]

/-- Each displayed transition in the first example has a nonzero kernel element. -/
theorem zSquaredSystem_transition_has_nontrivial_kernel (n : ℕ) :
    ∃ x : ℤ × ℤ, x ≠ 0 ∧
      (zSquaredSystem.map (homOfLE (Nat.le_add_right n 1))).hom x = 0 := by
  refine ⟨(1, -1), by norm_num, ?_⟩
  change
    (AddCommGrpCat.Hom.hom
        ((Functor.ofSequence (fun _ : ℕ => zSquaredTransition)).map
          (homOfLE (Nat.le_add_right n 1)))) (1, -1) = 0
  rw [Functor.ofSequence_map_homOfLE_succ]
  change (AddCommGrpCat.Hom.hom zSquaredTransition) (1, -1) = 0
  simp [zSquaredTransition]

/-- The underlying module of the shift example. -/
abbrev ShiftModule := ⨁ _ : ℕ, ℤ

/-- The left shift on the direct sum of countably many copies of `ℤ`. -/
def shiftLinearMap : ShiftModule →ₗ[ℤ] ShiftModule :=
  DirectSum.toModule ℤ ℕ ShiftModule (fun n =>
    match n with
    | 0 => 0
    | n + 1 => DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) n)

/-- The repeated shift system. -/
def shiftSystem : ℕ ⥤ ModuleCat ℤ :=
  Functor.ofSequence (fun _ : ℕ => ModuleCat.ofHom shiftLinearMap)

/-- The colimit of the shift system is zero. -/
theorem shiftSystem_colimit_is_zero :
    IsZero (colimit shiftSystem) := by
  classical
  let F : ℕ ⥤ ModuleCat ℤ :=
    Functor.ofSequence
      (fun _ : ℕ =>
        (ModuleCat.ofHom shiftLinearMap :
          ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
  have hF : F = shiftSystem := by
    rfl
  have hsingle : ∀ (n i k : ℕ) (h : n + i + 1 ≤ k) (z : ℤ),
      ((F.map (homOfLE (show n ≤ k by omega))).hom
        (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) i z)) = 0 := by
    intro n i k h z
    induction i generalizing n k with
    | zero =>
        dsimp [F, Functor.ofSequence]
        change
          ((Functor.OfSequence.map
            (fun _ : ℕ =>
              (ModuleCat.ofHom shiftLinearMap :
                ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
            n k (show n ≤ k by omega)).hom
            (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) 0 z)) = 0
        rw [Functor.OfSequence.map_comp
          (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
            ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
          n (n + 1) k (by omega) (by omega)]
        change
          ((Functor.OfSequence.map
              (fun _ : ℕ =>
                (ModuleCat.ofHom shiftLinearMap :
                  ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
              n (n + 1) (by omega) ≫
            Functor.OfSequence.map
              (fun _ : ℕ =>
                (ModuleCat.ofHom shiftLinearMap :
                  ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
              (n + 1) k (by omega))
            (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) 0 z)) = 0
        rw [ModuleCat.comp_apply]
        rw [Functor.OfSequence.map_le_succ]
        simp [shiftLinearMap]
    | succ i ih =>
        dsimp [F, Functor.ofSequence]
        change
          ((Functor.OfSequence.map
            (fun _ : ℕ =>
              (ModuleCat.ofHom shiftLinearMap :
                ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
            n k (show n ≤ k by omega)).hom
            (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) (i + 1) z)) = 0
        rw [Functor.OfSequence.map_comp
          (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
            ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
          n (n + 1) k (by omega) (by omega)]
        change
          ((Functor.OfSequence.map
              (fun _ : ℕ =>
                (ModuleCat.ofHom shiftLinearMap :
                  ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
              n (n + 1) (by omega) ≫
            Functor.OfSequence.map
              (fun _ : ℕ =>
                (ModuleCat.ofHom shiftLinearMap :
                  ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
              (n + 1) k (by omega))
            (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) (i + 1) z)) = 0
        rw [ModuleCat.comp_apply]
        rw [Functor.OfSequence.map_le_succ]
        simp only [ConcreteCategory.hom_ofHom]
        rw [show shiftLinearMap
          (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) (i + 1) z) =
            DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) i z by
          simp [shiftLinearMap]]
        exact ih (n + 1) k (by omega)
  have hkill : ∀ (n : ℕ) (x : ShiftModule),
      ∃ (k : ℕ) (h : n ≤ k),
        (F.map (homOfLE h)).hom x = 0 := by
    intro n x
    induction x using DirectSum.induction_on with
    | zero =>
        refine ⟨n, le_rfl, ?_⟩
        rw [show homOfLE (le_refl n) = 𝟙 n by simp, F.map_id]
        change (0 : ShiftModule) = 0
        rfl
    | of i z =>
        exact ⟨n + i + 1, by omega, hsingle n i (n + i + 1) (by omega) z⟩
    | add x y hx hy =>
        rcases hx with ⟨k, hk, hx⟩
        rcases hy with ⟨l, hl, hy⟩
        refine ⟨max k l, by omega, ?_⟩
        have hx' :
            (F.map (homOfLE (show n ≤ max k l by omega))).hom x = 0 := by
          dsimp [F, Functor.ofSequence] at hx ⊢
          change
            (ConcreteCategory.hom
              (Functor.OfSequence.map
                (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
                  ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
                n k hk)) x = 0 at hx
          rw [Functor.OfSequence.map_comp
            (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
              ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
            n k (max k l) hk (by omega)]
          change
            ((Functor.OfSequence.map
                (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
                  ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
                n k hk ≫
              Functor.OfSequence.map
                (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
                  ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
                k (max k l) (by omega)) x) = 0
          rw [ModuleCat.comp_apply]
          rw [hx]
          simp
        have hy' :
            (F.map (homOfLE (show n ≤ max k l by omega))).hom y = 0 := by
          dsimp [F, Functor.ofSequence] at hy ⊢
          change
            (ConcreteCategory.hom
              (Functor.OfSequence.map
                (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
                  ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
                n l hl)) y = 0 at hy
          rw [Functor.OfSequence.map_comp
            (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
              ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
            n l (max k l) hl (by omega)]
          change
            ((Functor.OfSequence.map
                (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
                  ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
                n l hl ≫
              Functor.OfSequence.map
                (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
                  ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
                l (max k l) (by omega)) y) = 0
          rw [ModuleCat.comp_apply]
          rw [hy]
          simp
        dsimp [F, Functor.ofSequence] at hx' hy' ⊢
        change
          (ConcreteCategory.hom
            (Functor.OfSequence.map
              (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
                ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
              n (max k l) (by omega))) (x + y) = 0
        change
          (ConcreteCategory.hom
            (Functor.OfSequence.map
              (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
                ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
              n (max k l) (by omega))) x = 0 at hx'
        change
          (ConcreteCategory.hom
            (Functor.OfSequence.map
              (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
                ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
              n (max k l) (by omega))) y = 0 at hy'
        rw [map_add, hx', hy', add_zero]
  have hzero : ∀ (x y : (colimit F : ModuleCat ℤ)), x = y := by
    intro x y
    obtain ⟨j, xj, rfl⟩ := Concrete.colimit_exists_rep F x
    obtain ⟨k, yk, rfl⟩ := Concrete.colimit_exists_rep F y
    have hxzero : colimit.ι F j xj = 0 := by
      rcases hkill j xj with ⟨j', h, hh⟩
      rw [← colimit.w F (homOfLE h)]
      change colimit.ι F j' ((F.map (homOfLE h)).hom xj) = 0
      rw [hh]
      simp
    have hyzero : colimit.ι F k yk = 0 := by
      rcases hkill k yk with ⟨k', h, hh⟩
      rw [← colimit.w F (homOfLE h)]
      change colimit.ι F k' ((F.map (homOfLE h)).hom yk) = 0
      rw [hh]
      simp
    rw [hxzero, hyzero]
  letI : Subsingleton (colimit F : ModuleCat ℤ) := ⟨hzero⟩
  have hZF : IsZero (colimit F) := ModuleCat.isZero_of_subsingleton _
  simpa only [F, shiftSystem] using hZF

/-- The zero object supplies the split section/retraction in the shift example. -/
theorem shiftSystem_zero_retraction (n : ℕ) :
    (0 : (0 : ModuleCat ℤ) ⟶ shiftSystem.obj n) ≫
        (0 : shiftSystem.obj n ⟶ (0 : ModuleCat ℤ)) =
      𝟙 (0 : ModuleCat ℤ) := by
  simp

/-- The shift system is not essentially constant despite its zero colimit and split map. -/
theorem shiftSystem_not_essentiallyConstant :
    ¬ IsEssentiallyConstantIndDiagram shiftSystem := by
  have hmap : ∀ (i d r : ℕ),
      (shiftSystem.map (homOfLE (show i ≤ i + d by omega))).hom
          (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) (d + r) 1) =
        DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) r 1 := by
    intro i d r
    induction d generalizing r with
    | zero =>
        dsimp [shiftSystem, Functor.ofSequence]
        change
          ((Functor.OfSequence.map
            (fun _ : ℕ =>
              (ModuleCat.ofHom shiftLinearMap :
                ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
            i i (show i ≤ i by omega)).hom
            (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) (0 + r) 1)) =
            DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) r 1
        rw [Functor.OfSequence.map_id]
        simp
    | succ d ih =>
        dsimp [shiftSystem, Functor.ofSequence]
        change
          ((Functor.OfSequence.map
            (fun _ : ℕ =>
              (ModuleCat.ofHom shiftLinearMap :
                ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
            i (i + d + 1) (show i ≤ i + d + 1 by omega)).hom
            (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) (d + 1 + r) 1)) =
            DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) r 1
        rw [Functor.OfSequence.map_comp
          (fun _ : ℕ => (ModuleCat.ofHom shiftLinearMap :
            ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
          i (i + d) (i + d + 1) (by omega) (by omega)]
        change
          ((Functor.OfSequence.map
              (fun _ : ℕ =>
                (ModuleCat.ofHom shiftLinearMap :
                  ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
              i (i + d) (by omega) ≫
            Functor.OfSequence.map
              (fun _ : ℕ =>
                (ModuleCat.ofHom shiftLinearMap :
                  ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
              (i + d) (i + d + 1) (by omega))
            (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) (d + 1 + r) 1)) =
            DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) r 1
        rw [ModuleCat.comp_apply]
        rw [Functor.OfSequence.map_le_succ]
        simp only [ConcreteCategory.hom_ofHom]
        have hinner :
            (Functor.OfSequence.map
                (fun _ : ℕ =>
                  (ModuleCat.ofHom shiftLinearMap :
                    ModuleCat.of ℤ ShiftModule ⟶ ModuleCat.of ℤ ShiftModule))
                i (i + d) (by omega)).hom
              (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) (d + (r + 1)) 1) =
              DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) (r + 1) 1 := by
          dsimp [shiftSystem, Functor.ofSequence] at ih
          exact ih (r + 1)
        rw [show d + 1 + r = d + (r + 1) by omega, hinner]
        simp [shiftLinearMap]
  intro hM
  rcases hM with ⟨c, hc⟩
  rcases hc with ⟨i, s, hs, hfactor⟩
  have hkill : ∀ (j : ℕ) (x : shiftSystem.obj j),
      ∃ (k : ℕ) (f : j ⟶ k), (shiftSystem.map f).hom x = 0 := by
    intro j x
    have hx : colimit.ι shiftSystem j x = 0 := by
      have hιzero : colimit.ι shiftSystem j =
          (0 : shiftSystem.obj j ⟶ colimit shiftSystem) :=
        shiftSystem_colimit_is_zero.eq_of_tgt (colimit.ι shiftSystem j) 0
      rw [hιzero]
      simp
    exact Concrete.colimit_rep_eq_zero (R := ℤ) shiftSystem j x hx
  have hι : ∀ j : ℕ, c.ι.app j = 0 := by
    intro j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases hkill j x with ⟨k, f, hf⟩
    have hw := congrArg (fun g => g.hom x) (c.w f)
    change
      (c.ι.app k).hom ((shiftSystem.map f).hom x) =
        (c.ι.app j).hom x at hw
    change (c.ι.app j).hom x = (0 : c.pt)
    simpa only [Functor.const_obj_obj, hf, map_zero] using hw.symm
  rcases hfactor i with ⟨k, f, g, hfg⟩
  have hmapzero : shiftSystem.map g = 0 := by
    rw [hfg, hι i]
    simp
  obtain ⟨d, hk⟩ := Nat.exists_eq_add_of_le (leOfHom g)
  subst k
  have hg : g = homOfLE (show i ≤ i + d by omega) := by
    apply Subsingleton.elim
  rw [hg] at hmapzero
  have heval := congrArg
    (fun q => q.hom (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) d 1)) hmapzero
  have hnonzero :
      (shiftSystem.map (homOfLE (show i ≤ i + d by omega))).hom
          (DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) d 1) =
        DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) 0 1 := by
    simpa using hmap i d 0
  rw [hnonzero] at heval
  have hne : DirectSum.lof ℤ ℕ (fun _ : ℕ => ℤ) 0 1 ≠ 0 := by
    intro hz
    have hz' := congrArg (fun x => x 0) hz
    simp at hz'
  exact hne heval

/-! ## The sanity check and Ind/Pro viewpoints -/

/-- The chosen cocone in an ind-essentially constant diagram is a colimit cocone. -/
theorem essentiallyConstantInd_hasColimit
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (hM : IsEssentiallyConstantIndDiagram M) :
    ∃ c : Cocone M, Nonempty (IsColimit c) ∧ IsEssentiallyConstantInd M c := by
  rcases hM with ⟨c, hc⟩
  rcases hc with ⟨i, s, hs, hfactor⟩
  let P : IsColimit c := {
    desc := fun t => s ≫ t.ι.app i
    fac := by
      intro t j
      rcases hfactor j with ⟨k, f, g, hfg⟩
      have h := congrArg (fun u => u ≫ t.ι.app k) hfg
      simpa only [Category.assoc, t.w f, t.w g] using h.symm
    uniq := by
      intro t m hm
      calc
        m = 𝟙 c.pt ≫ m := by simp
        _ = (s ≫ c.ι.app i) ≫ m := by rw [hs]
        _ = s ≫ (c.ι.app i ≫ m) := by rw [Category.assoc]
        _ = s ≫ t.ι.app i := by rw [hm i]
  }
  exact ⟨c, ⟨P⟩, ⟨i, s, hs, hfactor⟩⟩

/-- The chosen cone in a pro-essentially constant diagram is a limit cone. -/
theorem essentiallyConstantPro_hasLimit
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (hM : IsEssentiallyConstantProDiagram M) :
    ∃ c : Cone M, Nonempty (IsLimit c) ∧ IsEssentiallyConstantPro M c := by
  rcases hM with ⟨c, hc⟩
  rcases hc with ⟨i, r, hr, hfactor⟩
  let P : IsLimit c := {
    lift := fun t => t.π.app i ≫ r
    fac := by
      intro t j
      rcases hfactor j with ⟨k, f, g, hfg⟩
      have h := congrArg (fun u => t.π.app k ≫ u) hfg
      rw [t.w g] at h
      rw [← Category.assoc] at h
      rw [t.w f] at h
      simpa only [Category.assoc] using h.symm
    uniq := by
      intro t m hm
      calc
        m = m ≫ 𝟙 c.pt := by simp
        _ = m ≫ (c.π.app i ≫ r) := by rw [hr]
        _ = (m ≫ c.π.app i) ≫ r := by rw [Category.assoc]
        _ = t.π.app i ≫ r := by rw [hm i]
  }
  exact ⟨c, ⟨P⟩, ⟨i, r, hr, hfactor⟩⟩

private theorem isColimit_of_essentiallyConstantInd
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cocone M) (hM : IsEssentiallyConstantInd M c) :
    Nonempty (IsColimit c) := by
  rcases hM with ⟨i, s, hs, hfactor⟩
  let P : IsColimit c := {
    desc := fun t => s ≫ t.ι.app i
    fac := by
      intro t j
      rcases hfactor j with ⟨k, f, g, hfg⟩
      have h := congrArg (fun u => u ≫ t.ι.app k) hfg
      simpa only [Category.assoc, t.w f, t.w g] using h.symm
    uniq := by
      intro t m hm
      calc
        m = 𝟙 c.pt ≫ m := by simp
        _ = (s ≫ c.ι.app i) ≫ m := by rw [hs]
        _ = s ≫ (c.ι.app i ≫ m) := by rw [Category.assoc]
        _ = s ≫ t.ι.app i := by rw [hm i]
  }
  exact ⟨P⟩

/-- The canonical ind-category attached to a category. -/
abbrev IndCategory (C : Type u) [Category.{v} C] := CategoryTheory.Ind C

/-- The canonical fully faithful embedding into the ind-category. -/
noncomputable def indEmbedding {C : Type u} [Category.{v} C] :
    C ⥤ IndCategory C :=
  Ind.yoneda

noncomputable def indEmbedding_fullyFaithful {C : Type u} [Category.{v} C] :
    (indEmbedding (C := C)).FullyFaithful :=
  Ind.yoneda.fullyFaithful

/-- The pro-category is the opposite of the ind-category of the opposite. -/
abbrev ProCategory (C : Type u) [Category.{v} C] :=
  (CategoryTheory.Ind Cᵒᵖ)ᵒᵖ

/-- The canonical fully faithful embedding into the pro-category. -/
noncomputable def proEmbedding {C : Type u} [Category.{v} C] :
    C ⥤ ProCategory C :=
  opOp C ⋙ (Ind.yoneda (C := Cᵒᵖ)).op

noncomputable def proEmbedding_fullyFaithful {C : Type u} [Category.{v} C] :
    (proEmbedding (C := C)).FullyFaithful := by
  exact
    (Functor.FullyFaithful.ofFullyFaithful (opOp C)).comp
      (Ind.yoneda.fullyFaithful (C := Cᵒᵖ)).op

/-- The ind-object represented by a small filtered diagram. -/
noncomputable def indLim
    {C : Type u} [Category.{v} C]
    (I : Type v) [SmallCategory I] [IsFiltered I] :
    (I ⥤ C) ⥤ IndCategory C :=
  Ind.lim I

/-- The pro-object represented by a small cofiltered diagram. -/
noncomputable def proLim
    {C : Type u} [Category.{v} C]
    (I : Type v) [SmallCategory I] [IsCofiltered I] :
    (I ⥤ C) ⥤ ProCategory C where
  obj M := Opposite.op ((Ind.lim (C := Cᵒᵖ) Iᵒᵖ).obj M.op)
  map {M N} α := ((Ind.lim (C := Cᵒᵖ) Iᵒᵖ).map (NatTrans.op α)).op
  map_id := by
    intro M
    apply Quiver.Hom.op_inj
    simp
  map_comp := by
    intro M N P α β
    apply Quiver.Hom.op_inj
    simp

/-- The ind characterization in the ind-category. -/
theorem essentiallyConstantInd_iff_indLim_isomorphic_to_constant
    {C : Type u} [Category.{v} C]
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ C) :
    IsEssentiallyConstantIndDiagram M ↔
      ∃ X : C, Nonempty ((indLim I).obj M ≅ (indEmbedding (C := C)).obj X) := by
  change IsEssentiallyConstantIndDiagram M ↔
    ∃ X : C, Nonempty (colimit (M ⋙ indEmbedding) ≅ (indEmbedding (C := C)).obj X)
  constructor
  · rintro ⟨c, ⟨i, s, hs, hfactor⟩⟩
    let d : Cocone (M ⋙ indEmbedding) :=
      { pt := indEmbedding.obj c.pt
        ι :=
          { app := fun j => indEmbedding.map (c.ι.app j)
            naturality := by
              intro j k f
              change indEmbedding.map (M.map f) ≫ indEmbedding.map (c.ι.app k) =
                indEmbedding.map (c.ι.app j) ≫
                  ((Functor.const I).obj (indEmbedding.obj c.pt)).map f
              calc
                indEmbedding.map (M.map f) ≫ indEmbedding.map (c.ι.app k) =
                    indEmbedding.map (M.map f ≫ c.ι.app k) := by
                  rw [indEmbedding.map_comp]
                _ = indEmbedding.map (c.ι.app j ≫ 𝟙 c.pt) :=
                  congrArg indEmbedding.map (c.ι.naturality f)
                _ = indEmbedding.map (c.ι.app j) ≫ indEmbedding.map (𝟙 c.pt) := by
                  rw [indEmbedding.map_comp]
                _ = indEmbedding.map (c.ι.app j) ≫
                    ((Functor.const I).obj (indEmbedding.obj c.pt)).map f := by
                  simp [Functor.const_obj_map] } }
    let f : colimit (M ⋙ indEmbedding) ⟶ indEmbedding.obj c.pt :=
      colimit.desc (M ⋙ indEmbedding) d
    let g : indEmbedding.obj c.pt ⟶ colimit (M ⋙ indEmbedding) :=
      indEmbedding.map s ≫ colimit.ι (M ⋙ indEmbedding) i
    have hdesc (j : I) :
        colimit.ι (M ⋙ indEmbedding) j ≫ f = indEmbedding.map (c.ι.app j) := by
      exact colimit.ι_desc d j
    have hfg : f ≫ g = 𝟙 _ := by
      apply colimit.hom_ext
      intro j
      rcases hfactor j with ⟨k, a, b, hab⟩
      have hmap_a : (M ⋙ indEmbedding).map a = indEmbedding.map (M.map a) := by
        rfl
      calc
        colimit.ι (M ⋙ indEmbedding) j ≫ (f ≫ g) =
            indEmbedding.map (c.ι.app j) ≫ g := by
              simpa only [Category.assoc] using
                congrArg (fun q => q ≫ g) (hdesc j)
        _ = indEmbedding.map (c.ι.app j ≫ s) ≫
              colimit.ι (M ⋙ indEmbedding) i := by
              dsimp [g]
              simpa only [Category.assoc] using
                congrArg (fun q => q ≫ colimit.ι (M ⋙ indEmbedding) i)
                  (indEmbedding.map_comp (c.ι.app j) s).symm
        _ = indEmbedding.map (c.ι.app j ≫ s) ≫
              (indEmbedding.map (M.map a) ≫
                colimit.ι (M ⋙ indEmbedding) k) := by
              change indEmbedding.map (c.ι.app j ≫ s) ≫
                  colimit.ι (M ⋙ indEmbedding) i =
                indEmbedding.map (c.ι.app j ≫ s) ≫
                  indEmbedding.map (M.map a) ≫ colimit.ι (M ⋙ indEmbedding) k
              rw [← hmap_a]
              rw [← colimit.w (M ⋙ indEmbedding) a]
        _ = indEmbedding.map (c.ι.app j ≫ s ≫ M.map a) ≫
              colimit.ι (M ⋙ indEmbedding) k := by
              simpa only [Category.assoc] using
                congrArg (fun q => q ≫ colimit.ι (M ⋙ indEmbedding) k)
                  (indEmbedding.map_comp (c.ι.app j ≫ s) (M.map a)).symm
        _ = indEmbedding.map (M.map b) ≫
              colimit.ι (M ⋙ indEmbedding) k := by rw [hab]
        _ = colimit.ι (M ⋙ indEmbedding) j := colimit.w (M ⋙ indEmbedding) b
        _ = colimit.ι (M ⋙ indEmbedding) j ≫ 𝟙 _ := by simp
    have hgf : g ≫ f = 𝟙 _ := by
      dsimp [g]
      calc
        (indEmbedding.map s ≫ colimit.ι (M ⋙ indEmbedding) i) ≫ f =
            indEmbedding.map s ≫
              (colimit.ι (M ⋙ indEmbedding) i ≫ f) := by rw [Category.assoc]
        _ = indEmbedding.map s ≫ indEmbedding.map (c.ι.app i) := by rw [hdesc]
        _ = indEmbedding.map (s ≫ c.ι.app i) := by
              rw [indEmbedding.map_comp]
        _ = 𝟙 _ := by rw [hs, indEmbedding.map_id]
    exact ⟨c.pt, ⟨{ hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }⟩⟩
  · change (∃ X : C, Nonempty ((Ind.lim I).obj M ≅ Ind.yoneda.obj X)) →
      IsEssentiallyConstantIndDiagram M
    rintro ⟨X, ⟨e⟩⟩
    change colimit (M ⋙ Ind.yoneda) ≅ Ind.yoneda.obj X at e
    let c : Cocone M :=
      { pt := X
        ι :=
          { app := fun j =>
              (Ind.yoneda.fullyFaithful (C := C)).preimage
                (colimit.ι (M ⋙ Ind.yoneda) j ≫ e.hom)
            naturality := by
              intro j k f
              apply (Ind.yoneda.fullyFaithful (C := C)).map_injective
              simp [Functor.map_comp, Functor.FullyFaithful.map_preimage,
                Functor.const_obj_map]
              simpa only [Functor.comp_map, Category.assoc] using
                congrArg (fun z => z ≫ e.hom)
                  (colimit.w (M ⋙ Ind.yoneda) f) } }
    let α := (Ind.yonedaCompInclusion (C := C)).app X
    let β := (Ind.limCompInclusion (C := C) (I := I)).app M
    change (Ind.inclusion C).obj (colimit (M ⋙ Ind.yoneda)) ≅
      colimit (M ⋙ yoneda) at β
    let q : yoneda.obj X ⟶ colimit (M ⋙ yoneda) :=
      α.inv ≫ (Ind.inclusion C).map e.inv ≫ β.hom
    let x := (colimitObjIsoColimitCompEvaluation (M ⋙ yoneda) (Opposite.op X)).hom
      (yonedaEquiv q)
    obtain ⟨i, s, hsrep⟩ := Concrete.colimit_exists_rep
      ((M ⋙ yoneda) ⋙ (evaluation Cᵒᵖ (Type v)).obj (Opposite.op X)) x
    change X ⟶ M.obj i at s
    have hq : q = yoneda.map s ≫ colimit.ι (M ⋙ yoneda) i := by
      have hsrep' := congrArg
        (ConcreteCategory.hom
          (colimitObjIsoColimitCompEvaluation (M ⋙ yoneda) (Opposite.op X)).inv)
        hsrep
      have hleft :
          (ConcreteCategory.hom
            (colimitObjIsoColimitCompEvaluation (M ⋙ yoneda) (Opposite.op X)).inv)
              ((ConcreteCategory.hom
                (colimitObjIsoColimitCompEvaluation (M ⋙ yoneda) (Opposite.op X)).hom)
                (yonedaEquiv q)) = yonedaEquiv q := by
        simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
          ConcreteCategory.congr_hom
            (colimitObjIsoColimitCompEvaluation (M ⋙ yoneda) (Opposite.op X)).hom_inv_id
            (yonedaEquiv q)
      have hright :
          (ConcreteCategory.hom
            (colimitObjIsoColimitCompEvaluation (M ⋙ yoneda) (Opposite.op X)).inv)
              ((ConcreteCategory.hom
                (colimit.ι ((M ⋙ yoneda) ⋙ (evaluation Cᵒᵖ (Type v)).obj
                  (Opposite.op X)) i)) s) =
            (ConcreteCategory.hom ((colimit.ι (M ⋙ yoneda) i).app
              (Opposite.op X))) s := by
        simpa only [ConcreteCategory.comp_apply] using
          ConcreteCategory.congr_hom
            (colimitObjIsoColimitCompEvaluation_ι_inv
              (M ⋙ yoneda) i (Opposite.op X)) s
      apply yonedaEquiv.injective
      rw [yonedaEquiv_apply]
      calc
        (ConcreteCategory.hom (q.app (Opposite.op X))) (𝟙 X) = yonedaEquiv q :=
          (yonedaEquiv_apply q).symm
        _ = ConcreteCategory.hom
              (colimitObjIsoColimitCompEvaluation (M ⋙ yoneda) (Opposite.op X)).inv
              x := by
                dsimp [x]
                exact hleft.symm
        _ = ConcreteCategory.hom
              (colimitObjIsoColimitCompEvaluation (M ⋙ yoneda) (Opposite.op X)).inv
              ((ConcreteCategory.hom
                (colimit.ι ((M ⋙ yoneda) ⋙ (evaluation Cᵒᵖ (Type v)).obj
                  (Opposite.op X)) i)) s) := by rw [hsrep]
        _ = (ConcreteCategory.hom ((colimit.ι (M ⋙ yoneda) i).app
              (Opposite.op X))) s := by simpa using hright
        _ = (ConcreteCategory.hom
              ((yoneda.map s ≫ colimit.ι (M ⋙ yoneda) i).app
                (Opposite.op X))) (𝟙 X) := by simp
    have heinv : e.inv = Ind.yoneda.map s ≫ colimit.ι (M ⋙ Ind.yoneda) i := by
      apply (Ind.inclusion C).map_injective
      change (Ind.inclusion C).map e.inv =
        (Ind.inclusion C).map (Ind.yoneda.map s ≫
          colimit.ι (M ⋙ Ind.yoneda) i)
      have hinc :
          (Ind.inclusion C).map e.inv =
            α.hom ≫ (yoneda.map s ≫ colimit.ι (M ⋙ yoneda) i) ≫ β.inv := by
        rw [← hq]
        dsimp [q]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        simp
      have hβ (j : I) :
          (Ind.inclusion C).map (colimit.ι (M ⋙ Ind.yoneda) j) ≫ β.hom =
            (Ind.yonedaCompInclusion (C := C)).hom.app (M.obj j) ≫
              colimit.ι (M ⋙ yoneda) j := by
        change (Ind.inclusion C).map (colimit.ι (M ⋙ Ind.yoneda) j) ≫ β.hom =
          (Ind.yonedaCompInclusion (C := C)).hom.app (M.obj j) ≫
            colimit.ι (M ⋙ yoneda) j
        dsimp [β, Ind.limCompInclusion, Ind.lim, indEmbedding]
        simp [Trans.trans, Iso.trans, Functor.isoWhiskerLeft,
          Functor.whiskeringRightObjCompIso, Category.assoc]
      have hstep :
          α.hom ≫ (yoneda.map s ≫ colimit.ι (M ⋙ yoneda) i) ≫ β.inv =
              (Ind.inclusion C).map (Ind.yoneda.map s) ≫
              (Ind.inclusion C).map (colimit.ι (M ⋙ Ind.yoneda) i) := by
        dsimp [α]
        rw [← Category.assoc, ← Category.assoc]
        rw [← (Ind.yonedaCompInclusion (C := C)).hom.naturality s]
        have h := congrArg
          (fun z => (Ind.yoneda ⋙ Ind.inclusion C).map s ≫ z ≫ β.inv)
          (hβ i)
        simpa [Category.assoc, Functor.comp_map, β.hom_inv_id] using h.symm
      simpa [Functor.map_comp] using hinc.trans hstep
    have hs : s ≫ c.ι.app i = 𝟙 X := by
      apply (Ind.yoneda.fullyFaithful (C := C)).map_injective
      dsimp [c]
      rw [Functor.map_comp, Functor.FullyFaithful.map_preimage]
      rw [← Category.assoc, ← heinv]
      simp
    have hβ (j : I) :
        (Ind.inclusion C).map (colimit.ι (M ⋙ Ind.yoneda) j) ≫ β.hom =
          (Ind.yonedaCompInclusion (C := C)).hom.app (M.obj j) ≫
            colimit.ι (M ⋙ yoneda) j := by
      change (Ind.inclusion C).map (colimit.ι (M ⋙ Ind.yoneda) j) ≫ β.hom =
        (Ind.yonedaCompInclusion (C := C)).hom.app (M.obj j) ≫
          colimit.ι (M ⋙ yoneda) j
      dsimp [β, Ind.limCompInclusion, Ind.lim, indEmbedding]
      simp [Trans.trans, Iso.trans, Functor.isoWhiskerLeft,
        Functor.whiskeringRightObjCompIso, Category.assoc]
    refine ⟨c, ⟨i, s, hs, ?_⟩⟩
    intro j
    have hcj (j : I) :
        Ind.yoneda.map (c.ι.app j) =
          colimit.ι (M ⋙ Ind.yoneda) j ≫ e.hom := by
      dsimp [c]
      simp
    have hstagej (j : I) :
        colimit.ι (M ⋙ Ind.yoneda) j =
          Ind.yoneda.map (c.ι.app j ≫ s) ≫
            colimit.ι (M ⋙ Ind.yoneda) i := by
      calc
        colimit.ι (M ⋙ Ind.yoneda) j =
            colimit.ι (M ⋙ Ind.yoneda) j ≫ e.hom ≫ e.inv := by
              rw [e.hom_inv_id, Category.comp_id]
        _ = Ind.yoneda.map (c.ι.app j) ≫ e.inv := by
              rw [hcj]
              simp only [Category.assoc]
        _ = Ind.yoneda.map (c.ι.app j) ≫
              (Ind.yoneda.map s ≫ colimit.ι (M ⋙ Ind.yoneda) i) := by
              rw [heinv]
        _ = Ind.yoneda.map (c.ι.app j ≫ s) ≫
              colimit.ι (M ⋙ Ind.yoneda) i := by
              simp [Category.assoc]
    have hp (j : I) :
        colimit.ι (M ⋙ yoneda) j =
          yoneda.map (c.ι.app j ≫ s) ≫ colimit.ι (M ⋙ yoneda) i := by
      apply (cancel_epi
        ((Ind.yonedaCompInclusion (C := C)).hom.app (M.obj j))).1
      have hmap := congrArg
        (fun z => (Ind.inclusion C).map z ≫ β.hom) (hstagej j)
      have hmap' :
          (Ind.inclusion C).map (colimit.ι (M ⋙ Ind.yoneda) j) ≫ β.hom =
            (Ind.inclusion C).map (Ind.yoneda.map (c.ι.app j ≫ s)) ≫
              ((Ind.inclusion C).map (colimit.ι (M ⋙ Ind.yoneda) i) ≫ β.hom) := by
        simpa only [Functor.map_comp, Category.assoc] using hmap
      calc
        (Ind.yonedaCompInclusion (C := C)).hom.app (M.obj j) ≫
              colimit.ι (M ⋙ yoneda) j =
            (Ind.inclusion C).map (colimit.ι (M ⋙ Ind.yoneda) j) ≫ β.hom :=
          (hβ j).symm
        _ = (Ind.inclusion C).map (Ind.yoneda.map (c.ι.app j ≫ s)) ≫
              ((Ind.inclusion C).map (colimit.ι (M ⋙ Ind.yoneda) i) ≫ β.hom) := hmap'
        _ = (Ind.inclusion C).map (Ind.yoneda.map (c.ι.app j ≫ s)) ≫
              ((Ind.yonedaCompInclusion (C := C)).hom.app (M.obj i) ≫
                colimit.ι (M ⋙ yoneda) i) := by rw [hβ i]
        _ = (Ind.yonedaCompInclusion (C := C)).hom.app (M.obj j) ≫
              (yoneda.map (c.ι.app j ≫ s) ≫ colimit.ι (M ⋙ yoneda) i) := by
          simpa only [Functor.comp_map, Category.assoc] using
            congrArg (fun z => z ≫ colimit.ι (M ⋙ yoneda) i)
              ((Ind.yonedaCompInclusion (C := C)).hom.naturality
                (c.ι.app j ≫ s))
    have heq :
        colimit.ι ((M ⋙ yoneda) ⋙ (evaluation Cᵒᵖ (Type v)).obj
          (Opposite.op (M.obj j))) j (𝟙 (M.obj j)) =
          colimit.ι ((M ⋙ yoneda) ⋙ (evaluation Cᵒᵖ (Type v)).obj
            (Opposite.op (M.obj j))) i (c.ι.app j ≫ s) := by
      have hp' := congrArg
        (fun z => ConcreteCategory.hom
          (z.app (Opposite.op (M.obj j)) ≫
            (colimitObjIsoColimitCompEvaluation
              (M ⋙ yoneda) (Opposite.op (M.obj j))).hom)
          (𝟙 (M.obj j))) (hp j)
      simpa [Functor.comp_map, Category.assoc] using hp'
    obtain ⟨k, f, g, hfg⟩ :=
      (Types.FilteredColimit.colimit_eq_iff
        ((M ⋙ yoneda) ⋙ (evaluation Cᵒᵖ (Type v)).obj
          (Opposite.op (M.obj j)))).1 heq
    refine ⟨k, g, f, ?_⟩
    simpa [Category.assoc] using hfg

private theorem isEssentiallyConstantPro_iff_op
    {C : Type u} [Category.{v} C]
    {I : Type v} [SmallCategory I] [IsCofiltered I]
    {M : I ⥤ C} (c : Cone M) :
    IsEssentiallyConstantPro M c ↔
      IsEssentiallyConstantInd M.op c.op := by
  constructor
  · rintro ⟨i, r, hr, hfactor⟩
    refine ⟨Opposite.op i, r.op, ?_, ?_⟩
    · simpa using congrArg Quiver.Hom.op hr
    · intro j
      rcases hfactor j.unop with ⟨k, f, g, hfg⟩
      refine ⟨Opposite.op k, f.op, g.op, ?_⟩
      simpa using congrArg Quiver.Hom.op hfg
  · rintro ⟨i, s, hs, hfactor⟩
    refine ⟨i.unop, s.unop, ?_, ?_⟩
    · simpa using congrArg Quiver.Hom.unop hs
    · intro j
      rcases hfactor (Opposite.op j) with ⟨k, f, g, hfg⟩
      refine ⟨k.unop, f.unop, g.unop, ?_⟩
      simpa using congrArg Quiver.Hom.unop hfg

/-- The pro characterization in the pro-category. -/
theorem essentiallyConstantPro_iff_proLim_isomorphic_to_constant
    {C : Type u} [Category.{v} C]
    {I : Type v} [SmallCategory I] [IsCofiltered I]
    (M : I ⥤ C) :
    IsEssentiallyConstantProDiagram M ↔
      ∃ X : C, Nonempty ((proLim I).obj M ≅ (proEmbedding (C := C)).obj X) := by
  change IsEssentiallyConstantProDiagram M ↔
    ∃ X : C, Nonempty
      (Opposite.op ((Ind.lim (C := Cᵒᵖ) Iᵒᵖ).obj M.op) ≅
        Opposite.op ((Ind.yoneda (C := Cᵒᵖ)).obj (Opposite.op X)))
  constructor
  · rintro ⟨c, hc⟩
    have hInd : IsEssentiallyConstantIndDiagram M.op :=
      ⟨c.op, (isEssentiallyConstantPro_iff_op c).mp hc⟩
    obtain ⟨X, ⟨e⟩⟩ :=
      (essentiallyConstantInd_iff_indLim_isomorphic_to_constant M.op).mp hInd
    refine ⟨X.unop, ⟨?_⟩⟩
    simpa [indLim, indEmbedding] using (Iso.op e.symm)
  · rintro ⟨X, ⟨e⟩⟩
    have hInd : IsEssentiallyConstantIndDiagram M.op :=
      (essentiallyConstantInd_iff_indLim_isomorphic_to_constant M.op).mpr
        ⟨Opposite.op X, ⟨(e.unop).symm⟩⟩
    obtain ⟨c, hc⟩ := hInd
    exact ⟨c.unop, (isEssentiallyConstantPro_iff_op c.unop).mpr hc⟩

/-! The following structure records the standard representative of a pro
morphism between inverse sequences.  `refines` is the common-refinement
criterion from the source's example. -/

structure ProMorphismData
    {C : Type u} [Category.{v} C]
    (X Y : ℕᵒᵖ ⥤ C) where
  index : ℕ → ℕ
  monotone : Monotone index
  app : ∀ n : ℕ, X.obj (Opposite.op (index n)) ⟶ Y.obj (Opposite.op n)
  naturality : ∀ {n n' : ℕ} (h : n ≤ n'),
    X.map (homOfLE (monotone h)).op ≫ app n =
      app n' ≫ Y.map (homOfLE h).op

/-- The unreindexed data for a morphism of inverse sequences. -/
structure RawProMorphismData
    {C : Type u} [Category.{v} C]
    (X Y : ℕᵒᵖ ⥤ C) where
  index : ℕ → ℕ
  app : ∀ n : ℕ, X.obj (Opposite.op (index n)) ⟶ Y.obj (Opposite.op n)
  compatible : ∀ {n n' : ℕ} (h : n ≤ n'),
    ∃ (m : ℕ) (hn : index n ≤ m) (hn' : index n' ≤ m),
      X.map (homOfLE hn).op ≫ app n =
        X.map (homOfLE hn').op ≫ app n' ≫ Y.map (homOfLE h).op

namespace RawProMorphismData

/-- A monotone representative refines raw data when it is obtained by moving
each source index farther out and composing with the inverse-system map. -/
def Refines
    {C : Type u} [Category.{v} C]
    {X Y : ℕᵒᵖ ⥤ C}
    (p : RawProMorphismData X Y) (q : ProMorphismData X Y) : Prop :=
  (∀ n : ℕ, p.index n ≤ q.index n) ∧
    ∀ (n : ℕ) (h : p.index n ≤ q.index n),
      X.map (homOfLE h).op ≫ p.app n = q.app n

/-- Every compatible raw presentation admits a monotone refinement. -/
theorem exists_monotone_refinement
    {C : Type u} [Category.{v} C]
    {X Y : ℕᵒᵖ ⥤ C} (p : RawProMorphismData X Y) :
    ∃ q : ProMorphismData X Y, Refines p q := by
  let hc (n : ℕ) := p.compatible (show n ≤ n + 1 by omega)
  let m (n : ℕ) : ℕ := (hc n).choose
  have hm₀ (n : ℕ) : p.index n ≤ m n := (hc n).choose_spec.1
  have hm₁ (n : ℕ) : p.index (n + 1) ≤ m n := (hc n).choose_spec.2.1
  have hmeq (n : ℕ) :
      X.map (homOfLE (hm₀ n)).op ≫ p.app n =
        X.map (homOfLE (hm₁ n)).op ≫ p.app (n + 1) ≫
          Y.map (homOfLE (show n ≤ n + 1 by omega)).op :=
    (hc n).choose_spec.2.2
  let qidx : ℕ → ℕ :=
    Nat.rec (p.index 0) (fun n z => max (max z (p.index (n + 1))) (m n))
  have hqstep (n : ℕ) : qidx n ≤ qidx (n + 1) := by
    simp [qidx]
  have hqmono : Monotone qidx := by
    intro n n' h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    clear h
    induction d with
    | zero => rfl
    | succ d ih =>
        exact le_trans ih (by simpa [Nat.add_assoc] using hqstep (n + d))
  have hpq (n : ℕ) : p.index n ≤ qidx n := by
    induction n with
    | zero => simp [qidx]
    | succ n ih =>
        exact le_trans (le_max_right _ _) (le_max_left _ _)
  let q : ProMorphismData X Y :=
    { index := qidx
      monotone := hqmono
      app := fun n => X.map (homOfLE (hpq n)).op ≫ p.app n
      naturality := by
        have hadj : ∀ n : ℕ,
            X.map (homOfLE (hqmono (show n ≤ n + 1 by omega))).op ≫
                (X.map (homOfLE (hpq n)).op ≫ p.app n) =
              (X.map (homOfLE (hpq (n + 1))).op ≫ p.app (n + 1)) ≫
                Y.map (homOfLE (show n ≤ n + 1 by omega)).op := by
          intro n
          have hmq : m n ≤ qidx (n + 1) := by
            simp [qidx]
          have hqmp : p.index n ≤ qidx (n + 1) := le_trans (hm₀ n) hmq
          have hqmp' : p.index (n + 1) ≤ qidx (n + 1) :=
            hpq (n + 1)
          have hpath₀ :
              (homOfLE (hqmono (show n ≤ n + 1 by omega))).op ≫
                  (homOfLE (hpq n)).op =
                (homOfLE hqmp).op := by
            apply Subsingleton.elim
          have hpath₁ :
              (homOfLE hqmp).op =
                (homOfLE hmq).op ≫ (homOfLE (hm₀ n)).op := by
            apply Subsingleton.elim
          have hpath₂ :
              (homOfLE hmq).op ≫ (homOfLE (hm₁ n)).op =
                (homOfLE hqmp').op := by
            apply Subsingleton.elim
          rw [← Category.assoc, ← X.map_comp, hpath₀, hpath₁, X.map_comp]
          rw [Category.assoc, hmeq n]
          rw [← Category.assoc, ← X.map_comp, hpath₂]
          simp only [Category.assoc]
        intro n n' h
        refine Nat.le_induction ?_ ?_ n' h
        · simp
        · intro k hk ih
          have hpath :
              (homOfLE (hqmono (show n ≤ k + 1 by omega))).op =
                (homOfLE (hqmono (show k ≤ k + 1 by omega))).op ≫
                  (homOfLE (hqmono hk)).op := by
            apply Subsingleton.elim
          rw [hpath, X.map_comp, Category.assoc, ih]
          have hh := congrArg
            (fun f : X.obj (Opposite.op (qidx (k + 1))) ⟶
                Y.obj (Opposite.op k) => f ≫ Y.map (homOfLE hk).op)
            (hadj k)
          convert hh using 1 <;>
            simp only [Category.assoc, ← Y.map_comp]
          congr 2
          }
  refine ⟨q, ?_⟩
  refine ⟨hpq, ?_⟩
  intro n h
  dsimp [q]

end RawProMorphismData

namespace ProMorphismData

/-- One representative is obtained from another by increasing the source index. -/
def Refines
    {C : Type u} [Category.{v} C]
    {X Y : ℕᵒᵖ ⥤ C}
    (p q : ProMorphismData X Y) : Prop :=
  (∀ n : ℕ, p.index n ≤ q.index n) ∧
    ∀ (n : ℕ) (h : p.index n ≤ q.index n),
      X.map (homOfLE h).op ≫ p.app n = q.app n

/-- Two representatives have the same pro morphism when they admit a common
increasing refinement. -/
def HaveCommonRefinement
    {C : Type u} [Category.{v} C]
    {X Y : ℕᵒᵖ ⥤ C}
    (p q : ProMorphismData X Y) : Prop :=
  ∃ r : ProMorphismData X Y, Refines p r ∧ Refines q r

theorem commonRefinement_is_equivalence
    {C : Type u} [Category.{v} C]
    {X Y : ℕᵒᵖ ⥤ C} :
    Equivalence (HaveCommonRefinement (X := X) (Y := Y)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    refine ⟨p, ?_, ?_⟩
    · refine ⟨fun n => le_rfl, ?_⟩
      intro n h
      simp
    · exact ⟨fun n => le_rfl, by intro n h; simp⟩
  · intro p q h
    rcases h with ⟨r, hpr, hqr⟩
    exact ⟨r, hqr, hpr⟩
  · intro p q r hpq hqr
    have htrans : ∀ {a b c : ProMorphismData X Y},
        Refines a b → Refines b c → Refines a c := by
      intro a b c hab hbc
      refine ⟨fun n => le_trans (hab.1 n) (hbc.1 n), ?_⟩
      intro n h
      rw [← hbc.2 n (hbc.1 n), ← hab.2 n (hab.1 n)]
      rw [← Category.assoc, ← X.map_comp]
      apply congrArg (fun f => X.map f ≫ a.app n)
      apply Subsingleton.elim
    rcases hpq with ⟨s, hps, hqs⟩
    rcases hqr with ⟨t, hqt, hrt⟩
    let u : ProMorphismData X Y :=
      { index := fun n => max (s.index n) (t.index n)
        monotone := by
          intro n n' h
          exact max_le_max (s.monotone h) (t.monotone h)
        app := fun n =>
          X.map (homOfLE (le_max_left (s.index n) (t.index n))).op ≫ s.app n
        naturality := by
          intro n n' h
          rw [← Category.assoc, ← X.map_comp]
          rw [show
            (homOfLE (max_le_max (s.monotone h) (t.monotone h))).op ≫
                (homOfLE (le_max_left (s.index n) (t.index n))).op =
              (homOfLE (le_max_left (s.index n') (t.index n'))).op ≫
                (homOfLE (s.monotone h)).op by
            apply Subsingleton.elim]
          rw [X.map_comp, Category.assoc, s.naturality h]
          simp only [Category.assoc] }
    have hsu : Refines s u := by
      refine ⟨fun n => le_max_left _ _, ?_⟩
      intro n h
      rfl
    have htu : Refines t u := by
      refine ⟨fun n => le_max_right _ _, ?_⟩
      intro n h
      dsimp [u]
      rw [← hqt.2 n (hqt.1 n), ← hqs.2 n (hqs.1 n)]
      rw [← Category.assoc, ← X.map_comp, ← Category.assoc, ← X.map_comp]
      apply congrArg (fun f => X.map f ≫ q.app n)
      apply Subsingleton.elim
    exact ⟨u, htrans hps hsu, htrans hrt htu⟩

end ProMorphismData

/-- The copresheaf represented by a cofiltered diagram at an object. -/
noncomputable def proCopresheafAt
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    (F : I ⥤ C) (X : C)
    [HasColimit (F.op ⋙ yoneda.obj X)] : Type v' :=
  colimit (F.op ⋙ yoneda.obj X)

/-- The copresheaf `X ↦ colim_i Hom(F(i),X)`. -/
noncomputable def proCopresheaf
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    (F : I ⥤ C) [HasColimitsOfShape Iᵒᵖ (Type v')] :
    C ⥤ Type v' where
  obj X := colimit (F.op ⋙ yoneda.obj X)
  map {X Y} f := colim.map (Functor.whiskerLeft F.op (yoneda.map f))
  map_id := by
    intro X
    apply colimit.hom_ext
    intro i
    simp
  map_comp := by
    intro X Y Z f g
    apply colimit.hom_ext
    intro i
    simp [Functor.map_comp]

private noncomputable def proCopresheafToFunctorColimit
    {J : Type v} [SmallCategory J]
    {C : Type u} [Category.{v} C]
    [HasColimitsOfShape Jᵒᵖ (Type v)]
    (G : J ⥤ C) :
    proCopresheaf G ≅ colimit (G.op ⋙ coyoneda) := by
  refine NatIso.ofComponents
    (fun X => (colimitObjIsoColimitCompEvaluation (G.op ⋙ coyoneda) X).symm) ?_
  intro X Y f
  dsimp [proCopresheaf]
  apply colimit.hom_ext
  intro i
  simp only [Functor.whiskerLeft, ι_colimMap_assoc,
    colimitObjIsoColimitCompEvaluation_inv_colimit_map, Category.assoc]
  rfl

private noncomputable def proIndColimitToCopresheafIso
    {J : Type v} [SmallCategory J]
    {C : Type u} [Category.{v} C]
    [HasColimitsOfShape Jᵒᵖ (Type v)]
    (G : J ⥤ C) :
    ((Functor.whiskeringLeft C Cᵒᵖᵒᵖ (Type v)).obj (opOp C)).obj
        (colimit (G.op ⋙ yoneda (C := Cᵒᵖ))) ≅
      proCopresheaf G := by
  let w := Coyoneda.opIso (C := C)
  let k := colimitCompWhiskeringLeftIsoCompColimit
    (G.op ⋙ yoneda (C := Cᵒᵖ)) (opOp C)
  let z := HasColimit.isoOfNatIso (Functor.isoWhiskerLeft G.op w)
  exact k.symm.trans (z.trans (proCopresheafToFunctorColimit G).symm)

/-- The pro-morphism formula in terms of copresheaf transformations. -/
theorem proCategory_hom_as_copresheaf_natTrans
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    [IsCofiltered I] [IsCofiltered J]
    {C : Type u} [Category.{v} C]
    [HasColimitsOfShape Iᵒᵖ (Type v)]
    [HasColimitsOfShape Jᵒᵖ (Type v)]
    (F : I ⥤ C) (G : J ⥤ C) :
    Nonempty
      (((proLim I).obj F ⟶ (proLim J).obj G) ≃
        (proCopresheaf G ⟶ proCopresheaf F)) := by
  let o := opEquiv
    (Opposite.op ((Ind.lim Iᵒᵖ).obj F.op))
      (Opposite.op ((Ind.lim Jᵒᵖ).obj G.op))
  refine ⟨o.trans ?_⟩
  refine (Ind.inclusion.fullyFaithful (C := Cᵒᵖ)).homEquiv.trans ?_
  refine (Iso.homCongr (Ind.limCompInclusion.app G.op)
      (Ind.limCompInclusion.app F.op)).trans ?_
  let L := (Functor.whiskeringLeft C Cᵒᵖᵒᵖ (Type v)).obj (opOp C)
  let qG := proIndColimitToCopresheafIso G
  let qF := proIndColimitToCopresheafIso F
  exact (Functor.FullyFaithful.ofFullyFaithful L).homEquiv.trans
    (qG.homCongr qF)

/-- A functor carries ind-essentially constant diagrams to ind-essentially
constant diagrams. -/
theorem isEssentiallyConstantInd_comp
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    {D : Type w} [Category.{w'} D]
    (F : C ⥤ D) {M : I ⥤ C}
    (hM : IsEssentiallyConstantIndDiagram M) :
    IsEssentiallyConstantIndDiagram (M ⋙ F) := by
  rcases hM with ⟨c, hc⟩
  rcases hc with ⟨i, s, hs, hfactor⟩
  refine ⟨F.mapCocone c, ?_⟩
  refine ⟨i, F.map s, ?_, ?_⟩
  · simpa [Functor.mapCocone_ι_app, Functor.mapCocone_pt, Functor.comp_map] using congrArg F.map hs
  · intro j
    rcases hfactor j with ⟨k, f, g, hfg⟩
    refine ⟨k, f, g, ?_⟩
    simpa [Functor.mapCocone_ι_app, Functor.comp_map, Functor.map_comp] using congrArg F.map hfg

/-- A functor carries pro-essentially constant diagrams to pro-essentially
constant diagrams. -/
theorem isEssentiallyConstantPro_comp
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    {D : Type w} [Category.{w'} D]
    (F : C ⥤ D) {M : I ⥤ C}
    (hM : IsEssentiallyConstantProDiagram M) :
    IsEssentiallyConstantProDiagram (M ⋙ F) := by
  rcases hM with ⟨c, hc⟩
  rcases hc with ⟨i, r, hr, hfactor⟩
  refine ⟨F.mapCone c, ?_⟩
  refine ⟨i, F.map r, ?_, ?_⟩
  · simpa [Functor.mapCone_π_app, Functor.mapCone_pt, Functor.comp_map] using congrArg F.map hr
  · intro j
    rcases hfactor j with ⟨k, f, g, hfg⟩
    refine ⟨k, f, g, ?_⟩
    simpa [Functor.mapCone_π_app, Functor.comp_map, Functor.map_comp] using congrArg F.map hfg

/-! ## Hom-set characterizations -/

/-- The covariant hom diagram `W ↦ Hom(W,M_i)`.  It is the typed form of
`M ⋙ coyoneda.obj (op W)`; writing the components explicitly avoids casts
between `op (unop W)` and `W` in the hom-set conditions. -/
abbrev homIntoDiagram
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) (W : C) : I ⥤ Type v' :=
  { obj := fun i => W ⟶ M.obj i
    map := fun {i j} (f : i ⟶ j) =>
      TypeCat.ofHom (fun g : W ⟶ M.obj i => g ≫ M.map f)
    map_id := by
      intro i
      ext g
      simp
    map_comp := by
      intro i j k f g
      ext h
      simp [Category.assoc] }

/-- The contravariant hom diagram `i ↦ Hom(M_i,W)`.  It is the typed form of
`M.op ⋙ yoneda.obj W`. -/
abbrev homFromDiagram
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) (W : C) : Iᵒᵖ ⥤ Type v' :=
  { obj := fun i => M.obj i.unop ⟶ W
    map := fun {i j} (f : i ⟶ j) =>
      TypeCat.ofHom (fun g : M.obj i.unop ⟶ W => M.map f.unop ≫ g)
    map_id := by
      intro i
      ext g
      simp
    map_comp := by
      intro i j k f g
      ext h
      simp [Category.assoc] }

/-- Precomposition on the covariant hom diagrams. -/
def precomposeHomInto
    {J : Type u} [Category.{v} J]
    {C : Type u'} [Category.{v'} C]
    {A B : C} (G : J ⥤ C) (f : A ⟶ B) :
    homIntoDiagram G B ⟶ homIntoDiagram G A where
  app := fun j =>
    TypeCat.ofHom (fun g : B ⟶ G.obj j => f ≫ g)
  naturality := by
    intro i j g
    ext h
    simp [Category.assoc]

/-- The diagram whose limit is the ind-category hom formula
`lim_i colim_j Hom(F(i),G(j))`. -/
def indHomFormulaDiagram
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    {C : Type u} [Category.{v} C]
    [HasColimitsOfShape J (Type v)]
    (F : I ⥤ C) (G : J ⥤ C) : Iᵒᵖ ⥤ Type v where
  obj i := colimit (homIntoDiagram G (F.obj i.unop))
  map {i j} f :=
    colim.map (precomposeHomInto G (F.map f.unop))
  map_id := by
    intro i
    apply colimit.hom_ext
    intro j
    ext h
    simp [precomposeHomInto]
  map_comp := by
    intro i j k f g
    apply colimit.hom_ext
    intro l
    ext h
    simp [precomposeHomInto, Category.assoc]

/-- The ind-category hom-set formula from the source's ind-category remark. -/
theorem indCategory_hom_formula
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    [IsFiltered I] [IsFiltered J]
    {C : Type u} [Category.{v} C]
    [HasColimitsOfShape J (Type v)]
    (F : I ⥤ C) (G : J ⥤ C)
    [HasLimit (indHomFormulaDiagram F G)] :
    Nonempty
      (((indLim I).obj F ⟶ (indLim J).obj G) ≃
        limit (indHomFormulaDiagram F G)) := by
  refine ⟨(Ind.inclusion.fullyFaithful (C := C)).homEquiv.trans ?_⟩
  refine (Iso.homCongr (Ind.limCompInclusion.app F)
      (Ind.limCompInclusion.app G)).trans ?_
  have hobj (i : Iᵒᵖ) :
      colimit (homIntoDiagram G (F.obj i.unop)) =
        (indHomFormulaDiagram F G).obj i := by
    rfl
  let w (i : Iᵒᵖ) :
      ((G ⋙ yoneda) ⋙
          (Functor.whiskeringLeft Iᵒᵖ Cᵒᵖ (Type v)).obj F.op) ⋙
        (evaluation Iᵒᵖ (Type v)).obj i ≅
      homIntoDiagram G (F.obj i.unop) :=
    NatIso.ofComponents
      (fun j =>
        show
          (((G ⋙ yoneda) ⋙
              (Functor.whiskeringLeft Iᵒᵖ Cᵒᵖ (Type v)).obj F.op).obj j).obj i ≅
            (homIntoDiagram G (F.obj i.unop)).obj j
        from Iso.refl (F.obj i.unop ⟶ G.obj j))
      (by
        intro j k f
        ext h
        simp [homIntoDiagram])
  let hdiag : F.op ⋙ colimit (G ⋙ yoneda) ≅ indHomFormulaDiagram F G :=
    (colimitCompWhiskeringLeftIsoCompColimit (G ⋙ yoneda) F.op).symm.trans
      (NatIso.ofComponents
        (fun i =>
          (colimitObjIsoColimitCompEvaluation
              ((G ⋙ yoneda) ⋙
                (Functor.whiskeringLeft Iᵒᵖ Cᵒᵖ (Type v)).obj F.op) i).trans
            ((HasColimit.isoOfNatIso (w i)).trans (eqToIso (hobj i))))
        (by
          intro i j f
          dsimp only [Iso.trans_hom]
          rw [← Category.assoc, colimit_map_colimitObjIsoColimitCompEvaluation_hom]
          simp only [Category.assoc]
          have hi :
              colimMap
                  (((G ⋙ yoneda) ⋙
                      (Functor.whiskeringLeft Iᵒᵖ Cᵒᵖ (Type v)).obj F.op).whiskerLeft
                    ((evaluation Iᵒᵖ (Type v)).map f)) ≫
                  (HasColimit.isoOfNatIso (w j)).hom ≫
                    (eqToIso (hobj j)).hom =
                (HasColimit.isoOfNatIso (w i)).hom ≫
                  (eqToIso (hobj i)).hom ≫
                    (indHomFormulaDiagram F G).map f := by
            apply colimit.hom_ext
            intro k
            cases hobj i
            cases hobj j
            simp [indHomFormulaDiagram, homIntoDiagram, precomposeHomInto, w]
          simpa only [Category.assoc] using
            congrArg
              (fun q =>
                (colimitObjIsoColimitCompEvaluation
                  ((G ⋙ yoneda) ⋙
                    (Functor.whiskeringLeft Iᵒᵖ Cᵒᵖ (Type v)).obj F.op) i).hom ≫ q) hi))
  exact (colimitYonedaHomEquiv F (colimit (G ⋙ yoneda))).trans
    (HasLimit.isoOfNatIso hdiag).toEquiv

/-- The pro-category hom-set formula, expressed as the opposite ind formula. -/
theorem proCategory_hom_formula
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    [IsCofiltered I] [IsCofiltered J]
    {C : Type u} [Category.{v} C]
    [HasColimitsOfShape Iᵒᵖ (Type v)]
    (F : I ⥤ C) (G : J ⥤ C)
    [HasLimit (indHomFormulaDiagram (F := G.op) (G := F.op))] :
    Nonempty
      (((proLim I).obj F ⟶ (proLim J).obj G) ≃
        limit (indHomFormulaDiagram (F := G.op) (G := F.op))) := by
  obtain ⟨e⟩ := indCategory_hom_formula (F := G.op) (G := F.op)
  let o := opEquiv
    (Opposite.op ((indLim Iᵒᵖ).obj F.op))
      (Opposite.op ((indLim Jᵒᵖ).obj G.op))
  exact ⟨o.trans e⟩

/-- The cocone induced on `Hom(W,-)` by a cocone on `M`. -/
def homIntoCocone
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cocone M) (W : C) :
    Cocone (homIntoDiagram M W) where
  pt := W ⟶ c.pt
  ι :=
    { app := fun i =>
          TypeCat.ofHom (fun f : W ⟶ M.obj i =>
            f ≫ (c.ι.app i : M.obj i ⟶ c.pt))
      naturality := by
        intro i j f
        ext g
        simp [Category.assoc] }

/-- The cocone induced on `Hom(-,W)` by a cone on `M`. -/
def homFromCocone
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cone M) (W : C) :
    Cocone (homFromDiagram M W) where
  pt := c.pt ⟶ W
  ι :=
    { app := fun i =>
          TypeCat.ofHom (fun f : M.obj i.unop ⟶ W =>
            (c.π.app i.unop : c.pt ⟶ M.obj i.unop) ≫ f)
      naturality := by
        intro i j f
        ext g
        simp }

/-- The map on hom sets induced by an ind cocone. -/
noncomputable def homIntoCoconeMap
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cocone M) (W : C)
    [HasColimit (homIntoDiagram M W)] :
    colimit (homIntoDiagram M W) → (W ⟶ c.pt) :=
  colimit.desc (homIntoDiagram M W) (homIntoCocone c W)

/-- The map on hom sets induced by a pro cone. -/
noncomputable def homFromCoconeMap
    {I : Type u} [Category.{v} I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cone M) (W : C)
    [HasColimit (homFromDiagram M W)] :
    colimit (homFromDiagram M W) → (c.pt ⟶ W) :=
  colimit.desc (homFromDiagram M W) (homFromCocone c W)

/-- The first three ind hom-set formulations, with the existence of the
set-valued colimits made explicit. -/
def IndHomColimitCondition
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) : Prop :=
  ∃ c : Cocone M, ∀ W : C, ∃ hW : HasColimit (homIntoDiagram M W),
    letI : HasColimit (homIntoDiagram M W) := hW
    Function.Bijective (homIntoCoconeMap c W)

def IndHomColimitAndIsColimitCondition
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) : Prop :=
  ∃ c : Cocone M, Nonempty (IsColimit c) ∧
    ∀ W : C, ∃ hW : HasColimit (homIntoDiagram M W),
      letI : HasColimit (homIntoDiagram M W) := hW
      Function.Bijective (homIntoCoconeMap c W)

/-- The fourth ind hom-set formulation, using a section at one stage. -/
def IndHomSectionCondition
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) : Prop :=
  ∃ (X : C) (i : I) (s : X ⟶ M.obj i),
    ∀ W : C, ∃ hW : HasColimit (homIntoDiagram M W),
      letI : HasColimit (homIntoDiagram M W) := hW
      Function.Bijective
        (fun f : W ⟶ X =>
          colimit.ι (homIntoDiagram M W) i (f ≫ s))

private theorem essentiallyConstantInd_of_homIntoCoconeMap
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cocone M)
    (hc : ∀ W : C, ∃ hW : HasColimit (homIntoDiagram M W),
      letI : HasColimit (homIntoDiagram M W) := hW
      Function.Bijective (homIntoCoconeMap c W)) :
    IsEssentiallyConstantInd M c := by
  obtain ⟨hW, hbij⟩ := hc c.pt
  letI := hW
  have hmap (j : I) (f : c.pt ⟶ M.obj j) :
      homIntoCoconeMap c c.pt (colimit.ι (homIntoDiagram M c.pt) j f) =
        f ≫ c.ι.app j := by
    change
      (colimit.desc (homIntoDiagram M c.pt) (homIntoCocone c c.pt))
          (colimit.ι (homIntoDiagram M c.pt) j f) =
        f ≫ c.ι.app j
    exact congrArg (fun q => q f) (colimit.ι_desc (homIntoCocone c c.pt) j)
  obtain ⟨x, hx⟩ := hbij.2 (𝟙 c.pt)
  obtain ⟨i, s, rfl⟩ := Concrete.colimit_exists_rep (homIntoDiagram M c.pt) x
  change c.pt ⟶ M.obj i at s
  have hs : s ≫ c.ι.app i = 𝟙 c.pt := by
    simpa only [hmap] using hx
  refine ⟨i, s, hs, ?_⟩
  intro j
  obtain ⟨hWj, hbijj⟩ := hc (M.obj j)
  letI := hWj
  have hmapj (j' : I) (f : M.obj j ⟶ M.obj j') :
      homIntoCoconeMap c (M.obj j)
          (colimit.ι (homIntoDiagram M (M.obj j)) j' f) =
        f ≫ c.ι.app j' := by
    change
      (colimit.desc (homIntoDiagram M (M.obj j))
          (homIntoCocone c (M.obj j)))
          (colimit.ι (homIntoDiagram M (M.obj j)) j' f) =
        f ≫ c.ι.app j'
    exact congrArg (fun q => q f)
      (colimit.ι_desc (homIntoCocone c (M.obj j)) j')
  have heq :
      colimit.ι (homIntoDiagram M (M.obj j)) j (𝟙 (M.obj j)) =
        colimit.ι (homIntoDiagram M (M.obj j)) i (c.ι.app j ≫ s) := by
    apply hbijj.1
    rw [hmapj, hmapj]
    simpa [Category.assoc] using
      (congrArg (fun q => c.ι.app j ≫ q) hs).symm
  obtain ⟨k, f, g, hfg⟩ :=
    (Types.FilteredColimit.colimit_eq_iff (homIntoDiagram M (M.obj j))).1 heq
  refine ⟨k, g, f, ?_⟩
  simpa [homIntoDiagram, Category.assoc] using hfg

private theorem indHomColimitCondition_iff_essentiallyConstant
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    IsEssentiallyConstantIndDiagram M ↔ IndHomColimitCondition M := by
  constructor
  · rintro ⟨c, ⟨i, s, hs, hfactor⟩⟩
    refine ⟨c, ?_⟩
    intro W
    let tc : Functor.CoconeTypes (homIntoDiagram M W) :=
      { pt := W ⟶ c.pt
        ι := fun j f => f ≫ c.ι.app j
        ι_naturality := by
          intro j j' f
          funext g
          simp [Category.assoc] }
    have htc : tc.IsColimit := by
      constructor
      constructor
      · intro x y hxy
        obtain ⟨j, xj, rfl⟩ :=
          (homIntoDiagram M W).ιColimitType_jointly_surjective x
        obtain ⟨j', yj, rfl⟩ :=
          (homIntoDiagram M W).ιColimitType_jointly_surjective y
        change xj ≫ c.ι.app j = yj ≫ c.ι.app j' at hxy
        rcases hfactor j with ⟨k, f, g, hfg⟩
        rcases hfactor j' with ⟨k', f', g', hfg'⟩
        let u := IsFiltered.leftToMax k k'
        let v := IsFiltered.rightToMax k k'
        let t := IsFiltered.coeqHom (f ≫ u) (f' ≫ v)
        apply (Functor.ιColimitType_eq_iff_of_isFiltered (homIntoDiagram M W) xj yj).mpr
        refine ⟨IsFiltered.coeq (f ≫ u) (f' ≫ v), g ≫ u ≫ t, g' ≫ v ≫ t, ?_⟩
        change xj ≫ M.map (g ≫ u ≫ t) = yj ≫ M.map (g' ≫ v ≫ t)
        have hpaths : f ≫ u ≫ t = f' ≫ v ≫ t := by
          simpa [t, Category.assoc] using
            IsFiltered.coeq_condition (f ≫ u) (f' ≫ v)
        calc
          xj ≫ M.map (g ≫ u ≫ t) = xj ≫ M.map g ≫ M.map u ≫ M.map t := by
            rw [M.map_comp, M.map_comp]
          _ = xj ≫ (c.ι.app j ≫ s ≫ M.map f) ≫ M.map u ≫ M.map t := by
            rw [hfg]
          _ = (xj ≫ c.ι.app j) ≫ s ≫ M.map (f ≫ u ≫ t) := by
            simp only [Category.assoc, M.map_comp]
          _ = (yj ≫ c.ι.app j') ≫ s ≫ M.map (f' ≫ v ≫ t) := by
            rw [hxy, hpaths]
          _ = yj ≫ (c.ι.app j' ≫ s ≫ M.map f') ≫ M.map v ≫ M.map t := by
            simp only [M.map_comp, Category.assoc]
          _ = yj ≫ M.map (g' ≫ v ≫ t) := by
            rw [← hfg']
            simp only [M.map_comp, Category.assoc]
      · intro z
        refine ⟨(homIntoDiagram M W).ιColimitType i (z ≫ s), ?_⟩
        simp [tc, Category.assoc, hs]
    have hcol : Nonempty (IsColimit (homIntoCocone c W)) := by
      exact (Functor.CoconeTypes.isColimit_iff (c := tc)).mp htc
    let hW : HasColimit (homIntoDiagram M W) :=
      ⟨⟨homIntoCocone c W, hcol.some⟩⟩
    refine ⟨hW, ?_⟩
    letI := hW
    have hmap (j : I) (f : W ⟶ M.obj j) :
        homIntoCoconeMap c W (colimit.ι (homIntoDiagram M W) j f) =
          f ≫ c.ι.app j := by
      change
        (colimit.desc (homIntoDiagram M W) (homIntoCocone c W))
            (colimit.ι (homIntoDiagram M W) j f) =
          f ≫ c.ι.app j
      exact congrArg (fun q => q f) (colimit.ι_desc (homIntoCocone c W) j)
    constructor
    · intro x y hxy
      obtain ⟨j, xj, rfl⟩ := Concrete.colimit_exists_rep (homIntoDiagram M W) x
      obtain ⟨j', yj, rfl⟩ := Concrete.colimit_exists_rep (homIntoDiagram M W) y
      change W ⟶ M.obj j at xj
      change W ⟶ M.obj j' at yj
      have hxy' : xj ≫ c.ι.app j = yj ≫ c.ι.app j' := by
        rw [hmap, hmap] at hxy
        exact hxy
      rcases hfactor j with ⟨k, f, g, hfg⟩
      rcases hfactor j' with ⟨k', f', g', hfg'⟩
      let l := IsFiltered.max k k'
      let u := IsFiltered.leftToMax k k'
      let v := IsFiltered.rightToMax k k'
      let t := IsFiltered.coeqHom (f ≫ u) (f' ≫ v)
      apply Concrete.colimit_rep_eq_of_exists (homIntoDiagram M W) _ _
      refine ⟨IsFiltered.coeq (f ≫ u) (f' ≫ v), g ≫ u ≫ t, g' ≫ v ≫ t, ?_⟩
      change xj ≫ M.map (g ≫ u ≫ t) = yj ≫ M.map (g' ≫ v ≫ t)
      have hpaths : f ≫ u ≫ t = f' ≫ v ≫ t :=
        by simpa [t, Category.assoc] using
          IsFiltered.coeq_condition (f ≫ u) (f' ≫ v)
      calc
        xj ≫ M.map (g ≫ u ≫ t) = xj ≫ M.map g ≫ M.map u ≫ M.map t := by
          rw [M.map_comp, M.map_comp]
        _ = xj ≫ (c.ι.app j ≫ s ≫ M.map f) ≫ M.map u ≫ M.map t := by rw [hfg]
        _ = (xj ≫ c.ι.app j) ≫ s ≫ M.map (f ≫ u ≫ t) := by
          simp only [Category.assoc, M.map_comp]
        _ = (yj ≫ c.ι.app j') ≫ s ≫ M.map (f' ≫ v ≫ t) := by
          rw [hxy', hpaths]
        _ = yj ≫ (c.ι.app j' ≫ s ≫ M.map f') ≫ M.map v ≫ M.map t := by
          simp only [M.map_comp, Category.assoc]
        _ = yj ≫ M.map (g' ≫ v ≫ t) := by
          rw [← hfg']
          simp only [M.map_comp, Category.assoc]
    · intro f
      refine ⟨colimit.ι (homIntoDiagram M W) i (f ≫ s), ?_⟩
      rw [hmap]
      rw [Category.assoc, hs, Category.comp_id]
  · rintro ⟨c, hc⟩
    exact ⟨c, essentiallyConstantInd_of_homIntoCoconeMap c hc⟩

private theorem indHomColimitCondition_iff_isColimitCondition
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    IndHomColimitCondition M ↔ IndHomColimitAndIsColimitCondition M := by
  constructor
  · intro h
    rcases h with ⟨c, hc⟩
    have hce : IsEssentiallyConstantInd M c :=
      essentiallyConstantInd_of_homIntoCoconeMap c hc
    exact ⟨c, isColimit_of_essentiallyConstantInd c hce, hc⟩
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩

private theorem homInto_colimit_precompose_eq
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) {W W' : C}
    [HasColimit (homIntoDiagram M W)]
    [HasColimit (homIntoDiagram M W')]
    (f : W' ⟶ W) {i j : I} (x : W ⟶ M.obj i) (y : W ⟶ M.obj j)
    (h : colimit.ι (homIntoDiagram M W) i x =
      colimit.ι (homIntoDiagram M W) j y) :
    colimit.ι (homIntoDiagram M W') i (f ≫ x) =
      colimit.ι (homIntoDiagram M W') j (f ≫ y) := by
  apply (Types.FilteredColimit.colimit_eq_iff
    (homIntoDiagram M W')).2
  obtain ⟨k, p, q, hpq⟩ :=
    (Types.FilteredColimit.colimit_eq_iff (homIntoDiagram M W)).1 h
  refine ⟨k, p, q, ?_⟩
  simpa [homIntoDiagram, Category.assoc] using congrArg (fun z => f ≫ z) hpq

private theorem indHomColimitAndIsColimitCondition_iff_section
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    IndHomColimitAndIsColimitCondition M ↔ IndHomSectionCondition M := by
  constructor
  · rintro ⟨c, _, hall⟩
    obtain ⟨hX, hbijX⟩ := hall c.pt
    letI := hX
    have hmapX (j : I) (f : c.pt ⟶ M.obj j) :
        homIntoCoconeMap c c.pt (colimit.ι (homIntoDiagram M c.pt) j f) =
          f ≫ c.ι.app j := by
      change
        (colimit.desc (homIntoDiagram M c.pt) (homIntoCocone c c.pt))
            (colimit.ι (homIntoDiagram M c.pt) j f) =
          f ≫ c.ι.app j
      exact congrArg (fun q => q f) (colimit.ι_desc (homIntoCocone c c.pt) j)
    obtain ⟨x, hx⟩ := hbijX.2 (𝟙 c.pt)
    obtain ⟨i, s, rfl⟩ := Concrete.colimit_exists_rep (homIntoDiagram M c.pt) x
    change c.pt ⟶ M.obj i at s
    have hs : s ≫ c.ι.app i = 𝟙 c.pt := by
      simpa only [hmapX] using hx
    refine ⟨c.pt, i, s, ?_⟩
    intro W
    obtain ⟨hW, hbij⟩ := hall W
    letI := hW
    have hmap (j : I) (f : W ⟶ M.obj j) :
        homIntoCoconeMap c W (colimit.ι (homIntoDiagram M W) j f) =
          f ≫ c.ι.app j := by
      change
        (colimit.desc (homIntoDiagram M W) (homIntoCocone c W))
            (colimit.ι (homIntoDiagram M W) j f) =
          f ≫ c.ι.app j
      exact congrArg (fun q => q f) (colimit.ι_desc (homIntoCocone c W) j)
    refine ⟨hW, ?_⟩
    constructor
    · intro f g hfg
      have hq := congrArg (homIntoCoconeMap c W) hfg
      simpa only [hmap, Category.assoc, hs, Category.comp_id] using hq
    · intro x
      refine ⟨homIntoCoconeMap c W x, ?_⟩
      apply hbij.1
      change
        homIntoCoconeMap c W
            (colimit.ι (homIntoDiagram M W) i
              (homIntoCoconeMap c W x ≫ s)) =
          homIntoCoconeMap c W x
      rw [hmap]
      simp [Category.assoc, hs]
  · rintro ⟨X, i, s, hsec⟩
    let hW : ∀ W : C, HasColimit (homIntoDiagram M W) :=
      fun W => (hsec W).choose
    have hbij (W : C) :
        letI : HasColimit (homIntoDiagram M W) := hW W
        Function.Bijective
          (fun f : W ⟶ X =>
            colimit.ι (homIntoDiagram M W) i (f ≫ s)) := by
      exact (hsec W).choose_spec
    let cι : ∀ j : I, M.obj j ⟶ X := fun j =>
      let hWj := hW (M.obj j)
      letI := hWj
      Classical.choose ((hbij (M.obj j)).2
        (colimit.ι (homIntoDiagram M (M.obj j)) j (𝟙 (M.obj j)))
        )
    let c : Cocone M :=
      { pt := X
        ι :=
          { app := cι
            naturality := by
              intro j k f
              let hWj := hW (M.obj j)
              let hWk := hW (M.obj k)
              letI := hWj
              letI := hWk
              have hj :
                  colimit.ι (homIntoDiagram M (M.obj j)) i (cι j ≫ s) =
                    colimit.ι (homIntoDiagram M (M.obj j)) j (𝟙 (M.obj j)) := by
                dsimp [cι]
                exact Classical.choose_spec ((hbij (M.obj j)).2
                  (colimit.ι (homIntoDiagram M (M.obj j)) j (𝟙 (M.obj j))))
              have hk :
                  colimit.ι (homIntoDiagram M (M.obj k)) i (cι k ≫ s) =
                    colimit.ι (homIntoDiagram M (M.obj k)) k (𝟙 (M.obj k)) := by
                dsimp [cι]
                exact Classical.choose_spec ((hbij (M.obj k)).2
                  (colimit.ι (homIntoDiagram M (M.obj k)) k (𝟙 (M.obj k))))
              have ht := homInto_colimit_precompose_eq M (M.map f)
                (cι k ≫ s) (𝟙 (M.obj k)) hk
              have hfj :
                  colimit.ι (homIntoDiagram M (M.obj j)) k (M.map f) =
                    colimit.ι (homIntoDiagram M (M.obj j)) j (𝟙 (M.obj j)) := by
                apply (Types.FilteredColimit.colimit_eq_iff
                  (homIntoDiagram M (M.obj j))).2
                refine ⟨k, 𝟙 k, f, ?_⟩
                simp [homIntoDiagram]
              have ht' :
                  colimit.ι (homIntoDiagram M (M.obj j)) i
                      ((M.map f ≫ cι k) ≫ s) =
                    colimit.ι (homIntoDiagram M (M.obj j)) j (𝟙 (M.obj j)) := by
                have ht' :
                    colimit.ι (homIntoDiagram M (M.obj j)) i
                        ((M.map f ≫ cι k) ≫ s) =
                      colimit.ι (homIntoDiagram M (M.obj j)) k (M.map f) := by
                  simpa [Category.assoc] using ht
                exact ht'.trans hfj
              apply (hbij (M.obj j)).1
              simpa [Functor.const_obj_map, Category.assoc] using
                ht'.trans hj.symm } }
    have hs : s ≫ cι i = 𝟙 X := by
      let hWi := hW (M.obj i)
      let hWX := hW X
      letI := hWi
      have hi :
          colimit.ι (homIntoDiagram M (M.obj i)) i (cι i ≫ s) =
            colimit.ι (homIntoDiagram M (M.obj i)) i (𝟙 (M.obj i)) := by
        dsimp [cι]
        exact Classical.choose_spec ((hbij (M.obj i)).2
          (colimit.ι (homIntoDiagram M (M.obj i)) i (𝟙 (M.obj i))))
      letI := hWX
      have ht := homInto_colimit_precompose_eq M s (cι i ≫ s) (𝟙 (M.obj i)) hi
      apply (hbij X).1
      change
        colimit.ι (homIntoDiagram M X) i ((s ≫ cι i) ≫ s) =
          colimit.ι (homIntoDiagram M X) i (𝟙 X ≫ s)
      simpa [Category.assoc] using ht
    have hce : IsEssentiallyConstantInd M c := by
      refine ⟨i, s, ?_, ?_⟩
      · simpa [c, hs]
      · intro j
        let hWj := hW (M.obj j)
        letI := hWj
        have hj :
            colimit.ι (homIntoDiagram M (M.obj j)) i (cι j ≫ s) =
              colimit.ι (homIntoDiagram M (M.obj j)) j (𝟙 (M.obj j)) := by
          dsimp [cι]
          exact Classical.choose_spec ((hbij (M.obj j)).2
            (colimit.ι (homIntoDiagram M (M.obj j)) j (𝟙 (M.obj j))))
        obtain ⟨k, f, g, hfg⟩ :=
          (Types.FilteredColimit.colimit_eq_iff
            (homIntoDiagram M (M.obj j))).1 hj
        refine ⟨k, f, g, ?_⟩
        simpa [c, homIntoDiagram, Category.assoc] using hfg.symm
    have hc : ∀ W : C, ∃ hW' : HasColimit (homIntoDiagram M W),
        letI : HasColimit (homIntoDiagram M W) := hW'
        Function.Bijective (homIntoCoconeMap c W) := by
      intro W
      let hWW := hW W
      letI := hWW
      have hmap (j : I) (f : W ⟶ M.obj j) :
          homIntoCoconeMap c W (colimit.ι (homIntoDiagram M W) j f) =
            f ≫ cι j := by
        change
          (colimit.desc (homIntoDiagram M W) (homIntoCocone c W))
              (colimit.ι (homIntoDiagram M W) j f) =
            f ≫ cι j
        exact congrArg (fun q => q f) (colimit.ι_desc (homIntoCocone c W) j)
      have hleft (f : W ⟶ X) :
          homIntoCoconeMap c W
              (colimit.ι (homIntoDiagram M W) i (f ≫ s)) = f := by
        rw [hmap]
        simp [c, Category.assoc, hs]
      have hright (x : colimit (homIntoDiagram M W)) :
          colimit.ι (homIntoDiagram M W) i
              (homIntoCoconeMap c W x ≫ s) = x := by
        obtain ⟨j, f, rfl⟩ := Concrete.colimit_exists_rep (homIntoDiagram M W) x
        let hWj := hW (M.obj j)
        letI := hWj
        have hj :
            colimit.ι (homIntoDiagram M (M.obj j)) i (cι j ≫ s) =
              colimit.ι (homIntoDiagram M (M.obj j)) j (𝟙 (M.obj j)) := by
          dsimp [cι]
          exact Classical.choose_spec ((hbij (M.obj j)).2
            (colimit.ι (homIntoDiagram M (M.obj j)) j (𝟙 (M.obj j))))
        have ht := homInto_colimit_precompose_eq M f (cι j ≫ s) (𝟙 (M.obj j)) hj
        rw [hmap]
        simpa [Category.assoc] using ht
      refine ⟨hWW, ?_⟩
      constructor
      · intro x y hxy
        calc
          x = colimit.ι (homIntoDiagram M W) i
              (homIntoCoconeMap c W x ≫ s) := (hright x).symm
          _ = colimit.ι (homIntoDiagram M W) i
              (homIntoCoconeMap c W y ≫ s) :=
            congrArg (fun z => colimit.ι (homIntoDiagram M W) i (z ≫ s)) hxy
          _ = y := hright y
      · intro f
        exact ⟨colimit.ι (homIntoDiagram M W) i (f ≫ s), hleft f⟩
    exact ⟨c, isColimit_of_essentiallyConstantInd c hce, hc⟩

def ProHomLimitCondition
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) : Prop :=
  ∃ c : Cone M, ∀ W : C, ∃ hW : HasColimit (homFromDiagram M W),
    letI : HasColimit (homFromDiagram M W) := hW
    Function.Bijective (homFromCoconeMap c W)

def ProHomLimitAndIsLimitCondition
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) : Prop :=
  ∃ c : Cone M, Nonempty (IsLimit c) ∧
    ∀ W : C, ∃ hW : HasColimit (homFromDiagram M W),
      letI : HasColimit (homFromDiagram M W) := hW
      Function.Bijective (homFromCoconeMap c W)

def ProHomSectionCondition
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) : Prop :=
  ∃ (X : C) (i : I) (r : M.obj i ⟶ X),
    ∀ W : C, ∃ hW : HasColimit (homFromDiagram M W),
      letI : HasColimit (homFromDiagram M W) := hW
      Function.Bijective
        (fun f : X ⟶ W =>
          colimit.ι (homFromDiagram M W) (Opposite.op i) (r ≫ f))

/-- The ind characterization by the three equivalent hom-set formulations. -/
theorem characterizeEssentiallyConstantInd
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
      (IsEssentiallyConstantIndDiagram M ↔ IndHomColimitCondition M) ∧
      (IndHomColimitCondition M ↔ IndHomColimitAndIsColimitCondition M) ∧
      (IndHomColimitAndIsColimitCondition M ↔ IndHomSectionCondition M) := by
  exact ⟨indHomColimitCondition_iff_essentiallyConstant M,
    indHomColimitCondition_iff_isColimitCondition M,
    indHomColimitAndIsColimitCondition_iff_section M⟩

/-- The pro dual characterization by the three equivalent hom-set formulations. -/
private noncomputable def homIntoDiagram_op_iso
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) (W : C) :
    homIntoDiagram M.op (Opposite.op W) ≅ homFromDiagram M W := by
  refine NatIso.ofComponents
    (fun i => (opEquiv (Opposite.op W) (Opposite.op (M.obj i.unop))).toIso) ?_
  intro i j f
  ext g
  simp [homIntoDiagram, homFromDiagram, opEquiv]

private noncomputable def homIntoCocone_op_iso_precompose
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cone M) (W : C) :
    homIntoCocone c.op (Opposite.op W) ≅
      (Cocone.precompose (homIntoDiagram_op_iso M W).hom).obj
        (homFromCocone c W) := by
  refine Cocone.ext (opEquiv (Opposite.op W) (Opposite.op c.pt)).toIso ?_
  intro i
  ext f
  change c.π.app i.unop ≫ f.unop = c.π.app i.unop ≫ f.unop
  rfl

private theorem function_bijective_iff_postcomp_equiv
    {X Y Z : Type*} (e : Y ≃ Z) (f : X → Y) :
    Function.Bijective f ↔ Function.Bijective (e ∘ f) := by
  constructor
  · intro hf
    exact e.bijective.comp hf
  · intro hf
    constructor
    · intro x y hxy
      apply hf.1
      exact congrArg e hxy
    · intro z
      obtain ⟨x, hx⟩ := hf.2 (e z)
      exact ⟨x, e.injective hx⟩

private theorem function_bijective_iff_precomp_equiv
    {X Y Z : Type*} (e : X ≃ Y) (f : Y → Z) :
    Function.Bijective f ↔ Function.Bijective (f ∘ e) := by
  constructor
  · intro hf
    exact hf.comp e.bijective
  · intro hf
    constructor
    · intro x y hxy
      have h' : (f ∘ e) (e.symm x) = (f ∘ e) (e.symm y) := by
        simpa only [Function.comp_apply, e.apply_symm_apply] using hxy
      exact e.symm.injective (hf.1 h')
    · intro z
      obtain ⟨x, hx⟩ := hf.2 z
      exact ⟨e x, hx⟩

private theorem homFromCoconeMap_bijective_iff_op
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cone M) (W : C)
    [HasColimit (homIntoDiagram M.op (Opposite.op W))]
    [HasColimit (homFromDiagram M W)] :
    Function.Bijective (homFromCoconeMap c W) ↔
      Function.Bijective (homIntoCoconeMap c.op (Opposite.op W)) := by
  let α := homIntoDiagram_op_iso M W
  let β := (opEquiv (Opposite.op W) (Opposite.op c.pt)).toIso
  let s := homIntoCocone c.op (Opposite.op W)
  let t := (Cocone.precompose α.hom).obj (homFromCocone c W)
  let p : colimit (homIntoDiagram M.op (Opposite.op W)) ⟶
      (Opposite.op W ⟶ Opposite.op c.pt) :=
    TypeCat.ofHom (homIntoCoconeMap c.op (Opposite.op W))
  let q : colimit (homFromDiagram M W) ⟶ (c.pt ⟶ W) :=
    TypeCat.ofHom (homFromCoconeMap c W)
  have hleg (i : Iᵒᵖ) : s.ι.app i ≫ β.hom = t.ι.app i := by
    exact (homIntoCocone_op_iso_precompose c W).hom.w i
  have hpost :
      p ≫ β.hom = (HasColimit.isoOfNatIso α).hom ≫ q := by
    apply colimit.hom_ext
    intro i
    change
      (colimit.ι (homIntoDiagram M.op (Opposite.op W)) i ≫
          colimit.desc (homIntoDiagram M.op (Opposite.op W)) s) ≫ β.hom =
        (colimit.ι (homIntoDiagram M.op (Opposite.op W)) i ≫
          (HasColimit.isoOfNatIso α).hom) ≫ q
    rw [colimit.ι_desc, HasColimit.isoOfNatIso_ι_hom]
    dsimp [q, homFromCoconeMap, t]
    change
      (homIntoCocone c.op (Opposite.op W)).ι.app i ≫ β.hom =
        (α.hom.app i ≫ colimit.ι (homFromDiagram M W) i) ≫
          colimit.desc (homFromDiagram M W) (homFromCocone c W)
    simpa only [s, t, NatTrans.comp_app, Category.assoc, colimit.ι_desc,
      Cocone.precompose_obj_ι] using hleg i
  have hfun :
      (β.toEquiv ∘ homIntoCoconeMap c.op (Opposite.op W)) =
        (homFromCoconeMap c W) ∘ (HasColimit.isoOfNatIso α).toEquiv := by
    funext x
    have hx := congrArg (fun f => f x) hpost
    change β.hom (homIntoCoconeMap c.op (Opposite.op W) x) =
      homFromCoconeMap c W ((HasColimit.isoOfNatIso α).hom x) at hx
    change β.toEquiv (homIntoCoconeMap c.op (Opposite.op W) x) =
      homFromCoconeMap c W ((HasColimit.isoOfNatIso α).toEquiv x)
    exact hx
  constructor
  · intro h
    apply (function_bijective_iff_postcomp_equiv β.toEquiv _).mpr
    rw [hfun]
    exact (function_bijective_iff_precomp_equiv
      (HasColimit.isoOfNatIso α).toEquiv _).mp h
  · intro h
    apply (function_bijective_iff_precomp_equiv
      (HasColimit.isoOfNatIso α).toEquiv _).mpr
    rw [← hfun]
    exact (function_bijective_iff_postcomp_equiv β.toEquiv _).mp h

private theorem proDiagram_iff_indDiagram_op
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    IsEssentiallyConstantProDiagram M ↔
      IsEssentiallyConstantIndDiagram M.op := by
  constructor
  · rintro ⟨c, hc⟩
    rcases hc with ⟨i, r, hr, hfactor⟩
    refine ⟨c.op, ?_⟩
    refine ⟨Opposite.op i, r.op, ?_, ?_⟩
    · simpa using congrArg Quiver.Hom.op hr
    · intro j
      rcases hfactor j.unop with ⟨k, f, g, hfg⟩
      refine ⟨Opposite.op k, f.op, g.op, ?_⟩
      simpa using congrArg Quiver.Hom.op hfg
  · rintro ⟨d, hd⟩
    let c := d.unop
    refine ⟨c, ?_⟩
    rcases hd with ⟨i, s, hs, hfactor⟩
    refine ⟨i.unop, s.unop, ?_, ?_⟩
    · dsimp [c]
      simpa using congrArg Quiver.Hom.unop hs
    · intro j
      rcases hfactor (Opposite.op j) with ⟨k, f, g, hfg⟩
      refine ⟨k.unop, f.unop, g.unop, ?_⟩
      dsimp [c]
      simpa using congrArg Quiver.Hom.unop hfg

private theorem proHomLimitCondition_iff_indHomColimitCondition_op
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    ProHomLimitCondition M ↔ IndHomColimitCondition M.op := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c.op, ?_⟩
    intro W'
    let W := W'.unop
    obtain ⟨hW, hbij⟩ := hc W
    letI : HasColimit (homFromDiagram M W) := hW
    let α := homIntoDiagram_op_iso M W
    let hA : HasColimit (homIntoDiagram M.op (Opposite.op W)) :=
      hasColimit_of_iso α
    letI : HasColimit (homIntoDiagram M.op (Opposite.op W)) := hA
    refine ⟨hA, ?_⟩
    simpa [W] using (homFromCoconeMap_bijective_iff_op c W).mp hbij
  · rintro ⟨d, hd⟩
    let c := d.unop
    refine ⟨c, ?_⟩
    intro W
    obtain ⟨hW, hbij⟩ := hd (Opposite.op W)
    letI : HasColimit (homIntoDiagram M.op (Opposite.op W)) := hW
    let α := homIntoDiagram_op_iso M W
    let hB : HasColimit (homFromDiagram M W) :=
      hasColimit_of_iso α.symm
    letI : HasColimit (homFromDiagram M W) := hB
    refine ⟨hB, ?_⟩
    simpa [c] using (homFromCoconeMap_bijective_iff_op c W).mpr hbij

private theorem proMapCondition_iff_indMapCondition_op
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (c : Cone M) :
    (∀ W : C, ∃ hW : HasColimit (homFromDiagram M W),
      letI : HasColimit (homFromDiagram M W) := hW
      Function.Bijective (homFromCoconeMap c W)) ↔
    (∀ W' : Cᵒᵖ, ∃ hW : HasColimit (homIntoDiagram M.op W'),
      letI : HasColimit (homIntoDiagram M.op W') := hW
      Function.Bijective (homIntoCoconeMap c.op W')) := by
  constructor
  · intro hc W'
    let W := W'.unop
    obtain ⟨hW, hbij⟩ := hc W
    letI : HasColimit (homFromDiagram M W) := hW
    let α := homIntoDiagram_op_iso M W
    let hA : HasColimit (homIntoDiagram M.op (Opposite.op W)) :=
      hasColimit_of_iso α
    letI : HasColimit (homIntoDiagram M.op (Opposite.op W)) := hA
    refine ⟨hA, ?_⟩
    simpa [W] using (homFromCoconeMap_bijective_iff_op c W).mp hbij
  · intro hc W
    obtain ⟨hW, hbij⟩ := hc (Opposite.op W)
    letI : HasColimit (homIntoDiagram M.op (Opposite.op W)) := hW
    let α := homIntoDiagram_op_iso M W
    let hB : HasColimit (homFromDiagram M W) :=
      hasColimit_of_iso α.symm
    letI : HasColimit (homFromDiagram M W) := hB
    refine ⟨hB, ?_⟩
    simpa using (homFromCoconeMap_bijective_iff_op c W).mpr hbij

private theorem homFrom_colimit_postcompose_eq
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) {W W' : C}
    [HasColimit (homFromDiagram M W)]
    [HasColimit (homFromDiagram M W')]
    (f : W ⟶ W') {i j : I} (x : M.obj i ⟶ W) (y : M.obj j ⟶ W)
    (h : colimit.ι (homFromDiagram M W) (Opposite.op i) x =
      colimit.ι (homFromDiagram M W) (Opposite.op j) y) :
    colimit.ι (homFromDiagram M W') (Opposite.op i) (x ≫ f) =
      colimit.ι (homFromDiagram M W') (Opposite.op j) (y ≫ f) := by
  apply (Types.FilteredColimit.colimit_eq_iff (homFromDiagram M W')).2
  obtain ⟨k, p, q, hpq⟩ :=
    (Types.FilteredColimit.colimit_eq_iff (homFromDiagram M W)).1 h
  refine ⟨k, p, q, ?_⟩
  simpa [homFromDiagram, Category.assoc] using congrArg (fun z => z ≫ f) hpq

private theorem proSectionMap_bijective_iff_indSectionMap_op
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    {M : I ⥤ C} (X : C) (i : I) (r : M.obj i ⟶ X) (W : C)
    [HasColimit (homIntoDiagram M.op (Opposite.op W))]
    [HasColimit (homFromDiagram M W)] :
    Function.Bijective
        (fun f : X ⟶ W =>
          colimit.ι (homFromDiagram M W) (Opposite.op i) (r ≫ f)) ↔
      Function.Bijective
        (fun g : Opposite.op W ⟶ Opposite.op X =>
          colimit.ι (homIntoDiagram M.op (Opposite.op W)) (Opposite.op i)
            (g ≫ r.op)) := by
  let α := homIntoDiagram_op_iso M W
  let e := (HasColimit.isoOfNatIso α).toEquiv
  let input := (opEquiv (Opposite.op W) (Opposite.op X)).symm
  let p : (X ⟶ W) → colimit (homFromDiagram M W) := fun f =>
    colimit.ι (homFromDiagram M W) (Opposite.op i) (r ≫ f)
  let g : (Opposite.op W ⟶ Opposite.op X) →
      colimit (homIntoDiagram M.op (Opposite.op W)) := fun f =>
    colimit.ι (homIntoDiagram M.op (Opposite.op W)) (Opposite.op i) (f ≫ r.op)
  have hfun : p = (e ∘ g) ∘ input := by
    funext f
    have hι := HasColimit.isoOfNatIso_ι_hom α (Opposite.op i)
    have hx := congrArg
      (fun h => h ((input f) ≫ r.op)) hι
    change e (g (input f)) = p f at hx
    exact hx.symm
  constructor
  · intro hp
    have hmid : Function.Bijective (e ∘ g) := by
      apply (function_bijective_iff_precomp_equiv input _).mpr
      rw [← hfun]
      exact hp
    exact (function_bijective_iff_postcomp_equiv e _).mpr hmid
  · intro hg
    have hmid : Function.Bijective (e ∘ g) :=
      (function_bijective_iff_postcomp_equiv e _).mp hg
    have hcomp := (function_bijective_iff_precomp_equiv input _).mp hmid
    rw [← hfun] at hcomp
    exact hcomp

private theorem proHomSectionCondition_iff_indHomSectionCondition_op
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    ProHomSectionCondition M ↔ IndHomSectionCondition M.op := by
  constructor
  · rintro ⟨X, i, r, hsec⟩
    refine ⟨Opposite.op X, Opposite.op i, r.op, ?_⟩
    intro W'
    let W := W'.unop
    obtain ⟨hW, hbij⟩ := hsec W
    letI : HasColimit (homFromDiagram M W) := hW
    let α := homIntoDiagram_op_iso M W
    let hW' : HasColimit (homIntoDiagram M.op (Opposite.op W)) :=
      hasColimit_of_iso α
    letI : HasColimit (homIntoDiagram M.op (Opposite.op W)) := hW'
    refine ⟨hW', ?_⟩
    simpa [W] using
      (proSectionMap_bijective_iff_indSectionMap_op X i r W).mp hbij
  · rintro ⟨X, i, s, hsec⟩
    refine ⟨X.unop, i.unop, s.unop, ?_⟩
    intro W
    obtain ⟨hW, hbij⟩ := hsec (Opposite.op W)
    letI : HasColimit (homIntoDiagram M.op (Opposite.op W)) := hW
    let α := homIntoDiagram_op_iso M W
    let hW' : HasColimit (homFromDiagram M W) :=
      hasColimit_of_iso α.symm
    letI : HasColimit (homFromDiagram M W) := hW'
    refine ⟨hW', ?_⟩
    simpa using
      (proSectionMap_bijective_iff_indSectionMap_op
        X.unop i.unop s.unop W).mpr hbij

private theorem proHomLimitAndIsLimitCondition_iff_indHomColimitAndIsColimitCondition_op
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    ProHomLimitAndIsLimitCondition M ↔
      IndHomColimitAndIsColimitCondition M.op := by
  constructor
  · rintro ⟨c, ⟨hc⟩, hmap⟩
    refine ⟨c.op, ⟨hc.op⟩, ?_⟩
    exact (proMapCondition_iff_indMapCondition_op c).mp hmap
  · rintro ⟨d, ⟨hd⟩, hmap⟩
    let c := d.unop
    refine ⟨c, ⟨?_⟩, ?_⟩
    · dsimp [c]
      exact hd.unop
    · dsimp [c]
      exact (proMapCondition_iff_indMapCondition_op c).mpr hmap

theorem characterizeEssentiallyConstantPro
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
      (IsEssentiallyConstantProDiagram M ↔ ProHomLimitCondition M) ∧
      (ProHomLimitCondition M ↔ ProHomLimitAndIsLimitCondition M) ∧
      (ProHomLimitAndIsLimitCondition M ↔ ProHomSectionCondition M) := by
  have hInd := characterizeEssentiallyConstantInd (M := M.op)
  refine ⟨?_, ?_, ?_⟩
  · exact (proDiagram_iff_indDiagram_op M).trans
      (hInd.1.trans
        (proHomLimitCondition_iff_indHomColimitCondition_op M).symm)
  · exact (proHomLimitCondition_iff_indHomColimitCondition_op M).trans
      (hInd.2.1.trans
        (proHomLimitAndIsLimitCondition_iff_indHomColimitAndIsColimitCondition_op M).symm)
  · exact (proHomLimitAndIsLimitCondition_iff_indHomColimitAndIsColimitCondition_op M).trans
      (hInd.2.2.trans
        (proHomSectionCondition_iff_indHomSectionCondition_op M).symm)

/-! ## Cofinality, products, and initial functors -/

/-- A product of filtered categories is filtered. -/
theorem isFiltered_product
    {I J : Type u} [Category.{v} I] [Category.{v} J]
    [IsFiltered I] [IsFiltered J] :
    IsFiltered (I × J) := by
  infer_instance

/-- The second projection from a product of filtered categories is final. -/
theorem product_snd_is_final
    {I J : Type u} [Category.{v} I] [Category.{v} J]
    [IsFiltered I] [IsFiltered J] :
    Functor.Final (CategoryTheory.Prod.snd I J) := by
  infer_instance

theorem isEssentiallyConstantInd_comp_final_iff
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {J : Type u'} [Category.{v'} J] [IsFiltered J]
    {C : Type w} [Category.{w'} C]
    (H : I ⥤ J) [Functor.Final H] (M : J ⥤ C) :
    IsEssentiallyConstantIndDiagram M ↔
      IsEssentiallyConstantIndDiagram (H ⋙ M) := by
  sorry

theorem isEssentiallyConstantInd_comp_product_snd_iff
    {I : Type u} [Category.{v} I] [IsFiltered I]
    {J : Type u'} [Category.{v'} J] [IsFiltered J]
    {C : Type w} [Category.{w'} C]
    (M : J ⥤ C) :
    IsEssentiallyConstantIndDiagram M ↔
      IsEssentiallyConstantIndDiagram ((CategoryTheory.Prod.snd I J) ⋙ M) := by
  constructor
  · rintro ⟨c, i, s, hs, hfactor⟩
    let i₀ : I := Classical.choice (IsFiltered.nonempty (C := I))
    let c' : Cocone ((CategoryTheory.Prod.snd I J) ⋙ M) :=
      { pt := c.pt
        ι :=
          { app := fun x => c.ι.app x.2
            naturality := by
              intro x y f
              change M.map f.2 ≫ c.ι.app y.2 = c.ι.app x.2 ≫ 𝟙 c.pt
              have h := c.ι.naturality f.2
              change M.map f.2 ≫ c.ι.app y.2 = c.ι.app x.2 ≫ 𝟙 c.pt at h
              exact h } }
    refine ⟨c', ?_⟩
    refine ⟨(i₀, i), s, ?_, ?_⟩
    · simpa [c'] using hs
    · intro x
      rcases hfactor x.2 with ⟨k, f, g, hfg⟩
      let l := IsFiltered.max i₀ x.1
      let fi := IsFiltered.leftToMax i₀ x.1
      let fx := IsFiltered.rightToMax i₀ x.1
      refine ⟨(l, k), (fi, f), (fx, g), ?_⟩
      change M.map g = c.ι.app x.2 ≫ s ≫ M.map f
      exact hfg
  · rintro ⟨c, x, s, hs, hfactor⟩
    let a := x.1
    let c' : Cocone M :=
      { pt := c.pt
        ι :=
          { app := fun j => c.ι.app (a, j)
            naturality := by
              intro j k f
              let q : (a, j) ⟶ (a, k) := (𝟙 a, f)
              simpa [q] using c.ι.naturality q } }
    refine ⟨c', x.2, s, ?_, ?_⟩
    · simpa [c', a] using hs
    · intro j
      rcases hfactor (a, j) with ⟨k, f, g, hfg⟩
      refine ⟨k.2, f.2, g.2, ?_⟩
      change M.map g.2 = c.ι.app (a, j) ≫ s ≫ M.map f.2
      exact hfg

theorem isEssentiallyConstantPro_comp_initial_iff
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    {J : Type u'} [Category.{v'} J] [IsCofiltered J]
    {C : Type w} [Category.{w'} C]
    (H : I ⥤ J) [Functor.Initial H] (M : J ⥤ C) :
    IsEssentiallyConstantProDiagram M ↔
      IsEssentiallyConstantProDiagram (H ⋙ M) := by
  sorry

end
