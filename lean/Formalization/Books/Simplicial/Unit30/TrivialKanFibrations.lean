import Formalization.Books.Simplicial.Unit21.LeftAdjointsToSkeletonFunctors
import Formalization.Books.Simplicial.Unit26.Homotopies
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Simplicial Methods, Chapter 30: Trivial Kan fibrations

The boundary of the standard simplex is Mathlib's canonical `∂Δ[n]`, with
inclusion `(SSet.boundary n).ι`.  The declarations below give the source's
lifting property and its closure properties in the category of simplicial
sets.  Products, limits, filtered colimits, and homotopy equivalences use the
canonical categorical and homotopical interfaces established earlier.

The preliminary recalls about standard simplices are already represented by
the earlier interfaces `standard_simplex_obj_equiv`,
`standard_simplex_unique_nonDegenerate_top`, `simplex_map_equiv`, and
`simplex_map_equiv_apply`, together with Mathlib's
`SSet.stdSimplex.mem_nonDegenerate_iff_mono` and
`SSet.stdSimplex.nonDegenerateEquiv'`.  Thus the source's descriptions of
nondegenerate simplices as injective maps (or subsets) and of maps out of a
standard simplex require no parallel declarations here.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit30

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe u v w

/-! ## The boundary and the lifting property -/

/-
The source's boundary construction
`∂Δ[n] = i_(n - 1)! sk_(n - 1) Δ[n]` is represented by Mathlib's canonical
`SSet.boundary` and its inclusion `(SSet.boundary n).ι`; the earlier
left-adjoint identification is not needed to state any result in this
chapter.  The source's assertion that all lower-dimensional simplices lie in
the boundary and that the top simplex does not is already the pair of
Mathlib facts `SSet.boundary_obj_eq_univ` and
`SSet.stdSimplex.notMem_boundary`.
-/

/-- A simplicial map is injective in every degree. -/
abbrev TermwiseInjective {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∀ n : ℕ, Function.Injective (f.app (op (SimplexCategory.mk n)))

/-- The source's definition of a trivial Kan fibration. -/
def TrivialKanFibration {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  Function.Surjective (f.app (op (SimplexCategory.mk 0))) ∧
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (a : (∂Δ[n] : SSet.{u}) ⟶ X)
        (b : (Δ[n] : SSet.{u}) ⟶ Y),
        a ≫ f = (SSet.boundary n).ι ≫ b →
          ∃ l : (Δ[n] : SSet.{u}) ⟶ X,
            (SSet.boundary n).ι ≫ l = a ∧ l ≫ f = b

/-! ## General lifting and base change -/

/-- A trivial Kan fibration has the lifting property against every
degreewise-injective simplicial map. -/
theorem trivialKanFibration_lift
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : TrivialKanFibration f)
    {Z W : SSet.{u}} (i : Z ⟶ W) (hi : TermwiseInjective i)
    (a : Z ⟶ X) (b : W ⟶ Y) (comm : a ≫ f = i ≫ b) :
    ∃ l : W ⟶ X, i ≫ l = a ∧ l ≫ f = b := by
  have hi' : Mono i := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    simpa only [SimplexCategory.mk_len] using hi n.unop.len
  have hf' : (MorphismProperty.monomorphisms SSet.{u}).rlp f := by
    rw [SSet.rlp_monomorphisms]
    intro A B g hg
    simp only [SSet.modelCategoryQuillen.I] at hg ⊢
    obtain ⟨n⟩ := hg
    constructor
    intro c d sq
    by_cases hn : 1 ≤ n
    · obtain ⟨l, hl₁, hl₂⟩ := hf.2 n hn c d sq.w
      exact CommSq.HasLift.mk'
        { l := l
          fac_left := hl₁
          fac_right := hl₂ }
    · have hn0 : n = 0 := by omega
      subst n
      obtain ⟨x, hx⟩ := hf.1 (SSet.yonedaEquiv d)
      let l := SSet.yonedaEquiv.symm x
      have hl₂ : l ≫ f = d := by
        apply SSet.yonedaEquiv.injective
        rw [SSet.yonedaEquiv_comp]
        simpa only [l, SSet.yonedaEquiv_symm_zero, SSet.yonedaEquiv_const] using hx
      exact CommSq.HasLift.mk'
        { l := l
          fac_left := by
            let e : (∂Δ[0] : SSet.{u}) ≅ initial SSet.{u} :=
              (Formalization.Books.Simplicial.Unit21.boundary_zero_is_empty).some
            apply (cancel_epi e.inv).1
            exact Subsingleton.elim _ _
          fac_right := hl₂ }
  letI : Mono i := hi'
  let sq : CommSq a i f b := ⟨comm⟩
  letI : HasLiftingProperty i f := hf' i hi'
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- Base change preserves trivial Kan fibrations. -/
theorem trivialKanFibration_baseChange
    {X Y Y' : SSet.{u}} (f : X ⟶ Y) (hf : TrivialKanFibration f)
    (g : Y' ⟶ Y) :
    TrivialKanFibration (pullback.fst f g) := by
  sorry

/-- The composite of trivial Kan fibrations is a trivial Kan fibration. -/
theorem trivialKanFibration_comp
    {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : TrivialKanFibration f) (hg : TrivialKanFibration g) :
    TrivialKanFibration (f ≫ g) := by
  constructor
  · intro z
    obtain ⟨y, hy⟩ := hg.1 z
    obtain ⟨x, hx⟩ := hf.1 y
    exact ⟨x, by simpa [hx] using hy⟩
  · intro n hn a b comm
    obtain ⟨m, hm₁, hm₂⟩ := hg.2 n hn (a ≫ f) b (by
      simpa only [Category.assoc] using comm)
    obtain ⟨l, hl₁, hl₂⟩ := hf.2 n hn a m hm₁.symm
    refine ⟨l, hl₁, ?_⟩
    rw [← Category.assoc, hl₂, hm₂]

/-! ## Limits and products -/

/-
The source's sequence `… → U² → U¹ → U⁰` is represented by a functor
`U : ℕᵒᵖ ⥤ SSet`; its categorical limit is computed degreewise by the
presheaf category.
-/

/-- The successive transition map in an inverse sequence of simplicial sets. -/
def inverseSequenceTransition
    (U : ℕᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    U.obj (op (n + 1)) ⟶ U.obj (op n) :=
  U.map (homOfLE (Nat.le_succ n)).op

private lemma inverseSequence_boundary_lift
    (U : ℕᵒᵖ ⥤ SSet.{u})
    (hU : ∀ n : ℕ,
      TrivialKanFibration (inverseSequenceTransition U n))
    {n : ℕ} (hn : 1 ≤ n)
    (a : (∂Δ[n] : SSet.{u}) ⟶ limit U)
    (b : (Δ[n] : SSet.{u}) ⟶ U.obj (op 0))
    (comm : a ≫ limit.π U (op 0) = (SSet.boundary n).ι ≫ b) :
    ∃ l : (Δ[n] : SSet.{u}) ⟶ limit U,
      (SSet.boundary n).ι ≫ l = a ∧
        l ≫ limit.π U (op 0) = b := by
  let LiftType : ℕᵒᵖ → Type u := fun j =>
    {l : (Δ[n] : SSet.{u}) ⟶ U.obj j |
      (SSet.boundary n).ι ≫ l = a ≫ limit.π U j}
  let mapLift : ∀ {i j : ℕᵒᵖ}, (i ⟶ j) → LiftType i → LiftType j :=
    fun {i j} α z => by
      change {l : (Δ[n] : SSet.{u}) ⟶ U.obj j |
        (SSet.boundary n).ι ≫ l = a ≫ limit.π U j}
      change {l : (Δ[n] : SSet.{u}) ⟶ U.obj i |
        (SSet.boundary n).ι ≫ l = a ≫ limit.π U i} at z
      refine ⟨z.1 ≫ U.map α, ?_⟩
      change (SSet.boundary n).ι ≫ (z.1 ≫ U.map α) =
        a ≫ limit.π U j
      rw [← Category.assoc, z.2, Category.assoc, limit.w]
  let F : ℕᵒᵖ ⥤ Type u :=
    { obj := LiftType
      map := fun {i j} α => TypeCat.ofHom (mapLift α)
      map_id := by
        intro j
        apply ConcreteCategory.hom_ext
        intro z
        simp [mapLift]
      map_comp := by
        intro i j k α β
        apply ConcreteCategory.hom_ext
        intro z
        simp [mapLift, Category.assoc] }
  let x₀ : F.obj (op 0) := by
    change LiftType (op 0)
    exact ⟨b, comm.symm⟩
  let val : ∀ j, F.obj j → ((Δ[n] : SSet.{u}) ⟶ U.obj j) := fun j z => by
    change LiftType j at z
    exact z.1
  let d : F.WellOrderInductionData :=
    Functor.WellOrderInductionData.ofExists (F := F) (fun j _ z => by
      change LiftType (op j) at z
      obtain ⟨l, hl₁, hl₂⟩ := (hU j).2 n hn
        (a ≫ limit.π U (op (j + 1))) (val (op j) z) (by
          change (a ≫ limit.π U (op (j + 1))) ≫
              U.map (homOfLE (Nat.le_succ j)).op =
            (SSet.boundary n).ι ≫ z.1
          rw [Category.assoc, limit.w, z.2])
      change ∃ y : LiftType (op (Order.succ j)), F.map _ y = z
      refine ⟨⟨l, hl₁⟩, ?_⟩
      change mapLift (homOfLE (Nat.le_succ j)).op ⟨l, hl₁⟩ = z
      apply Subtype.ext
      change l ≫ U.map (homOfLE (Nat.le_succ j)).op = z.1
      exact hl₂)
      (fun j hj x => (Order.not_isSuccLimit_natCast j hj).elim)
  let s : F.sections := d.sectionsMk x₀
  let c : Cone U :=
    { pt := (Δ[n] : SSet.{u})
      π :=
        { app := fun j => val j (s.val j)
          naturality := by
            intro i j α
            have hs := congrArg (fun z => val j z) (s.property α)
            simpa [F, mapLift, val, LiftType, Category.assoc] using hs.symm } }
  let l : (Δ[n] : SSet.{u}) ⟶ limit U := limit.lift U c
  have hl₀ : (SSet.boundary n).ι ≫ l = a := by
    apply (limit.isLimit U).hom_ext
    intro j
    have hsj : (SSet.boundary n).ι ≫ val j (s.val j) =
        a ≫ limit.π U j := by
      unfold val
      change (SSet.boundary n).ι ≫ (s.val j : LiftType j).1 =
        a ≫ limit.π U j
      exact (show LiftType j from s.val j).2
    simpa [l, c, Category.assoc] using hsj
  have hl₁ : l ≫ limit.π U (op 0) = b := by
    have h := congrArg (fun z => val (op 0) z)
      (d.sectionsMk_val_op_bot x₀)
    simpa [l, c, s, x₀, val, LiftType] using h
  exact ⟨l, hl₀, hl₁⟩

/-- The limit of a sequence of trivial Kan fibrations maps by a trivial Kan
fibration to its zeroth term. -/
theorem trivialKanFibration_limit
    (U : ℕᵒᵖ ⥤ SSet.{u})
    (hU : ∀ n : ℕ,
      TrivialKanFibration (inverseSequenceTransition U n)) :
    TrivialKanFibration (limit.π U (op 0)) := by
  constructor
  · intro y
    let V : ℕᵒᵖ ⥤ Type u :=
      { obj := fun j => (U.obj j).obj (op (SimplexCategory.mk 0))
        map := fun {i j} α =>
          TypeCat.ofHom ((U.map α).app (op (SimplexCategory.mk 0)))
        map_id := by
          intro j
          apply ConcreteCategory.hom_ext
          intro x
          simp
        map_comp := by
          intro i j k α β
          apply ConcreteCategory.hom_ext
          intro x
          simp }
    let d : V.WellOrderInductionData :=
      Functor.WellOrderInductionData.ofExists (F := V) (fun j _ x => by
        obtain ⟨z, hz⟩ := (hU j).1 x
        refine ⟨z, ?_⟩
        change ((U.map (homOfLE (Nat.le_succ j)).op).app
          (op (SimplexCategory.mk 0))) z = x
        simpa [inverseSequenceTransition] using hz)
        (fun j hj x => (Order.not_isSuccLimit_natCast j hj).elim)
    let s : V.sections := d.sectionsMk y
    let c : Cone U :=
      { pt := (Δ[0] : SSet.{u})
        π :=
          { app := fun j => SSet.yonedaEquiv.symm (s.val j)
            naturality := by
              intro i j α
              change SSet.yonedaEquiv.symm (s.val j) =
                SSet.yonedaEquiv.symm (s.val i) ≫ U.map α
              rw [SSet.yonedaEquiv_symm_comp]
              simpa [V] using
                (congrArg (fun z => SSet.yonedaEquiv.symm z) (s.property α)).symm } }
    let l : (Δ[0] : SSet.{u}) ⟶ limit U := limit.lift U c
    refine ⟨SSet.yonedaEquiv l, ?_⟩
    have hl : l ≫ limit.π U (op 0) = SSet.yonedaEquiv.symm y := by
      simpa [l, c] using
        congrArg (fun z => SSet.yonedaEquiv.symm z)
          (d.sectionsMk_val_op_bot y)
    rw [← SSet.yonedaEquiv_comp, hl]
    rw [SSet.yonedaEquiv_symm_zero]
    exact SSet.yonedaEquiv_const y
  · intro n hn a b comm
    exact inverseSequence_boundary_lift U hU hn a b comm

/-- The product map induced by a family of trivial Kan fibrations is a
trivial Kan fibration. -/
theorem trivialKanFibration_product
    {T : Type w} {X Y : T → SSet.{u}}
    (hX : HasLimit (Discrete.functor X))
    (hY : HasLimit (Discrete.functor Y))
    (f : ∀ t, X t ⟶ Y t)
    (hf : ∀ t, TrivialKanFibration (f t)) :
    TrivialKanFibration
      (Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f) := by
  sorry

/-! ## Filtered colimits -/

/-- The canonical map on colimits induced by a natural transformation, with
the colimit choices made explicit for use in the filtered-colimit theorem. -/
noncomputable def filteredColimitMap
    {J : Type v} [Category.{v} J]
    {X Y : J ⥤ SSet.{u}} (f : X ⟶ Y)
    (hX : HasColimit X) (hY : HasColimit Y) :
    colimit X ⟶ colimit Y := by
  letI := hX
  letI := hY
  let c : Cocone X :=
    { pt := colimit Y
      ι :=
        { app := fun j => f.app j ≫ colimit.ι Y j
          naturality := by
            intro i j α
            change X.map α ≫ (f.app j ≫ colimit.ι Y j) =
              f.app i ≫ colimit.ι Y i
            rw [← Category.assoc, f.naturality α, Category.assoc, colimit.w] } }
  exact colimit.desc X c

/-- Filtered colimits preserve trivial Kan fibrations. -/
theorem trivialKanFibration_filteredColimit
    {J : Type v} [Category.{v} J] [IsFiltered J]
    {X Y : J ⥤ SSet.{u}} (f : X ⟶ Y)
    (hX : HasColimit X) (hY : HasColimit Y)
    (hf : ∀ j, TrivialKanFibration (f.app j)) :
    TrivialKanFibration (filteredColimitMap f hX hY) := by
  sorry

/-! ## Homotopy equivalence -/

/-- A trivial Kan fibration admits a simplicial section. -/
theorem trivialKanFibration_has_section
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : TrivialKanFibration f) :
    ∃ g : Y ⟶ X, g ≫ f = 𝟙 Y := by
  sorry

/-- Every trivial Kan fibration is a homotopy equivalence of simplicial sets. -/
theorem trivialKanFibration_isHomotopyEquivalence
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : TrivialKanFibration f) :
    Formalization.Books.Simplicial.Unit26.IsHomotopyEquivalence f := by
  sorry

/-! The displayed cylinder in the final proof is represented by Mathlib's
`SSet.Homotopy`, whose interval object is `Δ[1]`; the degreewise identity
`(∂Δ[1] × X)_n ≅ X_n ⊔ X_n` is consequently subsumed by that established
endpoint API.
-/

end Formalization.Books.Simplicial.Unit30
