import Formalization.Books.Simplicial.Unit26.Homotopies
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import Mathlib.CategoryTheory.Limits.FunctorToTypes
import Mathlib.CategoryTheory.Presentable.Type

attribute [-instance] CategoryTheory.evaluationIsLeftAdjoint


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
open CategoryTheory.MonoidalCategory
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
              by
                rw [SSet.boundary_zero]
                exact (SSet.Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))).uniqueUpToIso
                  (initialIsInitial)
            apply (cancel_epi e.inv).1
            exact Subsingleton.elim _ _
          fac_right := hl₂ }
  let sq : CommSq a i f b := ⟨comm⟩
  have hsq : HasLiftingProperty i f := hf' i hi'
  obtain ⟨l, hl_left, hl_right⟩ := (hsq.sq_hasLift sq).exists_lift.some
  exact ⟨l, hl_left, hl_right⟩

/-- Base change preserves trivial Kan fibrations. -/
theorem trivialKanFibration_baseChange
    {X Y Y' : SSet.{u}} (f : X ⟶ Y) (hf : TrivialKanFibration f)
    (g : Y' ⟶ Y) :
    TrivialKanFibration (pullback.snd f g) := by
  constructor
  · intro y'
    let b : (Δ[0] : SSet.{u}) ⟶ Y' := SSet.yonedaEquiv.symm y'
    obtain ⟨x, hx⟩ := hf.1 (SSet.yonedaEquiv (b ≫ g))
    let a : (Δ[0] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm x
    have hab : a ≫ f = b ≫ g := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp]
      simpa [a, SSet.yonedaEquiv_symm_zero, SSet.yonedaEquiv_const] using hx
    let l : (Δ[0] : SSet.{u}) ⟶ pullback f g :=
      pullback.lift a b hab
    refine ⟨SSet.yonedaEquiv l, ?_⟩
    rw [← SSet.yonedaEquiv_comp, pullback.lift_snd]
    simpa [b, SSet.yonedaEquiv_symm_zero] using SSet.yonedaEquiv_const y'
  · intro n hn a b comm
    obtain ⟨l, hl₁, hl₂⟩ := hf.2 n hn (a ≫ pullback.fst f g) (b ≫ g) (by
      calc
        (a ≫ pullback.fst f g) ≫ f =
            a ≫ (pullback.fst f g ≫ f) := Category.assoc _ _ _
        _ = a ≫ (pullback.snd f g ≫ g) :=
          congrArg (fun z => a ≫ z) (pullback.condition)
        _ = (a ≫ pullback.snd f g) ≫ g := (Category.assoc _ _ _).symm
        _ = (SSet.boundary n).ι ≫ b ≫ g :=
          congrArg (fun z => z ≫ g) comm)
    let l' : (Δ[n] : SSet.{u}) ⟶ pullback f g :=
      pullback.lift l b hl₂
    refine ⟨l', ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst]
        exact hl₁
      · rw [Category.assoc, pullback.lift_snd]
        exact comm.symm
    · change pullback.lift l b hl₂ ≫ pullback.snd f g = b
      rw [pullback.lift_snd]

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
  constructor
  · intro y
    let b : (Δ[0] : SSet.{u}) ⟶
        Formalization.Books.Simplicial.Unit26.indexedProduct Y hY :=
      SSet.yonedaEquiv.symm y
    let x : ∀ t : T, (X t) _⦋0⦌ := fun t =>
      Classical.choose ((hf t).1 (SSet.yonedaEquiv
        (b ≫ limit.π (Discrete.functor Y) ⟨t⟩)))
    let c : Cone (Discrete.functor X) :=
      { pt := (Δ[0] : SSet.{u})
        π :=
          { app := fun t => SSet.yonedaEquiv.symm (x t.as)
            naturality := by
              rintro ⟨i⟩ ⟨j⟩ g
              obtain rfl := Discrete.eq_of_hom g
              simp } }
    let l : (Δ[0] : SSet.{u}) ⟶
        Formalization.Books.Simplicial.Unit26.indexedProduct X hX :=
      limit.lift (Discrete.functor X) c
    have hmap : l ≫
        Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f = b := by
      apply (limit.isLimit (Discrete.functor Y)).hom_ext
      intro t
      have hx0 := Classical.choose_spec ((hf t.as).1
        (SSet.yonedaEquiv
          (b ≫ limit.π (Discrete.functor Y) ⟨t.as⟩)))
      have hxf : SSet.yonedaEquiv.symm
          ((f t.as).app (op (SimplexCategory.mk 0)) (x t.as)) =
          b ≫ limit.π (Discrete.functor Y) ⟨t.as⟩ := by
        simpa using congrArg SSet.yonedaEquiv.symm hx0
      have hproj :
          Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f ≫
              limit.π (Discrete.functor Y) t =
            limit.π (Discrete.functor X) t ≫ f t.as := by
        simpa using
          (Formalization.Books.Simplicial.Unit26.indexedProductMap_comp_projection
            hX hY f t.as)
      calc
        (l ≫ Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f) ≫
              limit.π (Discrete.functor Y) t =
            l ≫
              (Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f ≫
                limit.π (Discrete.functor Y) t) := Category.assoc _ _ _
        _ = l ≫ (limit.π (Discrete.functor X) t ≫ f t.as) :=
          congrArg (fun z => l ≫ z) hproj
        _ = (l ≫ limit.π (Discrete.functor X) t) ≫ f t.as :=
          (Category.assoc _ _ _).symm
        _ = (SSet.yonedaEquiv.symm (x t.as)) ≫ f t.as := by
          change (limit.lift (Discrete.functor X) c ≫
              limit.π (Discrete.functor X) t) ≫ f t.as =
            (SSet.yonedaEquiv.symm (x t.as)) ≫ f t.as
          rw [limit.lift_π]
        _ = b ≫ limit.π (Discrete.functor Y) t := by
          simpa [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_zero] using hxf
    refine ⟨SSet.yonedaEquiv l, ?_⟩
    rw [← SSet.yonedaEquiv_comp, hmap]
    simpa [b, SSet.yonedaEquiv_symm_zero] using SSet.yonedaEquiv_const y
  · intro n hn a b comm
    let sq : ∀ t : T, ∃ l : (Δ[n] : SSet.{u}) ⟶ X t,
        (SSet.boundary n).ι ≫ l = a ≫ limit.π (Discrete.functor X) ⟨t⟩ ∧
        l ≫ f t = b ≫ limit.π (Discrete.functor Y) ⟨t⟩ := fun t => by
      have hproj :
          Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f ≫
              limit.π (Discrete.functor Y) ⟨t⟩ =
            limit.π (Discrete.functor X) ⟨t⟩ ≫ f t := by
        exact
          Formalization.Books.Simplicial.Unit26.indexedProductMap_comp_projection
            hX hY f t
      obtain ⟨l, hl₁, hl₂⟩ := (hf t).2 n hn
        (a ≫ limit.π (Discrete.functor X) ⟨t⟩)
        (b ≫ limit.π (Discrete.functor Y) ⟨t⟩) (by
          calc
            (a ≫ limit.π (Discrete.functor X) ⟨t⟩) ≫ f t =
                a ≫ (limit.π (Discrete.functor X) ⟨t⟩ ≫ f t) :=
              Category.assoc _ _ _
            _ = a ≫
                (Formalization.Books.Simplicial.Unit26.indexedProductMap
                  hX hY f ≫ limit.π (Discrete.functor Y) ⟨t⟩) :=
              congrArg (fun z => a ≫ z) hproj.symm
            _ = (a ≫
                Formalization.Books.Simplicial.Unit26.indexedProductMap
                  hX hY f) ≫ limit.π (Discrete.functor Y) ⟨t⟩ :=
              (Category.assoc _ _ _).symm
            _ = ((SSet.boundary n).ι ≫ b) ≫
                limit.π (Discrete.functor Y) ⟨t⟩ :=
              congrArg (fun z => z ≫ limit.π (Discrete.functor Y) ⟨t⟩)
                comm
            _ = (SSet.boundary n).ι ≫
                (b ≫ limit.π (Discrete.functor Y) ⟨t⟩) :=
              Category.assoc _ _ _)
      exact ⟨l, hl₁, hl₂⟩
    let c : Cone (Discrete.functor X) :=
      { pt := (Δ[n] : SSet.{u})
        π :=
          { app := fun t => (sq t.as).choose
            naturality := by
              rintro ⟨i⟩ ⟨j⟩ g
              obtain rfl := Discrete.eq_of_hom g
              simp } }
    let l : (Δ[n] : SSet.{u}) ⟶
        Formalization.Books.Simplicial.Unit26.indexedProduct X hX :=
      limit.lift (Discrete.functor X) c
    refine ⟨l, ?_, ?_⟩
    · apply (limit.isLimit (Discrete.functor X)).hom_ext
      intro t
      change (SSet.boundary n).ι ≫
          limit.lift (Discrete.functor X) c ≫
            limit.π (Discrete.functor X) t = a ≫ limit.π (Discrete.functor X) t
      simpa only [Category.assoc, limit.lift_π] using
        (sq t.as).choose_spec.1
    · apply (limit.isLimit (Discrete.functor Y)).hom_ext
      intro t
      have hproj :
          Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f ≫
              limit.π (Discrete.functor Y) t =
            limit.π (Discrete.functor X) t ≫ f t.as := by
        simpa using
          (Formalization.Books.Simplicial.Unit26.indexedProductMap_comp_projection
            hX hY f t.as)
      calc
        (l ≫ Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f) ≫
              limit.π (Discrete.functor Y) t =
            l ≫
              (Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f ≫
                limit.π (Discrete.functor Y) t) := Category.assoc _ _ _
        _ = l ≫ (limit.π (Discrete.functor X) t ≫ f t.as) :=
          congrArg (fun z => l ≫ z) hproj
        _ = (l ≫ limit.π (Discrete.functor X) t) ≫ f t.as :=
          (Category.assoc _ _ _).symm
        _ = (sq t.as).choose ≫ f t.as := by
          change (limit.lift (Discrete.functor X) c ≫
              limit.π (Discrete.functor X) t) ≫ f t.as = _
          rw [limit.lift_π]
        _ = b ≫ limit.π (Discrete.functor Y) t :=
          (sq t.as).choose_spec.2

/-! ## Filtered colimits -/

/-- The canonical map on colimits induced by a natural transformation, with
the colimit choices made explicit for use in the filtered-colimit theorem. -/
noncomputable def filteredColimitMap
    {J : Type v} [Category.{v} J]
    {X Y : J ⥤ SSet.{u}} (f : X ⟶ Y)
    (hX : HasColimit X) (hY : HasColimit Y) :
    colimit X ⟶ colimit Y := by
  haveI := hX
  haveI := hY
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

private lemma finite_sset_isCardinalPresentable
    {Z : SSet.{u}} [Z.Finite]
    [Fact (Cardinal.aleph0 : Cardinal.{v}).IsRegular] :
    IsCardinalPresentable.{v} Z (Cardinal.aleph0 : Cardinal.{v}) := by
  have hstd (n : ℕ) :
      IsCardinalPresentable.{v} (Δ[n] : SSet.{u})
        (Cardinal.aleph0 : Cardinal.{v}) := by
    apply (isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj
      (Δ[n] : SSet.{u}) (Cardinal.aleph0 : Cardinal.{v})).2
    let e : uliftCoyoneda.{v}.obj (op (Δ[n] : SSet.{u})) ≅
        (SSet.evaluation.{u}).obj (op (SimplexCategory.mk n)) ⋙
          uliftFunctor.{v} :=
      NatIso.ofComponents (fun X => Equiv.toIso (Equiv.ofBijective
        (fun x => ⟨SSet.yonedaEquiv x.down⟩) (by
          constructor
          · intro x y h
            apply ULift.ext
            apply SSet.yonedaEquiv.injective
            exact congrArg ULift.down h
          · intro y
            refine ⟨⟨SSet.yonedaEquiv.symm y.down⟩, ?_⟩
            apply ULift.ext
            simp))) (by
        intro X Y g
        ext f
        apply ULift.ext
        change SSet.yonedaEquiv (f.down ≫ g) =
          (g.app (op (SimplexCategory.mk n))).hom
            (SSet.yonedaEquiv f.down)
        rw [SSet.yonedaEquiv_comp]
      )
    let : ((SSet.evaluation.{u}).obj (op (SimplexCategory.mk n))).IsLeftAdjoint :=
      ⟨_, ⟨evaluationAdjunctionLeft (Type u) (op (SimplexCategory.mk n))⟩⟩
    let : Functor.IsCardinalAccessible
        ((SSet.evaluation.{u}).obj (op (SimplexCategory.mk n)) ⋙
          uliftFunctor.{v})
        (Cardinal.aleph0 : Cardinal.{v}) :=
      ⟨fun J _ _ => inferInstance⟩
    exact Functor.isCardinalAccessible_of_natIso e.symm
      (Cardinal.aleph0 : Cardinal.{v})
  let P : SSet.{u} := ∐ (fun (s : Z.N) => Δ[s.dim])
  let : ∀ k : Discrete Z.N,
      IsCardinalPresentable.{v} ((Discrete.functor fun s => Δ[s.dim]).obj k)
        (Cardinal.aleph0 : Cardinal.{v}) := by
    rintro ⟨s⟩
    exact hstd s.dim
  have hP : IsCardinalPresentable.{v} P (Cardinal.aleph0 : Cardinal.{v}) := by
    apply isCardinalPresentable_of_isColimit' _ (coproductIsCoproduct _)
    · exact hasCardinalLT_of_finite _ _ (by rfl)
  let p : P ⟶ Z :=
    Sigma.desc (fun s ↦ SSet.yonedaEquiv.symm s.simplex)
  have hp : Epi p := by
    dsimp [p, P]
    simp only [← SSet.Subcomplex.range_eq_top_iff, SSet.range_eq_iSup_sigma_ι,
      colimit.ι_desc,
      Cofan.mk_ι_app, ← SSet.N.iSup_subcomplex_eq_top,
      SSet.Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]
  let Q : SSet.{u} := ∐ (fun (s : (pullback p p).N) => Δ[s.dim])
  let : ∀ k : Discrete (pullback p p).N,
      IsCardinalPresentable.{v} ((Discrete.functor fun s => Δ[s.dim]).obj k)
        (Cardinal.aleph0 : Cardinal.{v}) := by
    rintro ⟨s⟩
    exact hstd s.dim
  have hQ : IsCardinalPresentable.{v} Q (Cardinal.aleph0 : Cardinal.{v}) := by
    apply isCardinalPresentable_of_isColimit' _ (coproductIsCoproduct _)
    · exact hasCardinalLT_of_finite _ _ (by rfl)
  let q : Q ⟶ pullback p p :=
    Sigma.desc (fun s ↦ SSet.yonedaEquiv.symm s.simplex)
  have hq : Epi q := by
    dsimp [q, Q]
    simp only [← SSet.Subcomplex.range_eq_top_iff, SSet.range_eq_iSup_sigma_ι,
      colimit.ι_desc,
      Cofan.mk_ι_app, ← SSet.N.iSup_subcomplex_eq_top,
      SSet.Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]
  let : IsRegularEpi p := IsRegularEpiCategory.regularEpiOfEpi p
  let : IsRegularEpi q := IsRegularEpiCategory.regularEpiOfEpi q
  let : IsCardinalPresentable.{v} P (Cardinal.aleph0 : Cardinal.{v}) := hP
  let : IsCardinalPresentable.{v} Q (Cardinal.aleph0 : Cardinal.{v}) := hQ
  let : ∀ k : WalkingParallelPair,
      IsCardinalPresentable.{v}
        ((parallelPair (q ≫ pullback.fst p p) (q ≫ pullback.snd p p)).obj k)
        (Cardinal.aleph0 : Cardinal.{v}) := by
    rintro (_ | _)
    · exact hQ
    · exact hP
  apply isCardinalPresentable_of_isColimit' _
    (isCoequalizerEpiComp
      ((EffectiveEpi.getStruct p).isColimitCoforkOfIsPullback
        (IsPullback.of_hasPullback p p)) q)
  · exact hasCardinalLT_of_finite _ _ (by rfl)

/-- Filtered colimits preserve trivial Kan fibrations. -/
theorem trivialKanFibration_filteredColimit
    {J : Type v} [Category.{v} J] [IsFiltered J]
    {X Y : J ⥤ SSet.{u}} (f : X ⟶ Y)
    (hX : HasColimit X) (hY : HasColimit Y)
    (hf : ∀ j, TrivialKanFibration (f.app j)) :
    TrivialKanFibration (filteredColimitMap f hX hY) := by
  let _ := hX
  let _ := hY
  let _ : Fact (Cardinal.aleph0 : Cardinal.{v}).IsRegular :=
    Cardinal.fact_isRegular_aleph0
  let _ : IsFinitelyPresentable.{v} (Δ[0] : SSet.{u}) :=
    finite_sset_isCardinalPresentable
  have hι (j : J) :
      colimit.ι X j ≫ filteredColimitMap f hX hY =
        f.app j ≫ colimit.ι Y j := by
    change colimit.ι X j ≫ colimit.desc X _ = _
    rw [colimit.ι_desc]
  constructor
  · intro y
    obtain ⟨j, yj, hy⟩ :=
      IsFinitelyPresentable.exists_hom_of_isColimit (colimit.isColimit Y)
        (SSet.yonedaEquiv.symm y)
    let yj₀ := SSet.yonedaEquiv yj
    obtain ⟨xj, hxj⟩ := (hf j).1 yj₀
    have hy₀ : (colimit.ι Y j).app (op (SimplexCategory.mk 0)) yj₀ = y := by
      have h := congrArg SSet.yonedaEquiv hy
      rw [← SSet.yonedaEquiv_const y]
      simpa [yj₀, SSet.yonedaEquiv_comp, SSet.yonedaEquiv_symm_zero] using h
    refine ⟨(colimit.ι X j).app _ xj, ?_⟩
    have hj : (colimit.ι X j).app (op (SimplexCategory.mk 0)) ≫
        (filteredColimitMap f hX hY).app (op (SimplexCategory.mk 0)) =
        (f.app j).app (op (SimplexCategory.mk 0)) ≫
          (colimit.ι Y j).app (op (SimplexCategory.mk 0)) := by
      exact congr_app (hι j) (op (SimplexCategory.mk 0))
    calc
      (filteredColimitMap f hX hY).app (op (SimplexCategory.mk 0))
          ((colimit.ι X j).app (op (SimplexCategory.mk 0)) xj) =
          (colimit.ι Y j).app (op (SimplexCategory.mk 0))
            ((f.app j).app (op (SimplexCategory.mk 0)) xj) :=
        ConcreteCategory.congr_hom hj xj
      _ = (colimit.ι Y j).app (op (SimplexCategory.mk 0)) yj₀ :=
        congrArg (fun z => (colimit.ι Y j).app (op (SimplexCategory.mk 0)) z) hxj
      _ = y := hy₀
  · intro n hn a b comm
    let _ : IsFinitelyPresentable.{v} (SSet.boundary n : SSet.{u}) :=
      finite_sset_isCardinalPresentable
    let _ : IsFinitelyPresentable.{v} (Δ[n] : SSet.{u}) :=
      finite_sset_isCardinalPresentable
    obtain ⟨jA, aA, ha⟩ :=
      IsFinitelyPresentable.exists_hom_of_isColimit (colimit.isColimit X) a
    obtain ⟨jB, bB, hb⟩ :=
      IsFinitelyPresentable.exists_hom_of_isColimit (colimit.isColimit Y) b
    obtain ⟨j₀, p, q, _⟩ := IsFilteredOrEmpty.cocone_objs jA jB
    let a₀ : (SSet.boundary n : SSet.{u}) ⟶ X.obj j₀ :=
      aA ≫ X.map p
    let b₀ : (Δ[n] : SSet.{u}) ⟶ Y.obj j₀ :=
      bB ≫ Y.map q
    have ha₀ : a₀ ≫ colimit.ι X j₀ = a := by
      dsimp [a₀]
      rw [Category.assoc, colimit.w X p]
      exact ha
    have hb₀ : b₀ ≫ colimit.ι Y j₀ = b := by
      dsimp [b₀]
      rw [Category.assoc, colimit.w Y q]
      exact hb
    have hsq₀ :
        (a₀ ≫ f.app j₀) ≫ colimit.ι Y j₀ =
          (SSet.boundary n).ι ≫ b₀ ≫ colimit.ι Y j₀ := by
      calc
        (a₀ ≫ f.app j₀) ≫ colimit.ι Y j₀ =
            a₀ ≫ (f.app j₀ ≫ colimit.ι Y j₀) := Category.assoc _ _ _
        _ = a₀ ≫ (colimit.ι X j₀ ≫ filteredColimitMap f hX hY) :=
          congrArg (fun z => a₀ ≫ z) (hι j₀).symm
        _ = (a₀ ≫ colimit.ι X j₀) ≫ filteredColimitMap f hX hY :=
          (Category.assoc _ _ _).symm
        _ = a ≫ filteredColimitMap f hX hY :=
          congrArg (fun z => z ≫ filteredColimitMap f hX hY) ha₀
        _ = (SSet.boundary n).ι ≫ b :=
          comm
        _ = (SSet.boundary n).ι ≫ (b₀ ≫ colimit.ι Y j₀) :=
          congrArg (fun z => (SSet.boundary n).ι ≫ z) hb₀.symm
        _ = (SSet.boundary n).ι ≫ b₀ ≫ colimit.ι Y j₀ :=
          rfl
    obtain ⟨k, r, s, hrs⟩ :=
      IsFinitelyPresentable.exists_eq_of_isColimit (colimit.isColimit Y)
        (a₀ ≫ f.app j₀) ((SSet.boundary n).ι ≫ b₀) hsq₀
    let a₁ : (SSet.boundary n : SSet.{u}) ⟶ X.obj k :=
      a₀ ≫ X.map r
    let b₁ : (Δ[n] : SSet.{u}) ⟶ Y.obj k :=
      b₀ ≫ Y.map s
    have hsq :
        a₁ ≫ f.app k = (SSet.boundary n).ι ≫ b₁ := by
      calc
        a₁ ≫ f.app k = a₀ ≫ (X.map r ≫ f.app k) := Category.assoc _ _ _
        _ = a₀ ≫ (f.app j₀ ≫ Y.map r) :=
          congrArg (fun z => a₀ ≫ z) (f.naturality r)
        _ = (a₀ ≫ f.app j₀) ≫ Y.map r := (Category.assoc _ _ _).symm
        _ = ((SSet.boundary n).ι ≫ b₀) ≫ Y.map s := hrs
        _ = (SSet.boundary n).ι ≫ b₁ := Category.assoc _ _ _
    obtain ⟨l, hl₁, hl₂⟩ := (hf k).2 n hn a₁ b₁ hsq
    refine ⟨l ≫ colimit.ι X k, ?_, ?_⟩
    · calc
        (SSet.boundary n).ι ≫ (l ≫ colimit.ι X k) =
            ((SSet.boundary n).ι ≫ l) ≫ colimit.ι X k :=
          (Category.assoc _ _ _).symm
        _ = a₁ ≫ colimit.ι X k := congrArg (fun z => z ≫ colimit.ι X k) hl₁
        _ = (a₀ ≫ X.map r) ≫ colimit.ι X k := rfl
        _ = a₀ ≫ (X.map r ≫ colimit.ι X k) := Category.assoc _ _ _
        _ = a₀ ≫ colimit.ι X j₀ :=
          congrArg (fun z => a₀ ≫ z) (colimit.w X r)
        _ = a := ha₀
    · calc
        (l ≫ colimit.ι X k) ≫ filteredColimitMap f hX hY =
            l ≫ (colimit.ι X k ≫ filteredColimitMap f hX hY) :=
          Category.assoc _ _ _
        _ = l ≫ (f.app k ≫ colimit.ι Y k) :=
          congrArg (fun z => l ≫ z) (hι k)
        _ = (l ≫ f.app k) ≫ colimit.ι Y k := (Category.assoc _ _ _).symm
        _ = b₁ ≫ colimit.ι Y k := congrArg (fun z => z ≫ colimit.ι Y k) hl₂
        _ = (b₀ ≫ Y.map s) ≫ colimit.ι Y k := rfl
        _ = b₀ ≫ (Y.map s ≫ colimit.ι Y k) := Category.assoc _ _ _
        _ = b₀ ≫ colimit.ι Y j₀ :=
          congrArg (fun z => b₀ ≫ z) (colimit.w Y s)
        _ = b := hb₀

/-! ## Homotopy equivalence -/

/-- A trivial Kan fibration admits a simplicial section. -/
theorem trivialKanFibration_has_section
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : TrivialKanFibration f) :
    ∃ g : Y ⟶ X, g ≫ f = 𝟙 Y := by
  let e : (SSet.boundary 0 : SSet.{u}) ≅ (⊥_ SSet.{u}) := by
    rw [SSet.boundary_zero]
    exact
      (SSet.Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u})).uniqueUpToIso
        initialIsInitial)
  have hi_e : ∀ n, Function.Injective
      (ConcreteCategory.hom (e.inv.app (op (SimplexCategory.mk n)))) := by
    intro n x y hxy
    apply_fun ConcreteCategory.hom (e.hom.app (op (SimplexCategory.mk n))) at hxy
    simpa using hxy
  have hi : TermwiseInjective (initial.to Y) := by
    intro n x y hxy
    refine hi_e n ?_
    apply Subtype.ext
    let _ : Subsingleton ((Δ[0] : SSet.{u}) _⦋n⦌) :=
      Unit26.pointSimplex_subsingleton n
    exact Subsingleton.elim _ _
  obtain ⟨g, _, hg⟩ := trivialKanFibration_lift f hf
    (initial.to Y) hi (initial.to X) (𝟙 Y)
    (by apply initial.hom_ext)
  exact ⟨g, hg⟩

private lemma boundary_one_simplex_is_const {n : ℕ}
    (z : (SSet.boundary 1 : SSet.{u}) _⦋n⦌) :
    (∀ k : Fin (n + 1), z.1 k = 0) ∨
      (∀ k : Fin (n + 1), z.1 k = 1) := by
  obtain ⟨j, hj⟩ :=
    (SSet.mem_boundary_iff_notMem_range z.1).1 z.2
  fin_cases j
  · right
    intro k
    apply Fin.eq_one_of_ne_zero
    intro hk
    exact hj ⟨k, hk⟩
  · left
    intro k
    by_cases hk : z.1 k = 0
    · exact hk
    · have hk' : z.1 k = 1 := Fin.eq_one_of_ne_zero _ hk
      exfalso
      apply hj
      refine ⟨k, ?_⟩
      exact hk'

private def endpointMap {X : SSet.{u}} (p q : X ⟶ X) :
    (X ⊗ (SSet.boundary.{u} 1 : SSet.{u})) ⟶ X := {
  app := fun m => TypeCat.ofHom (fun z =>
    if (SSet.stdSimplex.asOrderHom z.2.1) 0 = 0 then p.app m z.1 else q.app m z.1)
  naturality := by
    intro m n α
    ext z
    obtain hz | hz := boundary_one_simplex_is_const z.2
    · have hz0 : (SSet.stdSimplex.asOrderHom z.2.1) 0 = 0 := hz 0
      have hzm : (SSet.stdSimplex.asOrderHom
          (((X ⊗ (SSet.boundary.{u} 1 : SSet.{u})).map α z).2).1) 0 = 0 := by
        change (SSet.stdSimplex.asOrderHom
          (((SSet.boundary.{u} 1 : SSet.{u}).map α z.2).1)) 0 = 0
        change (SSet.stdSimplex.asOrderHom
          ((Δ[1] : SSet.{u}).map α z.2.1)) 0 = 0
        rw [SSet.stdSimplex.map_apply]
        change (SSet.stdSimplex.objEquiv z.2.1).toOrderHom (α.unop 0) = 0
        have hobj : (SSet.stdSimplex.objEquiv z.2.1).toOrderHom =
            SSet.stdSimplex.asOrderHom z.2.1 := rfl
        rw [hobj]
        exact hz (α.unop 0)
      simp only [types_comp_apply, ConcreteCategory.hom_ofHom,
        TypeCat.Fun.coe_mk, TypeCat.Fun.toFun_apply]
      rw [if_pos hzm, if_pos hz0]
      exact ConcreteCategory.congr_hom (p.naturality α) z.1
    · have hz1 : (SSet.stdSimplex.asOrderHom z.2.1) 0 = 1 := hz 0
      have hzm : (SSet.stdSimplex.asOrderHom
          (((X ⊗ (SSet.boundary.{u} 1 : SSet.{u})).map α z).2).1) 0 = 1 := by
        change (SSet.stdSimplex.asOrderHom
          (((SSet.boundary.{u} 1 : SSet.{u}).map α z.2).1)) 0 = 1
        change (SSet.stdSimplex.asOrderHom
          ((Δ[1] : SSet.{u}).map α z.2.1)) 0 = 1
        rw [SSet.stdSimplex.map_apply]
        change (SSet.stdSimplex.objEquiv z.2.1).toOrderHom (α.unop 0) = 1
        have hobj : (SSet.stdSimplex.objEquiv z.2.1).toOrderHom =
            SSet.stdSimplex.asOrderHom z.2.1 := rfl
        rw [hobj]
        exact hz (α.unop 0)
      simp only [types_comp_apply, ConcreteCategory.hom_ofHom,
        TypeCat.Fun.coe_mk, TypeCat.Fun.toFun_apply]
      have hneₘ : ¬ (SSet.stdSimplex.asOrderHom
          (((X ⊗ (SSet.boundary.{u} 1 : SSet.{u})).map α z).2).1) 0 = 0 := by
        rw [hzm]
        exact Ne.symm Fin.zero_ne_one
      have hne : ¬ (SSet.stdSimplex.asOrderHom z.2.1) 0 = 0 := by
        rw [hz1]
        exact Ne.symm Fin.zero_ne_one
      rw [if_neg hneₘ, if_neg hne]
      exact ConcreteCategory.congr_hom (q.naturality α) z.1
}

private lemma endpointMap_apply {X : SSet.{u}} (p q : X ⟶ X)
    (m : SimplexCategoryᵒᵖ) (z : (X ⊗ (SSet.boundary 1 : SSet.{u})).obj m) :
    (endpointMap p q).app m z =
      if (SSet.stdSimplex.asOrderHom z.2.1) 0 = 0 then
        p.app m z.1 else q.app m z.1 := rfl

private def boundaryEndpoint {X : SSet.{u}} (i : Fin 2) :
    X ⟶ X ⊗ (SSet.boundary 1 : SSet.{u}) :=
  CartesianMonoidalCategory.lift (𝟙 X)
    (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0) ≫ SSet.boundary.ι i)

private lemma endpointMap_zero {X : SSet.{u}} (p q : X ⟶ X) :
    boundaryEndpoint (X := X) (1 : Fin 2) ≫ endpointMap p q = p := by
  ext m x
  change (endpointMap p q).app m
      ((boundaryEndpoint (X := X) (1 : Fin 2)).app m x) = p.app m x
  rw [endpointMap_apply]
  have hx : ((boundaryEndpoint (X := X) (1 : Fin 2)).app m x).1 = x := by
    rfl
  have hz : (SSet.stdSimplex.asOrderHom
      ((boundaryEndpoint (X := X) (1 : Fin 2)).app m x).2.1) 0 = 0 := by
    change (SSet.stdSimplex.asOrderHom
      (((SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0) ≫
        SSet.boundary.ι (1 : Fin 2)).app m x).1)) 0 = 0
    rw [SSet.const_comp]
    change (SSet.stdSimplex.asOrderHom.{u}
      (SSet.stdSimplex.objEquiv.{u}.symm
        ((SimplexCategory.Hom.mk OrderHom.id : ⦋0⦌ ⟶ ⦋0⦌) ≫
          SimplexCategory.δ (1 : Fin 2)))) 0 = 0
    change (((SimplexCategory.Hom.mk OrderHom.id : ⦋0⦌ ⟶ ⦋0⦌) ≫
      SimplexCategory.δ (1 : Fin 2)).toOrderHom) 0 = 0
    rfl
  rw [hx, hz]
  simp

private lemma endpointMap_one {X : SSet.{u}} (p q : X ⟶ X) :
    boundaryEndpoint (X := X) (0 : Fin 2) ≫ endpointMap p q = q := by
  ext m x
  change (endpointMap p q).app m
      ((boundaryEndpoint (X := X) (0 : Fin 2)).app m x) = q.app m x
  rw [endpointMap_apply]
  have hx : ((boundaryEndpoint (X := X) (0 : Fin 2)).app m x).1 = x := by
    rfl
  have hz : (SSet.stdSimplex.asOrderHom
      ((boundaryEndpoint (X := X) (0 : Fin 2)).app m x).2.1) 0 = 1 := by
    change (SSet.stdSimplex.asOrderHom
      (((SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0) ≫
        SSet.boundary.ι (0 : Fin 2)).app m x).1)) 0 = 1
    rw [SSet.const_comp]
    change (SSet.stdSimplex.asOrderHom.{u}
      (SSet.stdSimplex.objEquiv.{u}.symm
        ((SimplexCategory.Hom.mk OrderHom.id : ⦋0⦌ ⟶ ⦋0⦌) ≫
          SimplexCategory.δ (0 : Fin 2)))) 0 = 1
    change (((SimplexCategory.Hom.mk OrderHom.id : ⦋0⦌ ⟶ ⦋0⦌) ≫
      SimplexCategory.δ (0 : Fin 2)).toOrderHom) 0 = 1
    rfl
  rw [hx, hz]
  rfl

private lemma boundaryEndpoint_zero_comp {X : SSet.{u}} :
    boundaryEndpoint (X := X) (1 : Fin 2) ≫
        (X ◁ (SSet.boundary 1).ι) = SSet.ι₀ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [boundaryEndpoint]
  · simp [boundaryEndpoint]
    congr 1

private lemma boundaryEndpoint_one_comp {X : SSet.{u}} :
    boundaryEndpoint (X := X) (0 : Fin 2) ≫
        (X ◁ (SSet.boundary 1).ι) = SSet.ι₁ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [boundaryEndpoint]
  · simp [boundaryEndpoint]
    congr 1

/-- Every trivial Kan fibration is a homotopy equivalence of simplicial sets. -/
theorem trivialKanFibration_isHomotopyEquivalence
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : TrivialKanFibration f) :
    Formalization.Books.Simplicial.Unit26.IsHomotopyEquivalence f := by
  obtain ⟨g, hg⟩ := trivialKanFibration_has_section f hf
  let i : (X ⊗ (SSet.boundary 1 : SSet.{u})) ⟶ X ⊗ Δ[1] :=
    X ◁ (SSet.boundary 1).ι
  let a : (X ⊗ (SSet.boundary 1 : SSet.{u})) ⟶ X :=
    endpointMap (f ≫ g) (𝟙 X)
  let b : (X ⊗ Δ[1]) ⟶ Y :=
    CartesianMonoidalCategory.fst X Δ[1] ≫ f
  have hi : TermwiseInjective i := by
    intro n x y hxy
    have hxy₁ : x.1 = y.1 := congrArg (fun z => z.1) hxy
    have hxy₂ : x.2 = y.2 := by
      apply Subtype.ext
      have hxy' := congrArg (fun z => z.2) hxy
      change x.2.1 = y.2.1 at hxy'
      exact hxy'
    exact Prod.ext hxy₁ hxy₂
  have hfg : (f ≫ g) ≫ f = f := by
    rw [Category.assoc, hg, Category.comp_id]
  have comm : a ≫ f = i ≫ b := by
    ext m z
    obtain hz | hz := boundary_one_simplex_is_const z.2
    · have hz0 : (SSet.stdSimplex.asOrderHom z.2.1) 0 = 0 := hz 0
      have hzi : (SSet.stdSimplex.asOrderHom
          ((SSet.boundary 1).ι.app m z.2)) 0 = 0 := by
        change (SSet.stdSimplex.asOrderHom z.2.1) 0 = 0
        exact hz0
      dsimp only [a, i, b]
      change (ConcreteCategory.hom (f.app m))
          ((endpointMap (f ≫ g) (𝟙 X)).app m z) =
        (ConcreteCategory.hom (f.app m)) z.1
      rw [endpointMap_apply, if_pos hz0]
      exact ConcreteCategory.congr_hom (congr_app hfg m) z.1
    · have hz1 : (SSet.stdSimplex.asOrderHom z.2.1) 0 = 1 := hz 0
      have hzi : (SSet.stdSimplex.asOrderHom
          ((SSet.boundary 1).ι.app m z.2)) 0 = 1 := by
        change (SSet.stdSimplex.asOrderHom z.2.1) 0 = 1
        exact hz1
      dsimp only [a, i, b]
      have hne : ¬ (SSet.stdSimplex.asOrderHom z.2.1) 0 = 0 := by
        rw [hz1]
        exact Ne.symm Fin.zero_ne_one
      change (ConcreteCategory.hom (f.app m))
          ((endpointMap (f ≫ g) (𝟙 X)).app m z) =
        (ConcreteCategory.hom (f.app m)) z.1
      rw [endpointMap_apply, if_neg hne]
      rfl
  obtain ⟨l, hl₁, hl₂⟩ := trivialKanFibration_lift f hf i hi a b comm
  have h₀ : SSet.ι₀ ≫ l = f ≫ g := by
    rw [← boundaryEndpoint_zero_comp, Category.assoc, hl₁, endpointMap_zero]
  have h₁ : SSet.ι₁ ≫ l = 𝟙 X := by
    rw [← boundaryEndpoint_one_comp, Category.assoc, hl₁, endpointMap_one]
  let H : SSet.Homotopy (f ≫ g) (𝟙 X) := {
    h := l
    h₀ := h₀
    h₁ := h₁
    rel := by
      ext m x
      exact x.1.property.elim
  }
  refine ⟨g, ?_, ?_⟩
  · rw [hg]
    exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _
      ⟨SSet.Homotopy.toSimplicialObjectHomotopy H⟩

/-! The displayed cylinder in the final proof is represented by Mathlib's
`SSet.Homotopy`, whose interval object is `Δ[1]`; the degreewise identity
`(∂Δ[1] × X)_n ≅ X_n ⊔ X_n` is consequently subsumed by that established
endpoint API.
-/

end Formalization.Books.Simplicial.Unit30
