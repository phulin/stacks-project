import Formalization.Books.Simplicial.Unit30
import Formalization.Books.Simplicial.Unit27.HomotopiesInAbelianCategories
import Formalization.Books.Simplicial.Unit23.SimplicialObjectsAndChainComplexes
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Preadditive.CommGrp_
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.AlgebraicTopology.ModelCategory.Instances
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Simplicial Methods, Chapter 31: Kan fibrations

The horn `Λ[n, k]` is Mathlib's canonical `SSet.horn n k`, and the category
with fibrations on simplicial sets is Mathlib's canonical Quillen structure.
The standard simplex, its unique top simplex, and its face inclusions are
likewise provided by Mathlib's `SSet.stdSimplex` API.  Consequently the
source's Kan-fibration and Kan-complex definitions are recorded by the
corresponding canonical properties rather than by parallel lifting predicates.
The remaining declarations give the closure results and the
simplicial-group and simplicial-abelian-group applications from the source.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit31

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial
open SSet.modelCategoryQuillen

universe u v w

/-! ## Horns and the Kan lifting property

The source assumes `1 ≤ n` whenever it discusses an `n`-horn.  The canonical
`SSet.horn` supplies the generated subcomplex and its inclusion; the
`horn_obj_zero` lemma supplies the nonemptiness assertion in the positive
dimensions used below.
-/

/-- The source's Kan-fibration property, using Mathlib's canonical fibration
class for simplicial sets (whose generating lifting maps are the horn
inclusions). -/
abbrev KanFibration {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  HomotopicalAlgebra.Fibration f

/-- The source's Kan-complex property, using Mathlib's canonical fibrant
objects in simplicial sets. -/
abbrev KanComplex (X : SSet.{u}) : Prop :=
  SSet.KanComplex X

/-- Every positive-dimensional horn has a vertex. -/
theorem horn_nonempty (n : ℕ) (hn : 1 ≤ n) (k : Fin (n + 1)) :
    Nonempty ((SSet.horn n k : SSet.{u}) _⦋0⦌) := by
  obtain _ | n := n
  · omega
  obtain _ | n := n
  · fin_cases k
    · refine ⟨⟨SSet.stdSimplex.objEquiv.symm (⦋0⦌.const ⦋1⦌ 0), ?_⟩⟩
      rw [SSet.mem_horn_iff, SSet.stdSimplex.coe_asOrderHom_objEquiv_symm]
      intro h
      rw [Set.eq_univ_iff_forall] at h
      have h1 := h (1 : Fin 2)
      simp at h1
      change (0 : Fin 2) = 1 at h1
      exact Fin.zero_ne_one h1
    · refine ⟨⟨SSet.stdSimplex.objEquiv.symm (⦋0⦌.const ⦋1⦌ 1), ?_⟩⟩
      rw [SSet.mem_horn_iff, SSet.stdSimplex.coe_asOrderHom_objEquiv_symm]
      intro h
      rw [Set.eq_univ_iff_forall] at h
      have h0 := h (0 : Fin 2)
      simp at h0
      change (1 : Fin 2) = 0 at h0
      omega
  · have htop := SSet.horn_obj_zero n k
    refine ⟨⟨SSet.stdSimplex.objEquiv.symm (⦋0⦌.const ⦋n + 2⦌ 0), ?_⟩⟩
    rw [htop]
    simp

/-! The source's observation about the empty simplicial set is the vacuous
lifting property.  We retain it as a theorem interface; the implication from
trivial to ordinary Kan fibrations is the canonical inclusion of lifting
classes already present in Chapter 30 and Mathlib's model-category API. -/

theorem empty_to_kanFibration {Y : SSet.{u}} (f : (⊥_ SSet.{u}) ⟶ Y) :
    KanFibration f := by
  change HomotopicalAlgebra.Fibration f
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J,
    CategoryTheory.MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  refine ⟨fun {a} {b} sq => ?_⟩
  let x := (horn_nonempty (n + 1) (by omega) k).some
  let y := a.app (op ⦋0⦌) x
  let z₀ : (Δ[1] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm 0
  let z₁ : (Δ[1] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm 1
  have hconst : SSet.const (X := ⊥_ SSet.{u}) z₀ = SSet.const z₁ :=
    initialIsInitial.hom_ext _ _
  have hval := ConcreteCategory.congr_hom (congr_app hconst (op ⦋0⦌)) y
  have h01 : (0 : Fin 2) = 1 := by
    have hval' := congrArg SSet.stdSimplex.obj₀Equiv hval
    change (0 : Fin 2) = 1 at hval'
    exact hval'
  exact (Fin.zero_ne_one h01).elim

theorem trivialKanFibration_kanFibration
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : Formalization.Books.Simplicial.Unit30.TrivialKanFibration f) :
    KanFibration f := by
  change HomotopicalAlgebra.Fibration f
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J,
    CategoryTheory.MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  refine ⟨fun {a} {b} sq => ?_⟩
  obtain ⟨l, hl, hr⟩ :=
    Formalization.Books.Simplicial.Unit30.trivialKanFibration_lift f hf
      (SSet.horn (n + 1) k).ι
      (by
        intro d
        exact Subtype.val_injective) a b sq.w
  exact ⟨⟨{ l := l, fac_left := hl, fac_right := hr }⟩⟩

/-! ## Closure properties -/

/-- Kan fibrations are preserved by base change. -/
theorem kanFibration_baseChange
    {X Y Y' : SSet.{u}} (f : X ⟶ Y) (hf : KanFibration f)
    (g : Y' ⟶ Y) :
    KanFibration (pullback.snd f g) := by
  sorry

/-- The composite of Kan fibrations is a Kan fibration. -/
theorem kanFibration_comp
    {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : KanFibration f) (hg : KanFibration g) :
    KanFibration (f ≫ g) := by
  change HomotopicalAlgebra.Fibration f at hf
  change HomotopicalAlgebra.Fibration g at hg
  change HomotopicalAlgebra.Fibration (f ≫ g)
  rw [SSet.modelCategoryQuillen.fibration_iff] at hf hg ⊢
  exact (SSet.modelCategoryQuillen.J.rlp).comp_mem f g hf hg

private lemma kanFibration_limit_horn_lift
    (U : ℕᵒᵖ ⥤ SSet.{u})
    (hU : ∀ n : ℕ,
      KanFibration
        (Formalization.Books.Simplicial.Unit30.inverseSequenceTransition U n))
    {n : ℕ} (k : Fin (n + 2))
    (a : (SSet.horn (n + 1) k : SSet.{u}) ⟶ limit U)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ U.obj (op 0))
    (comm : a ≫ limit.π U (op 0) = (SSet.horn (n + 1) k).ι ≫ b) :
    ∃ l : (Δ[n + 1] : SSet.{u}) ⟶ limit U,
      (SSet.horn (n + 1) k).ι ≫ l = a ∧
        l ≫ limit.π U (op 0) = b := by
  let LiftType : ℕᵒᵖ → Type u := fun j =>
    {l : (Δ[n + 1] : SSet.{u}) ⟶ U.obj j |
      (SSet.horn (n + 1) k).ι ≫ l = a ≫ limit.π U j}
  let mapLift : ∀ {i j : ℕᵒᵖ}, (i ⟶ j) → LiftType i → LiftType j :=
    fun {i j} α z => by
      change {l : (Δ[n + 1] : SSet.{u}) ⟶ U.obj j |
        (SSet.horn (n + 1) k).ι ≫ l = a ≫ limit.π U j}
      change {l : (Δ[n + 1] : SSet.{u}) ⟶ U.obj i |
        (SSet.horn (n + 1) k).ι ≫ l = a ≫ limit.π U i} at z
      refine ⟨z.1 ≫ U.map α, ?_⟩
      change (SSet.horn (n + 1) k).ι ≫ (z.1 ≫ U.map α) =
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
  let val : ∀ j, F.obj j → ((Δ[n + 1] : SSet.{u}) ⟶ U.obj j) := fun j z => by
    change LiftType j at z
    exact z.1
  let d : F.WellOrderInductionData :=
    Functor.WellOrderInductionData.ofExists (F := F) (fun j _ z => by
      change LiftType (op j) at z
      have hrlp : SSet.modelCategoryQuillen.J.rlp
          (Formalization.Books.Simplicial.Unit30.inverseSequenceTransition U j) :=
        (SSet.modelCategoryQuillen.fibration_iff _).1 (hU j)
      have hsq : HasLiftingProperty (SSet.horn (n + 1) k).ι
          (Formalization.Books.Simplicial.Unit30.inverseSequenceTransition U j) :=
        hrlp _ (SSet.modelCategoryQuillen.horn_ι_mem_J _ _)
      let sq : CommSq
          (a ≫ limit.π U (op (j + 1)))
          (SSet.horn (n + 1) k).ι
          (Formalization.Books.Simplicial.Unit30.inverseSequenceTransition U j)
          z.1 :=
        ⟨by
          change (a ≫ limit.π U (op (j + 1))) ≫
              U.map (homOfLE (Nat.le_succ j)).op =
            (SSet.horn (n + 1) k).ι ≫ z.1
          rw [Category.assoc, limit.w, z.2]⟩
      obtain ⟨l, hl₁, hl₂⟩ := (hsq.sq_hasLift sq).exists_lift.some
      change ∃ y : LiftType (op (Order.succ j)), F.map _ y = z
      refine ⟨⟨l, hl₁⟩, ?_⟩
      change mapLift (homOfLE (Nat.le_succ j)).op ⟨l, hl₁⟩ = z
      apply Subtype.ext
      change l ≫ U.map (homOfLE (Nat.le_succ j)).op = z.1
      exact hl₂)
      (fun j hj x => (Order.not_isSuccLimit_natCast j hj).elim)
  let s : F.sections := d.sectionsMk x₀
  let c : Cone U :=
    { pt := (Δ[n + 1] : SSet.{u})
      π :=
        { app := fun j => val j (s.val j)
          naturality := by
            intro i j α
            have hs := congrArg (fun z => val j z) (s.property α)
            simpa [F, mapLift, val, LiftType, Category.assoc] using hs.symm } }
  let l : (Δ[n + 1] : SSet.{u}) ⟶ limit U := limit.lift U c
  have hl₀ : (SSet.horn (n + 1) k).ι ≫ l = a := by
    apply (limit.isLimit U).hom_ext
    intro j
    have hsj : (SSet.horn (n + 1) k).ι ≫ val j (s.val j) =
        a ≫ limit.π U j := by
      unfold val
      change (SSet.horn (n + 1) k).ι ≫ (s.val j : LiftType j).1 =
        a ≫ limit.π U j
      exact (show LiftType j from s.val j).2
    simpa [l, c, Category.assoc] using hsj
  have hl₁ : l ≫ limit.π U (op 0) = b := by
    have h := congrArg (fun z => val (op 0) z)
      (d.sectionsMk_val_op_bot x₀)
    simpa [l, c, s, x₀, val, LiftType] using h
  exact ⟨l, hl₀, hl₁⟩

/-- The projection from the inverse limit of a sequence of Kan fibrations to
its zeroth term is a Kan fibration. -/
theorem kanFibration_limit
    (U : ℕᵒᵖ ⥤ SSet.{u})
    (hU : ∀ n : ℕ,
      KanFibration
        (Formalization.Books.Simplicial.Unit30.inverseSequenceTransition U n)) :
    KanFibration (limit.π U (op 0)) := by
  change HomotopicalAlgebra.Fibration (limit.π U (op 0))
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J,
    CategoryTheory.MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  refine ⟨fun {a} {b} sq => ?_⟩
  obtain ⟨l, hl₁, hl₂⟩ := kanFibration_limit_horn_lift U hU k a b sq.w
  exact ⟨⟨{ l := l, fac_left := hl₁, fac_right := hl₂ }⟩⟩

/-- Products of Kan fibrations are Kan fibrations. -/
theorem kanFibration_product
    {T : Type w} {X Y : T → SSet.{u}}
    (hX : HasLimit (Discrete.functor X))
    (hY : HasLimit (Discrete.functor Y))
    (f : ∀ t, X t ⟶ Y t)
    (hf : ∀ t, KanFibration (f t)) :
    KanFibration
      (Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f) := by
  let Xs : T → SSet := X
  let Ys : T → SSet := Y
  change HomotopicalAlgebra.Fibration
    (Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f)
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A0 B0 i0 hi0
  simp only [SSet.modelCategoryQuillen.J,
    CategoryTheory.MorphismProperty.iSup_iff] at hi0
  obtain ⟨n, ⟨k⟩⟩ := hi0
  refine ⟨fun {a} {b} sq => ?_⟩
  let sqt : ∀ t : T,
      CommSq
        (a ≫ limit.π (Discrete.functor Xs) ⟨t⟩)
        (SSet.horn (n + 1) k).ι
        (f t)
        (b ≫ limit.π (Discrete.functor Ys) ⟨t⟩) := fun t =>
    ⟨by
      have hproj :
          Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f ≫
              limit.π (Discrete.functor Ys) ⟨t⟩ =
            limit.π (Discrete.functor Xs) ⟨t⟩ ≫ f t := by
        simpa only [Xs, Ys] using
          (Formalization.Books.Simplicial.Unit26.indexedProductMap_comp_projection
            hX hY f t)
      calc
        (a ≫ limit.π (Discrete.functor Xs) ⟨t⟩) ≫ f t =
            a ≫ (limit.π (Discrete.functor Xs) ⟨t⟩ ≫ f t) :=
          Category.assoc _ _ _
        _ = a ≫
            (Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f ≫
              limit.π (Discrete.functor Ys) ⟨t⟩) :=
          congrArg (fun z => a ≫ z) hproj.symm
        _ = (a ≫ Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f) ≫
            limit.π (Discrete.functor Ys) ⟨t⟩ :=
          (Category.assoc _ _ _).symm
        _ = (SSet.horn (n + 1) k).ι ≫ b ≫
            limit.π (Discrete.functor Ys) ⟨t⟩ :=
          (congrArg (fun z => z ≫ limit.π (Discrete.functor Ys) ⟨t⟩) sq.w).trans
            (Category.assoc _ _ _ )⟩
  let l : ∀ t : T, (sqt t).LiftStruct := fun t => by
    have hrlp : SSet.modelCategoryQuillen.J.rlp (f t) :=
      (SSet.modelCategoryQuillen.fibration_iff (f t)).1 (hf t)
    have hsq : HasLiftingProperty (SSet.horn (n + 1) k).ι (f t) :=
      hrlp _ (SSet.modelCategoryQuillen.horn_ι_mem_J _ _)
    exact (hsq.sq_hasLift (sqt t)).exists_lift.some
  let c : Cone (Discrete.functor Xs) :=
    { pt := (Δ[n + 1] : SSet.{u})
      π :=
        { app := fun t => (l t.as).l
          naturality := by
            rintro ⟨i⟩ ⟨j⟩ g
            obtain rfl : i = j := Discrete.eq_of_hom g
            simp } }
  let l' : (Δ[n + 1] : SSet.{u}) ⟶ limit (Discrete.functor Xs) :=
    limit.lift (Discrete.functor Xs) c
  refine ⟨⟨{ l := l', fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply (limit.isLimit (Discrete.functor Xs)).hom_ext
    intro t
    have hlift :
        l' ≫ limit.π (Discrete.functor Xs) t = (l t.as).l := by
      change limit.lift (Discrete.functor Xs) c ≫
        limit.π (Discrete.functor Xs) t = (l t.as).l
      rw [limit.lift_π]
    calc
      ((SSet.horn (n + 1) k).ι ≫ l') ≫
          limit.π (Discrete.functor Xs) t =
          (SSet.horn (n + 1) k).ι ≫
            (l' ≫ limit.π (Discrete.functor Xs) t) :=
        Category.assoc _ _ _
      _ = (SSet.horn (n + 1) k).ι ≫ (l t.as).l :=
        congrArg (fun z => (SSet.horn (n + 1) k).ι ≫ z) hlift
      _ = a ≫ limit.π (Discrete.functor Xs) t :=
        (l t.as).fac_left
  · apply (limit.isLimit (Discrete.functor Ys)).hom_ext
    intro t
    change
      (l' ≫ Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f) ≫
          limit.π (Discrete.functor Ys) t =
        b ≫ limit.π (Discrete.functor Ys) t
    have hproj :
        Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f ≫
            limit.π (Discrete.functor Ys) t =
          limit.π (Discrete.functor Xs) t ≫ f t.as := by
      simpa only [Xs, Ys] using
        (Formalization.Books.Simplicial.Unit26.indexedProductMap_comp_projection
          hX hY f t.as)
    have hlift :
        l' ≫ limit.π (Discrete.functor Xs) t = (l t.as).l := by
      change limit.lift (Discrete.functor Xs) c ≫
        limit.π (Discrete.functor Xs) t = (l t.as).l
      rw [limit.lift_π]
    calc
      (l' ≫ Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f) ≫
          limit.π (Discrete.functor Ys) t =
          l' ≫ (Formalization.Books.Simplicial.Unit26.indexedProductMap hX hY f ≫
            limit.π (Discrete.functor Ys) t) :=
        Category.assoc _ _ _
      _ = l' ≫ (limit.π (Discrete.functor Xs) t ≫ f t.as) :=
        congrArg (fun z => l' ≫ z) hproj
      _ = (l' ≫ limit.π (Discrete.functor Xs) t) ≫ f t.as :=
        (Category.assoc _ _ _).symm
      _ = (l t.as).l ≫ f t.as :=
        congrArg (fun z => z ≫ f t.as) hlift
      _ = b ≫ limit.π (Discrete.functor Ys) t :=
        (l t.as).fac_right

/-! ## Simplicial groups -/

/-- The underlying simplicial set of a simplicial group. -/
def underlyingSimplicialGroup
    (X : SimplicialObject CommGrpCat.{u}) : SSet.{u} :=
  ((SimplicialObject.whiskering CommGrpCat (Type u)).obj
    (CategoryTheory.forget CommGrpCat)).obj X

/-- The underlying simplicial map of a map of simplicial groups. -/
def underlyingSimplicialGroupMap
    {X Y : SimplicialObject CommGrpCat.{u}} (f : X ⟶ Y) :
    underlyingSimplicialGroup X ⟶ underlyingSimplicialGroup Y :=
  ((SimplicialObject.whiskering CommGrpCat (Type u)).obj
    (CategoryTheory.forget CommGrpCat)).map f

/-- The positive-dimensional part of the simplicial-group horn filler. -/
private theorem simplicialGroup_kanComplex_succ
    (X : SimplicialObject CommGrpCat.{u}) {m : ℕ}
    {i : Fin (m + 3)}
    (f : ∀ (j : Fin (m + 3)) (_ : j ≠ i),
      Δ[m + 1] ⟶ underlyingSimplicialGroup X)
    (hf : SSet.horn.IsCompatible f) :
    ∃ φ : Δ[m + 2] ⟶ underlyingSimplicialGroup X,
      ∀ (j : Fin (m + 3)) (hj : j ≠ i),
        SSet.stdSimplex.δ j ≫ φ = f j hj := by
  let n := m + 1
  let xj : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      X.obj (op (SimplexCategory.mk n)) := fun j hj =>
    SSet.yonedaEquiv (f j hj)
  have hface : ∀ (j k : Fin (n + 2)) (hj : j ≠ i) (hk : k ≠ i)
      (hjk : j < k),
      X.δ (k.pred (Fin.ne_zero_of_lt hjk)) (xj j hj) =
        X.δ (j.castPred (Fin.ne_last_of_lt hjk)) (xj k hk) := by
    intro j k hj hk hjk
    have h := congrArg SSet.yonedaEquiv (hf.δ_pred_comp j k hj hk hjk)
    simpa [xj, SSet.yonedaEquiv_comp, underlyingSimplicialGroup] using h
  let xzero : X.obj (op (SimplexCategory.mk n)) := xj 0 (by
    intro h
    subst h
    exact (i.isLt.false (by simp)))
  let u₀ : X.obj (op (SimplexCategory.mk (n + 1))) := X.σ 0 xzero
  have hu₀ : X.δ 0 u₀ = xzero := by
    dsimp [u₀]
    rw [X.δ_comp_σ_self]
    rfl
  let uStep : ℕ → X.obj (op (SimplexCategory.mk (n + 1))) →
      X.obj (op (SimplexCategory.mk (n + 1))) := fun r z =>
    if hr : r + 1 < i.val then
      let j : Fin (n + 2) := ⟨r + 1, by omega⟩
      z * X.σ ⟨r + 1, by omega⟩
        ((X.δ ⟨r + 1, by omega⟩ z)⁻¹ * xj j (by
          intro h
          subst h
          exact (by omega)))
    else z
  let uSeq : ℕ → X.obj (op (SimplexCategory.mk (n + 1))) :=
    Nat.rec (if hi : 0 < i.val then
      X.σ 0 (xj 0 (by intro h; subst h; omega)) else 1) uStep
  have huSeq : ∀ r : ℕ, r < i.val →
      ∀ (q : Fin (n + 2)) (hq : q.val ≤ r),
        X.δ q (uSeq r) = xj q (by
          intro h
          subst h
          exact (by omega)) := by
    intro r
    induction r with
    | zero =>
        intro hr q hq
        have hq0 : q = 0 := by ext; omega
        subst q
        simpa [uSeq, xzero, u₀] using hu₀
    | succ r ihr =>
        intro hr q hq
        by_cases hq' : q.val ≤ r
        · have hprev := ihr (by omega) q hq'
          simpa [uSeq, uStep, hr] using hprev
        · have hqr : q.val = r + 1 := by omega
          subst q
          have hstep := ihr (by omega)
          let s : Fin (n + 1) := ⟨r + 1, by omega⟩
          have hs : (⟨r + 1, by omega⟩ : Fin (n + 2)) = Fin.castSucc s := by
            ext
            rfl
          have hδσ : X.δ (⟨r + 1, by omega⟩ : Fin (n + 2)) ≫ X.σ s = 𝟙 _ := by
            rw [hs, X.δ_comp_σ_self]
          dsimp [uSeq, uStep]
          rw [if_pos hr]
          change X.δ (⟨r + 1, by omega⟩ : Fin (n + 2))
              (uSeq r * X.σ s
                ((X.δ (⟨r + 1, by omega⟩ : Fin (n + 2)) (uSeq r))⁻¹ *
                  xj ⟨r + 1, by omega⟩ (by omega))) = _
          rw [(X.δ (⟨r + 1, by omega⟩ : Fin (n + 2))).map_mul,
            ← hδσ]
          simp [hstep]
  let u : X.obj (op (SimplexCategory.mk (n + 1))) :=
    if hi : i.val = 0 then 1 else uSeq i.val
  have hu : ∀ (q : Fin (n + 2)) (hq : q.val < i.val),
      X.δ q u = xj q (by
        intro h
        subst h
        omega) := by
    intro q hq
    by_cases hi : i.val = 0
    · omega
    · dsimp [u]
      rw [dif_neg hi]
      exact huSeq i.val (by omega) q (by omega)
  let vStep : ℕ → X.obj (op (SimplexCategory.mk (n + 1))) →
      X.obj (op (SimplexCategory.mk (n + 1))) := fun r z =>
    if hr : r < n + 1 - i.val then
      let q : Fin (n + 2) := ⟨n + 1 - r, by omega⟩
      let s : Fin (n + 1) := ⟨n - r, by omega⟩
      z * X.σ s
        ((X.δ q z)⁻¹ * xj q (by
          intro h
          subst h
          omega))
    else z
  let vSeq : ℕ → X.obj (op (SimplexCategory.mk (n + 1))) := Nat.rec u vStep
  have hvSeq : ∀ r : ℕ, r ≤ n + 1 - i.val →
      ∀ (q : Fin (n + 2)),
        (q.val < i.val ∨ n + 1 - r < q.val) →
        X.δ q (vSeq r) = xj q (by
          intro h
          subst h
          omega) := by
    intro r
    induction r with
    | zero =>
        intro hr q hq
        rcases hq with hq | hq
        · exact hu q hq
        · omega
    | succ r ihr =>
        intro hr q hq
      by_cases hqold : q.val < i.val ∨ n + 1 - r < q.val
        · have hprev := ihr (by omega) q hqold
          let q₁ : Fin (n + 2) := ⟨n + 1 - r, by omega⟩
          let s : Fin (n + 1) := ⟨n - r, by omega⟩
          have hq₁ : q₁ = s.succ := by
            ext
            rfl
          have hσ : X.δ q (X.σ s
              ((X.δ q₁ (vSeq r))⁻¹ * xj q₁ (by
                intro h
                subst h
                omega))) = 1 := by
            by_cases hleft : q.val < i.val
            · let q' : Fin (n + 1) := ⟨q.val, by omega⟩
              let s' : Fin n := ⟨s.val - 1, by omega⟩
              have hq' : q = Fin.castSucc q' := by
                ext
                rfl
              have hs' : s = s'.succ := by
                ext
                omega
              have hcomp : X.σ s ≫ X.δ q = X.δ q' ≫ X.σ s' := by
                rw [hq', hs']
                symm
                exact X.δ_comp_σ_of_le (by omega)
              have hdd : X.δ q₁ ≫ X.δ q' =
                  X.δ q ≫ X.δ (q₁.pred (by omega)) := by
                have hqcast : q₁ = Fin.castSucc (q₁.castLT (by omega)) := by
                  ext
                  rfl
                rw [hqcast]
                exact X.δ_comp_δ' (by omega)
              have hδz : X.δ q' (X.δ q₁ (vSeq r)) =
                  X.δ (q₁.pred (by omega)) (X.δ q (vSeq r)) := by
                simpa only [Category.assoc] using
                  congrArg (fun g => g (vSeq r)) hdd
              have hface' : X.δ q' (xj q₁ (by omega)) =
                  X.δ (q₁.pred (by omega)) (xj q₁) := by
                have h := hface q₁ q (by omega) (by omega) (by omega)
                simpa using h.symm
              change (X.σ s ≫ X.δ q)
                ((X.δ q₁ (vSeq r))⁻¹ * xj q₁ (by omega)) = 1
              rw [hcomp, (X.δ q').map_mul, hδz, hface',
                hprev, inv_mul_cancel]
              simp
            · have hright : n + 1 - r < q.val := by omega
              let q' : Fin (n + 1) := ⟨q.val - 1, by omega⟩
              let s' : Fin n := ⟨s.val, by omega⟩
              have hq' : q = q'.succ := by
                ext
                omega
              have hs' : s = Fin.castSucc s' := by
                ext
                rfl
              have hcomp : X.σ s ≫ X.δ q = X.δ q' ≫ X.σ s' := by
                rw [hq', hs']
                exact X.δ_comp_σ_of_gt (by omega)
              have hdd : X.δ q₁ ≫ X.δ q' =
                  X.δ (q'.succ) ≫ X.δ (q₁.castLT (by omega)) := by
                have hqcast : q₁ = Fin.castSucc (q₁.castLT (by omega)) := by
                  ext
                  rfl
                rw [hqcast]
                symm
                exact X.δ_comp_δ (by omega)
              have hδz : X.δ q' (X.δ q₁ (vSeq r)) =
                  X.δ (q₁.castLT (by omega)) (X.δ (q'.succ) (vSeq r)) := by
                simpa only [Category.assoc] using
                  congrArg (fun g => g (vSeq r)) hdd
              have hface' : X.δ q' (xj q₁ (by omega)) =
                  X.δ (q₁.castLT (by omega)) (xj (q'.succ) (by omega)) := by
                have h := hface q₁ (q'.succ) (by omega) (by omega) (by omega)
                simpa using h.symm
              change (X.σ s ≫ X.δ q)
                ((X.δ q₁ (vSeq r))⁻¹ * xj q₁ (by omega)) = 1
              rw [hcomp, (X.δ q').map_mul, hδz, hface',
                hprev, inv_mul_cancel]
              simp
          dsimp [vSeq, vStep]
          rw [if_pos (by omega), (X.δ q).map_mul, hprev, hσ]
          simp
        · have hqval : q.val = n + 1 - r := by omega
          subst q
          let q₁ : Fin (n + 2) := ⟨n + 1 - r, by omega⟩
          let s : Fin (n + 1) := ⟨n - r, by omega⟩
          have hq₁ : q₁ = s.succ := by
            ext
            rfl
          have hδσ : X.δ q₁ ≫ X.σ s = 𝟙 _ := by
            rw [hq₁, X.δ_comp_σ_succ]
          have hstep := ihr (by omega) q₁ (by omega)
          dsimp [vSeq, vStep]
          rw [if_pos (by omega), (X.δ q₁).map_mul, ← hδσ]
          simp [hstep]
  let z := vSeq (n + 1 - i.val)
  refine ⟨SSet.yonedaEquiv.symm z, ?_⟩
  intro q hq
  apply SSet.yonedaEquiv.injective
  have hz := hvSeq (n + 1 - i.val) (by omega) q (by
    by_cases hqi : q.val < i.val
    · exact Or.inl hqi
    · right
      omega)
  simpa [z, SSet.yonedaEquiv_comp, underlyingSimplicialGroup] using hz

/- The zero-dimensional horn has only one prescribed vertex, and a single
  degeneracy supplies a 1-simplex with that vertex as its required face. -/
theorem simplicialGroup_kanComplex
    (X : SimplicialObject CommGrpCat.{u}) :
    KanComplex (underlyingSimplicialGroup X) := by
  apply SSet.KanComplex.iff.mpr
  intro n i f hf
  rcases n with _ | m
  · by_cases hi : i = 0
    · subst i
      let x := SSet.yonedaEquiv (f 1 (by omega))
      refine ⟨SSet.yonedaEquiv.symm (X.σ 0 x), ?_⟩
      intro j hj
      have hj1 : j = 1 := by omega
      subst j
      apply SSet.yonedaEquiv.injective
      have h := congrArg (fun g => g x) (X.δ_comp_σ_succ (i := 0))
      simpa [x, SSet.yonedaEquiv_comp, underlyingSimplicialGroup] using h
    · have hi1 : i = 1 := by omega
      subst i
      let x := SSet.yonedaEquiv (f 0 (by omega))
      refine ⟨SSet.yonedaEquiv.symm (X.σ 0 x), ?_⟩
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      apply SSet.yonedaEquiv.injective
      have h := congrArg (fun g => g x) (X.δ_comp_σ_self (i := 0))
      simpa [x, SSet.yonedaEquiv_comp, underlyingSimplicialGroup] using h
  · exact simplicialGroup_kanComplex_succ X f hf

/-! ## Simplicial abelian groups -/

/-- The underlying simplicial set of a simplicial abelian group. -/
def underlyingSimplicialAbelianGroup
    (X : SimplicialObject AddCommGrpCat.{u}) : SSet.{u} :=
  ((SimplicialObject.whiskering AddCommGrpCat (Type u)).obj
    (CategoryTheory.forget AddCommGrpCat)).obj X

/-- The underlying simplicial map of a map of simplicial abelian groups. -/
def underlyingSimplicialAbelianGroupMap
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y) :
    underlyingSimplicialAbelianGroup X ⟶ underlyingSimplicialAbelianGroup Y :=
  ((SimplicialObject.whiskering AddCommGrpCat (Type u)).obj
    (CategoryTheory.forget AddCommGrpCat)).map f

private def simplicialAddCommGroupKernel
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y) :
    SimplicialObject AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of ((f.app n).hom.ker)
  map α := AddCommGrpCat.ofHom
    { toFun := fun x => ⟨X.map α x, by
        have h := congrArg (fun g => g x) (f.naturality α)
        simpa using h.symm.trans (by simp [x.property])⟩
      map_zero' := by
        ext
        simp
      map_add' := by
        intro x y
        ext
        simp }
  map_id := by
    intro n
    apply AddCommGrpCat.ext
    intro x
    rfl
  map_comp := by
    intro n m l α β
    apply AddCommGrpCat.ext
    intro x
    rfl

private def simplicialAddCommGroupKernelι
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y) :
    simplicialAddCommGroupKernel f ⟶ X :=
  { app := fun n => AddCommGrpCat.ofHom (AddSubgroup.subtype ((f.app n).hom.ker))
    naturality := by
      intro n m α
      apply AddCommGrpCat.ext
      intro x
      rfl }

private def simplicialCommGroupKernel
    {X Y : SimplicialObject CommGrpCat.{u}} (f : X ⟶ Y) :
    SimplicialObject CommGrpCat.{u} where
  obj n := CommGrpCat.of ((f.app n).hom.ker)
  map α := CommGrpCat.ofHom
    { toFun := fun x => ⟨X.map α x, by
        have h := congrArg (fun g => g x) (f.naturality α)
        simpa using h.symm.trans (by simp [x.property])⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro x y
        ext
        simp }
  map_id := by
    intro n
    apply CommGrpCat.ext
    intro x
    rfl
  map_comp := by
    intro n m l α β
    apply CommGrpCat.ext
    intro x
    rfl

private def simplicialCommGroupKernelι
    {X Y : SimplicialObject CommGrpCat.{u}} (f : X ⟶ Y) :
    simplicialCommGroupKernel f ⟶ X :=
  { app := fun n => CommGrpCat.ofHom (Subgroup.subtype ((f.app n).hom.ker))
    naturality := by
      intro n m α
      apply CommGrpCat.ext
      intro x
      rfl }

private theorem termwiseSurjective_simplicialCommGroup_kanFibration
    {X Y : SimplicialObject CommGrpCat.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ,
      Function.Surjective (f.app (op (SimplexCategory.mk n)))) :
    KanFibration (underlyingSimplicialGroupMap f) := by
  change HomotopicalAlgebra.Fibration (underlyingSimplicialGroupMap f)
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J,
    CategoryTheory.MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  refine ⟨fun {a} {b} sq => ?_⟩
  let aFace : ∀ (j : Fin (n + 2)) (_ : j ≠ k),
      X.obj (op (SimplexCategory.mk n)) := fun j hj =>
    SSet.yonedaEquiv (SSet.horn.ι k j hj ≫ a)
  let x : Y.obj (op (SimplexCategory.mk (n + 1))) :=
    SSet.yonedaEquiv b
  obtain ⟨x₀, hx₀⟩ := hf (n + 1) x
  have hfa : ∀ (j : Fin (n + 2)) (hj : j ≠ k),
      f.app (op (SimplexCategory.mk n)) (aFace j hj) = Y.δ j x := by
    intro j hj
    have h := congrArg SSet.yonedaEquiv
      (congrArg (fun g => SSet.horn.ι k j hj ≫ g) sq.w)
    simpa [aFace, x, SSet.yonedaEquiv_comp, underlyingSimplicialGroupMap,
      underlyingSimplicialGroup] using h
  have hδf : ∀ (j : Fin (n + 2)),
      f.app (op (SimplexCategory.mk n)) (X.δ j x₀) = Y.δ j x := by
    intro j
    have h := congrArg (fun g => g x₀) (X.δ_naturality f j)
    simpa [hx₀] using h
  let K := simplicialCommGroupKernel f
  let d : ∀ (j : Fin (n + 2)) (hj : j ≠ k), K.obj (op (SimplexCategory.mk n)) :=
    fun j hj => ⟨(X.δ j x₀)⁻¹ * aFace j hj, by
      rw [(f.app (op (SimplexCategory.mk n))).map_mul,
        (f.app (op (SimplexCategory.mk n))).map_inv, hδf, hfa]
      simp⟩
  let g : ∀ (j : Fin (n + 2)) (hj : j ≠ k),
      Δ[n] ⟶ underlyingSimplicialGroup K := fun j hj =>
    SSet.yonedaEquiv.symm (d j hj)
  have hA := SSet.horn.IsCompatible.of_hom a
  have hX := SSet.horn.IsCompatible.of_hom
    (SSet.yonedaEquiv.symm x₀ : Δ[n + 1] ⟶ underlyingSimplicialGroup X)
  have hg : SSet.horn.IsCompatible g := by
    intro j l hj hl hjl
    apply SSet.yonedaEquiv.injective
    apply Subtype.ext
    have hAjl := congrArg SSet.yonedaEquiv (hA.δ_pred_comp j l hj hl hjl)
    have hXjl := congrArg SSet.yonedaEquiv (hX.δ_pred_comp j l hj hl hjl)
    have hAjl' : X.δ (l.pred (Fin.ne_zero_of_lt hjl)) (aFace j hj) =
        X.δ (j.castPred (Fin.ne_last_of_lt hjl)) (aFace l hl) := by
      simpa [aFace, SSet.yonedaEquiv_comp, underlyingSimplicialGroup] using hAjl
    have hXjl' : X.δ (l.pred (Fin.ne_zero_of_lt hjl)) (X.δ j x₀) =
        X.δ (j.castPred (Fin.ne_last_of_lt hjl)) (X.δ l x₀) := by
      simpa [SSet.yonedaEquiv_comp, underlyingSimplicialGroup] using hXjl
    change X.δ (l.pred (Fin.ne_zero_of_lt hjl)) (d j hj) =
      X.δ (j.castPred (Fin.ne_last_of_lt hjl)) (d l hl)
    rw [(X.δ (l.pred (Fin.ne_zero_of_lt hjl))).map_mul,
      (X.δ (j.castPred (Fin.ne_last_of_lt hjl))).map_mul,
      hXjl', hAjl']
  obtain ⟨φ, hφ⟩ :=
    (SSet.KanComplex.iff.mp (simplicialGroup_kanComplex K)) g hg
  let z₀ : K.obj (op (SimplexCategory.mk (n + 1))) :=
    SSet.yonedaEquiv φ
  let z : X.obj (op (SimplexCategory.mk (n + 1))) :=
    x₀ * (simplicialCommGroupKernelι f).app
      (op (SimplexCategory.mk (n + 1))) z₀
  refine ⟨SSet.yonedaEquiv.symm z, ?_⟩
  constructor
  · apply horn.hom_ext'
    intro j hj
    apply SSet.yonedaEquiv.injective
    have hφj := congrArg SSet.yonedaEquiv (hφ j hj)
    change X.δ j z = aFace j hj
    rw [z, (X.δ j).map_mul]
    have hι : X.δ j ((simplicialCommGroupKernelι f).app
        (op (SimplexCategory.mk (n + 1))) z₀) =
        (simplicialCommGroupKernelι f).app
          (op (SimplexCategory.mk n)) (K.δ j z₀) := by
      have h := congrArg (fun g => g z₀) (X.δ_naturality
        (simplicialCommGroupKernelι f) j)
      simpa using h.symm
    rw [hι, ← hφj]
    change X.δ j x₀ * ((X.δ j x₀)⁻¹ * aFace j hj) = _
    simp
  · apply SSet.yonedaEquiv.injective
    change (f.app (op (SimplexCategory.mk (n + 1)))) z = x
    rw [z, (f.app (op (SimplexCategory.mk (n + 1)))).map_mul, hx₀]
    have hz₀ : (f.app (op (SimplexCategory.mk (n + 1))))
        ((simplicialCommGroupKernelι f).app
          (op (SimplexCategory.mk (n + 1))) z₀) = 1 := by
      exact z₀.property
    rw [hz₀]
    simp

private theorem simplicialAddCommGroupKernel_associated_acyclic
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ,
      Function.Surjective (f.app (op (SimplexCategory.mk n))))
    (hquasi : QuasiIso
      (Formalization.Books.Simplicial.Unit23.associatedChainComplexMap f)) :
    (Formalization.Books.Simplicial.Unit23.associatedChainComplex
      (simplicialAddCommGroupKernel f)).Acyclic := by
  let ι := simplicialAddCommGroupKernelι f
  let α := Formalization.Books.Simplicial.Unit23.associatedChainComplexMap ι
  let β := Formalization.Books.Simplicial.Unit23.associatedChainComplexMap f
  have hcomp : α ≫ β = 0 := by
    ext n
    apply AddCommGrpCat.ext
    intro x
    exact x.property
  let S : ShortComplex (ChainComplex AddCommGrpCat.{u}) :=
    ShortComplex.mk α β hcomp
  have hS : S.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact S
    intro n
    change (ShortComplex.mk (ι.app (op (SimplexCategory.mk n)))
      (f.app (op (SimplexCategory.mk n))) _) .ShortExact
    apply ShortComplex.ShortExact.mk'
    · rw [ShortComplex.exact_iff_epi_kernel_lift]
      let hzero : ι.app (op (SimplexCategory.mk n)) ≫
          f.app (op (SimplexCategory.mk n)) = 0 := by
        apply AddCommGrpCat.ext
        intro x
        exact x.property
      have hkernel : Limits.kernel.lift (f.app (op (SimplexCategory.mk n)))
          (ι.app (op (SimplexCategory.mk n))) hzero =
          (AddCommGrpCat.kernelIsoKer (f.app
            (op (SimplexCategory.mk n)))).inv := by
        apply (cancel_mono (Limits.kernel.ι
          (f.app (op (SimplexCategory.mk n))))).1
        rw [Limits.kernel.lift_ι, ← AddCommGrpCat.kernelIsoKer_inv_comp_ι]
      rw [hkernel]
      infer_instance
    · infer_instance
    · rw [AddCommGrpCat.epi_iff_surjective]
      exact hf n
  exact CategoryTheory.ShortComplex.ShortExact.acyclic_X₁ hS hquasi

private theorem simplicialAddCommGroupKernel_normalized_acyclic
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ,
      Function.Surjective (f.app (op (SimplexCategory.mk n))))
    (hquasi : QuasiIso
      (Formalization.Books.Simplicial.Unit23.associatedChainComplexMap f)) :
    (Formalization.Books.Simplicial.Unit23.normalizedChainComplex
      (simplicialAddCommGroupKernel f)).Acyclic := by
  have hA := simplicialAddCommGroupKernel_associated_acyclic f hf hquasi
  let e := Formalization.Books.Simplicial.Unit23.normalizedToAssociated
    (simplicialAddCommGroupKernel f)
  have he : QuasiIso e :=
    Formalization.Books.Simplicial.Unit23.normalized_to_associated_quasiIso _
  intro i
  exact (quasiIsoAt_iff_exactAt' e i (hA i)).1 (he.quasiIsoAt i)

private def addCommGrpToCommGrp : AddCommGrpCat.{u} ⥤ CommGrpCat.{u} where
  obj X := CommGrpCat.of (Multiplicative X)
  map f := CommGrpCat.ofHom f.hom.toMultiplicative
  map_id := by
    intro X
    apply CommGrpCat.ext
    intro x
    rfl
  map_comp := by
    intro X Y Z f g
    apply CommGrpCat.ext
    intro x
    rfl

private def additiveToMultiplicativeSimplicialObject
    (X : SimplicialObject AddCommGrpCat.{u}) :
    SimplicialObject CommGrpCat.{u} where
  obj n := CommGrpCat.of (Multiplicative (X.obj n))
  map α := CommGrpCat.ofHom
    { toFun := fun x => Multiplicative.ofAdd (X.map α (Multiplicative.toAdd x))
      map_one' := by
        ext
        simp
      map_mul' := by
        intro x y
        ext
        simp }
  map_id := by
    intro n
    apply CommGrpCat.ext
    intro x
    change Multiplicative.ofAdd (X.map (𝟙 n) (Multiplicative.toAdd x)) = x
    rw [X.map_id]
    rfl
  map_comp := by
    intro n m l α β
    apply CommGrpCat.ext
    intro x
    change Multiplicative.ofAdd (X.map (α ≫ β) (Multiplicative.toAdd x)) =
      Multiplicative.ofAdd (X.map β (X.map α (Multiplicative.toAdd x)))
    rw [X.map_comp]
    rfl

private theorem simplicialAddCommGroup_kanComplex
    (X : SimplicialObject AddCommGrpCat.{u}) :
    KanComplex (underlyingSimplicialAbelianGroup X) := by
  let X' := additiveToMultiplicativeSimplicialObject X
  let toAddX : ∀ n, X'.obj n → X.obj n := fun n x =>
    Multiplicative.toAdd (show Multiplicative (X.obj n) from x)
  apply SSet.KanComplex.iff.mpr
  intro n i f hf
  let g : ∀ (j : Fin (n + 2)) (_ : j ≠ i),
      Δ[n] ⟶ underlyingSimplicialGroup X' := fun j hj =>
    SSet.yonedaEquiv.symm
      (Multiplicative.ofAdd (SSet.yonedaEquiv (f j hj)))
  have hmapX : ∀ {m : ℕ} (j : Fin (m + 2))
      (x : X'.obj (op (SimplexCategory.mk (m + 1)))),
      toAddX (op (SimplexCategory.mk m))
          (X'.map (SimplexCategory.δ j).op x) =
        X.map (SimplexCategory.δ j).op
          (toAddX (op (SimplexCategory.mk (m + 1))) x) := by
    intro m j x
    rfl
  have hcomp : ∀ {m : ℕ} (j : Fin (m + 2))
      (p : Δ[m + 1] ⟶ underlyingSimplicialGroup X'),
      toAddX (op (SimplexCategory.mk m))
          (SSet.yonedaEquiv (SSet.stdSimplex.δ j ≫ p)) =
        X.δ j (toAddX (op (SimplexCategory.mk (m + 1)))
          (SSet.yonedaEquiv p)) := by
    intro m j p
    have hp : p = SSet.yonedaEquiv.symm (SSet.yonedaEquiv p) := by
      exact (SSet.yonedaEquiv.symm_apply_eq.mpr rfl).symm
    conv_lhs => rw [hp]
    change toAddX (op (SimplexCategory.mk m))
      (SSet.yonedaEquiv (SSet.stdSimplex.map (SimplexCategory.δ j) ≫
        SSet.yonedaEquiv.symm (SSet.yonedaEquiv p))) = _
    rw [SSet.yonedaEquiv_symm_naturality_left]
    rw [SSet.yonedaEquiv.apply_symm_apply]
    exact hmapX j _
  have hadd : ∀ {m : ℕ} (j : Fin (m + 2))
      (p : Δ[m + 1] ⟶ underlyingSimplicialAbelianGroup X),
      SSet.yonedaEquiv (SSet.stdSimplex.δ j ≫ p) =
        X.δ j (SSet.yonedaEquiv p) := by
    intro m j p
    have hp : p = SSet.yonedaEquiv.symm (SSet.yonedaEquiv p) := by
      exact (SSet.yonedaEquiv.symm_apply_eq.mpr rfl).symm
    conv_lhs => rw [hp]
    change SSet.yonedaEquiv
        (SSet.stdSimplex.map (SimplexCategory.δ j) ≫
          SSet.yonedaEquiv.symm (SSet.yonedaEquiv p)) = _
    rw [SSet.yonedaEquiv_symm_naturality_left]
    rw [SSet.yonedaEquiv.apply_symm_apply]
    change (underlyingSimplicialAbelianGroup X).map
        (SimplexCategory.δ j).op (SSet.yonedaEquiv p) = _
    rfl
  have hg : SSet.horn.IsCompatible g := by
    rcases n with _ | n
    · trivial
    · intro j l hj hl hjl
      apply SSet.yonedaEquiv.injective
      apply Multiplicative.ext
      have h := congrArg SSet.yonedaEquiv (hf.δ_pred_comp j l hj hl hjl)
      change Multiplicative.toAdd (SSet.yonedaEquiv
          (SSet.stdSimplex.δ (l.pred (Fin.ne_zero_of_lt hjl)) ≫ g j hj)) =
        Multiplicative.toAdd (SSet.yonedaEquiv
          (SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjl)) ≫ g l hl))
      have hgj : X.δ (l.pred (Fin.ne_zero_of_lt hjl))
          (toAddX (op (SimplexCategory.mk (n + 1)))
            (SSet.yonedaEquiv (g j hj))) =
          X.δ (l.pred (Fin.ne_zero_of_lt hjl)) (SSet.yonedaEquiv (f j hj)) := by
        have hgval : toAddX (op (SimplexCategory.mk (n + 1)))
            (SSet.yonedaEquiv (g j hj)) = SSet.yonedaEquiv (f j hj) := by
          dsimp [toAddX, g, X']
          exact congrArg Multiplicative.toAdd
            (SSet.yonedaEquiv.apply_symm_apply _)
        exact congrArg (X.δ _) hgval
      have hmid : X.δ (l.pred (Fin.ne_zero_of_lt hjl))
          (SSet.yonedaEquiv (f j hj)) =
          X.δ (j.castPred (Fin.ne_last_of_lt hjl))
            (SSet.yonedaEquiv (f l hl)) := by
        exact (hadd (m := n) (l.pred (Fin.ne_zero_of_lt hjl)) (f j hj)).symm.trans
          (h.trans
            (hadd (m := n) (j.castPred (Fin.ne_last_of_lt hjl)) (f l hl)))
      have hgl : X.δ (j.castPred (Fin.ne_last_of_lt hjl))
          (toAddX (op (SimplexCategory.mk (n + 1)))
            (SSet.yonedaEquiv (g l hl))) =
          X.δ (j.castPred (Fin.ne_last_of_lt hjl))
            (SSet.yonedaEquiv (f l hl)) := by
        have hgval : toAddX (op (SimplexCategory.mk (n + 1)))
            (SSet.yonedaEquiv (g l hl)) = SSet.yonedaEquiv (f l hl) := by
          dsimp [toAddX, g, X']
          exact congrArg Multiplicative.toAdd
            (SSet.yonedaEquiv.apply_symm_apply _)
        exact congrArg (X.δ _) hgval
      have hleft := hcomp (m := n)
        (l.pred (Fin.ne_zero_of_lt hjl)) (g j hj)
      have hright := hcomp (m := n)
        (j.castPred (Fin.ne_last_of_lt hjl)) (g l hl)
      exact hleft.trans (hgj.trans (hmid.trans (hgl.symm.trans hright.symm)))
  obtain ⟨φ, hφ⟩ :=
    (SSet.KanComplex.iff.mp (simplicialGroup_kanComplex X')) g hg
  let z : X.obj (op (SimplexCategory.mk (n + 1))) :=
    toAddX (op (SimplexCategory.mk (n + 1))) (SSet.yonedaEquiv φ)
  refine ⟨SSet.yonedaEquiv.symm z, ?_⟩
  intro j hj
  apply SSet.yonedaEquiv.injective
  have h := congrArg SSet.yonedaEquiv (hφ j hj)
  change X.δ j z = SSet.yonedaEquiv (f j hj)
  have hfirst : X.δ j z = toAddX (op (SimplexCategory.mk n)) (SSet.yonedaEquiv
      (SSet.stdSimplex.δ j ≫ φ)) := by
    simpa [z] using (hcomp (m := n) j φ).symm
  have hlast : toAddX (op (SimplexCategory.mk n))
      (SSet.yonedaEquiv (g j hj)) =
      SSet.yonedaEquiv (f j hj) := by
    dsimp [toAddX, g, X']
    exact congrArg Multiplicative.toAdd
      (SSet.yonedaEquiv.apply_symm_apply _)
  exact hfirst.trans ((congrArg (toAddX (op (SimplexCategory.mk n))) h).trans hlast)

private theorem termwiseSurjective_simplicialAddCommGroup_kanFibration
    {P Q : SimplicialObject AddCommGrpCat.{u}} (f : P ⟶ Q)
    (hf : ∀ n : ℕ,
      Function.Surjective (f.app (op (SimplexCategory.mk n)))) :
    KanFibration (underlyingSimplicialAbelianGroupMap f) := by
  change HomotopicalAlgebra.Fibration (underlyingSimplicialAbelianGroupMap f)
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J,
    CategoryTheory.MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  refine ⟨fun {a} {b} sq => ?_⟩
  let aFace : ∀ (j : Fin (n + 2)) (_ : j ≠ k),
      P.obj (op (SimplexCategory.mk n)) := fun j hj =>
    SSet.yonedaEquiv (SSet.horn.ι k j hj ≫ a)
  let x : Q.obj (op (SimplexCategory.mk (n + 1))) :=
    SSet.yonedaEquiv b
  obtain ⟨x₀, hx₀⟩ := hf (n + 1) x
  have hfa : ∀ (j : Fin (n + 2)) (hj : j ≠ k),
      f.app (op (SimplexCategory.mk n)) (aFace j hj) = Q.δ j x := by
    intro j hj
    have h := congrArg SSet.yonedaEquiv
      (congrArg (fun g => SSet.horn.ι k j hj ≫ g) sq.w)
    simpa [aFace, x, SSet.yonedaEquiv_comp,
      underlyingSimplicialAbelianGroupMap,
      underlyingSimplicialAbelianGroup] using h
  have hδf : ∀ (j : Fin (n + 2)),
      f.app (op (SimplexCategory.mk n)) (P.δ j x₀) = Q.δ j x := by
    intro j
    have h := congrArg (fun g => g x₀) (f.δ_naturality j)
    simpa [hx₀] using h
  let K := simplicialAddCommGroupKernel f
  let d : ∀ (j : Fin (n + 2)) (hj : j ≠ k),
      K.obj (op (SimplexCategory.mk n)) := fun j hj =>
    ⟨aFace j hj - P.δ j x₀, by
      rw [map_sub, hfa,
        hδf, sub_self]⟩
  let g : ∀ (j : Fin (n + 2)) (hj : j ≠ k),
      Δ[n] ⟶ underlyingSimplicialAbelianGroup K := fun j hj =>
    SSet.yonedaEquiv.symm (d j hj)
  have hA := SSet.horn.IsCompatible.of_hom a
  have hg : SSet.horn.IsCompatible g := by
    intro j l hj hl hjl
    apply SSet.yonedaEquiv.injective
    apply Subtype.ext
    have hAjl := congrArg SSet.yonedaEquiv (hA.δ_pred_comp j l hj hl hjl)
    have hAjl' : P.δ (l.pred (Fin.ne_zero_of_lt hjl)) (aFace j hj) =
        P.δ (j.castPred (Fin.ne_last_of_lt hjl)) (aFace l hl) := by
      simpa [aFace, SSet.yonedaEquiv_comp,
        underlyingSimplicialAbelianGroup] using hAjl
    have hXjl' : P.δ (l.pred (Fin.ne_zero_of_lt hjl)) (P.δ j x₀) =
        P.δ (j.castPred (Fin.ne_last_of_lt hjl)) (P.δ l x₀) := by
      have h := P.δ_comp_δ' (i := j) (j := l) (by omega)
      simpa [Category.assoc] using congrArg (fun g => g x₀) h
    change P.δ (l.pred (Fin.ne_zero_of_lt hjl)) (d j hj) =
      P.δ (j.castPred (Fin.ne_last_of_lt hjl)) (d l hl)
    rw [(P.δ (l.pred (Fin.ne_zero_of_lt hjl))).map_sub,
      (P.δ (j.castPred (Fin.ne_last_of_lt hjl))).map_sub,
      hXjl', hAjl']
  obtain ⟨φ, hφ⟩ :=
    (SSet.KanComplex.iff.mp (simplicialAddCommGroup_kanComplex K)) g hg
  let z₀ : K.obj (op (SimplexCategory.mk (n + 1))) :=
    SSet.yonedaEquiv φ
  let z : P.obj (op (SimplexCategory.mk (n + 1))) :=
    x₀ + (simplicialAddCommGroupKernelι f).app
      (op (SimplexCategory.mk (n + 1))) z₀
  refine ⟨SSet.yonedaEquiv.symm z, ?_⟩
  constructor
  · apply SSet.horn.hom_ext'
    intro j hj
    apply SSet.yonedaEquiv.injective
    have hφj := congrArg SSet.yonedaEquiv (hφ j hj)
    change P.δ j z = aFace j hj
    rw [z, (P.δ j).map_add]
    have hι : P.δ j ((simplicialAddCommGroupKernelι f).app
        (op (SimplexCategory.mk (n + 1))) z₀) =
        (simplicialAddCommGroupKernelι f).app
          (op (SimplexCategory.mk n)) (K.δ j z₀) := by
      have h := congrArg (fun g => g z₀)
        ((simplicialAddCommGroupKernelι f).δ_naturality j)
      simpa using h.symm
    rw [hι, ← hφj]
    change P.δ j x₀ + (aFace j hj - P.δ j x₀) = _
    abel
  · apply SSet.yonedaEquiv.injective
    change (f.app (op (SimplexCategory.mk (n + 1)))) z = x
    rw [z, (f.app (op (SimplexCategory.mk (n + 1)))).map_add, hx₀]
    have hz₀ : (f.app (op (SimplexCategory.mk (n + 1))))
        ((simplicialAddCommGroupKernelι f).app
          (op (SimplexCategory.mk (n + 1))) z₀) = 0 := by
      exact z₀.property
    rw [hz₀]
    simp

/- A termwise-surjective map of simplicial abelian groups is a Kan
fibration on underlying simplicial sets. -/
theorem termwiseSurjective_simplicialAbelianGroup_kanFibration
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ,
      Function.Surjective (f.app (op (SimplexCategory.mk n)))) :
    KanFibration (underlyingSimplicialAbelianGroupMap f) := by
  exact termwiseSurjective_simplicialAddCommGroup_kanFibration f hf

/-- A termwise-surjective quasi-isomorphism of simplicial abelian groups is a
trivial Kan fibration. -/
theorem termwiseSurjective_quasiIso_simplicialAbelianGroup_trivialKanFibration
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ,
      Function.Surjective (f.app (op (SimplexCategory.mk n))))
    (hquasi : QuasiIso
      (Formalization.Books.Simplicial.Unit23.associatedChainComplexMap f)) :
    Formalization.Books.Simplicial.Unit30.TrivialKanFibration
      (underlyingSimplicialAbelianGroupMap f) := by
  constructor
  · intro y
    obtain ⟨x, hx⟩ := hf 0 y
    refine ⟨(SSet.yonedaEquiv (X := underlyingSimplicialAbelianGroup X)).symm x, ?_⟩
    apply SSet.yonedaEquiv.injective
    simpa [underlyingSimplicialAbelianGroupMap,
      underlyingSimplicialAbelianGroup, SSet.yonedaEquiv_comp] using hx
  · intro n hn a b hab
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    let k : Fin (r + 2) := Fin.last (r + 1)
    have hhorn : SSet.horn (r + 1) k ≤ SSet.boundary (r + 1) := by
      rw [SSet.horn_eq_iSup]
      exact iSup_le fun j => SSet.face_singleton_compl_le_boundary j
    let h : (SSet.horn (r + 1) k : SSet) ⟶
        (SSet.boundary (r + 1) : SSet) := SSet.Subcomplex.homOfLE hhorn
    have hface : ∀ (j : Fin (r + 2)) (hj : j ≠ k),
        SSet.horn.ι k j hj ≫ h = SSet.boundary.ι j := by
      intro j hj
      apply (cancel_mono (SSet.boundary (r + 1)).ι).1
      simp [h, Category.assoc]
    let ah : (SSet.horn (r + 1) k : SSet) ⟶
        underlyingSimplicialAbelianGroup X := h ≫ a
    have hah : ah ≫ underlyingSimplicialAbelianGroupMap f =
        (SSet.horn (r + 1) k).ι ≫ b := by
      apply SSet.horn.hom_ext
      intro j hj
      calc
        (SSet.horn.ι k j hj ≫ ah) ≫
            underlyingSimplicialAbelianGroupMap f =
            (SSet.boundary.ι j ≫ a) ≫
              underlyingSimplicialAbelianGroupMap f := by
          simp only [ah, Category.assoc, hface]
        _ = SSet.boundary.ι j ≫ b := by
          rw [hab]
        _ = SSet.horn.ι k j hj ≫ b := by
          rw [← hface]
          simp
    have hfp := termwiseSurjective_simplicialAbelianGroup_kanFibration f hf
    change HomotopicalAlgebra.Fibration
      (underlyingSimplicialAbelianGroupMap f) at hfp
    have hrlp := (SSet.modelCategoryQuillen.fibration_iff _).1 hfp
    have hsq : HasLiftingProperty (SSet.horn (r + 1) k).ι
        (underlyingSimplicialAbelianGroupMap f) :=
      hrlp _ (SSet.modelCategoryQuillen.horn_ι_mem_J _ _)
    let sq : CommSq ah (SSet.horn (r + 1) k).ι
        (underlyingSimplicialAbelianGroupMap f) b := ⟨hah⟩
    obtain ⟨l, hl, hlf⟩ := (hsq.sq_hasLift sq).exists_lift.some
    let K := simplicialAddCommGroupKernel f
    let lval : X.obj (op (SimplexCategory.mk (r + 1))) :=
      SSet.yonedaEquiv l
    let aFace : ∀ j : Fin (r + 2),
        X.obj (op (SimplexCategory.mk r)) := fun j =>
      SSet.yonedaEquiv (SSet.boundary.ι j ≫ a)
    have hlval : f.app (op (SimplexCategory.mk (r + 1))) lval =
        SSet.yonedaEquiv b := by
      have h := congrArg SSet.yonedaEquiv hlf
      simpa [lval, SSet.yonedaEquiv_comp, underlyingSimplicialAbelianGroupMap,
        underlyingSimplicialAbelianGroup] using h
    have hfaceval : ∀ (j : Fin (r + 2)) (hj : j ≠ k),
        X.δ j lval = aFace j := by
      intro j hj
      have h := congrArg (fun g => SSet.horn.ι k j hj ≫ g) hl
      have h' := congrArg SSet.yonedaEquiv h
      simpa [lval, aFace, ah, hface, SSet.yonedaEquiv_comp,
        underlyingSimplicialAbelianGroup] using h'
    have hface_f : ∀ j : Fin (r + 2),
        f.app (op (SimplexCategory.mk r)) (aFace j) =
          Y.δ j (SSet.yonedaEquiv b) := by
      intro j
      have h := congrArg SSet.yonedaEquiv
        (congrArg (fun g => SSet.boundary.ι j ≫ g) hab)
      simpa [aFace, SSet.yonedaEquiv_comp, underlyingSimplicialAbelianGroupMap,
        underlyingSimplicialAbelianGroup] using h
    have hface_l : ∀ j : Fin (r + 2),
        f.app (op (SimplexCategory.mk r)) (X.δ j lval) =
          Y.δ j (SSet.yonedaEquiv b) := by
      intro j
      have h := congrArg (fun g => g lval) (X.δ_naturality f j)
      simpa [hlval] using h
    let q : K.obj (op (SimplexCategory.mk r)) :=
      ⟨aFace k - X.δ k lval, by
        rw [(f.app (op (SimplexCategory.mk r))).map_sub, hface_f,
          hface_l, sub_self]⟩
    have hqcycle : ∀ j : Fin r,
        K.δ (Fin.castSucc j) q = 0 := by
      intro j
      have hcompA : X.δ (Fin.last r) (aFace (Fin.castSucc j)) =
          X.δ (Fin.castSucc j) (aFace k) := by
        have h := congrArg SSet.yonedaEquiv
          (congrArg (fun g =>
            SSet.stdSimplex.δ (Fin.last r) ≫
              SSet.boundary.ι (Fin.castSucc j) ≫ g) (rfl : a = a))
        have h' : SSet.stdSimplex.δ (Fin.last r) ≫
              SSet.boundary.ι (Fin.castSucc j) ≫ a =
            SSet.stdSimplex.δ (Fin.castSucc j) ≫
              SSet.boundary.ι k ≫ a := by
          apply (cancel_mono (SSet.boundary (r + 1)).ι).1
          simp only [Category.assoc, SSet.boundary.ι_ι]
          exact SSet.stdSimplex.δ_comp_δ' (by omega)
        simpa [aFace, SSet.yonedaEquiv_comp] using
          congrArg SSet.yonedaEquiv h'
      have hcompL : X.δ (Fin.last r) (X.δ (Fin.castSucc j) lval) =
          X.δ (Fin.castSucc j) (X.δ k lval) := by
        have h := X.δ_comp_δ' (i := Fin.castSucc j) (j := k) (by omega)
        simpa [Category.assoc] using congrArg (fun g => g lval) h
      have hmatch := hfaceval (Fin.castSucc j) (by omega)
      change X.δ (Fin.castSucc j) (aFace k - X.δ k lval) = 0
      rw [(X.δ (Fin.castSucc j)).map_sub, ← hcompA, ← hcompL,
        (X.δ (Fin.last r)).map_sub, hmatch, sub_self]
    have hqLast : ∀ (s : ℕ), r = s + 1 →
        K.δ (Fin.last r) q = 0 := by
      intro s hrs
      subst r
      have hcompA : X.δ (Fin.last (s + 1))
            (aFace (Fin.castSucc (Fin.last s))) =
          X.δ (Fin.last s) (aFace k) := by
        have h' : SSet.stdSimplex.δ (Fin.last (s + 1)) ≫
              SSet.boundary.ι (Fin.castSucc (Fin.last s)) ≫ a =
            SSet.stdSimplex.δ (Fin.last s) ≫
              SSet.boundary.ι k ≫ a := by
          apply (cancel_mono (SSet.boundary (s + 2)).ι).1
          simp only [Category.assoc, SSet.boundary.ι_ι]
          exact SSet.stdSimplex.δ_comp_δ' (by omega)
        simpa [aFace, SSet.yonedaEquiv_comp] using
          congrArg SSet.yonedaEquiv h'
      have hcompL : X.δ (Fin.last (s + 1))
            (X.δ (Fin.castSucc (Fin.last s)) lval) =
          X.δ (Fin.last s) (X.δ k lval) := by
        have h := X.δ_comp_δ' (i := Fin.castSucc (Fin.last s))
          (j := k) (by omega)
        simpa [Category.assoc] using congrArg (fun g => g lval) h
      have hmatch := hfaceval (Fin.castSucc (Fin.last s)) (by omega)
      change X.δ (Fin.last (s + 1))
          (aFace k - X.δ k lval) = 0
      rw [(X.δ (Fin.last (s + 1))).map_sub, ← hcompA, ← hcompL,
        (X.δ (Fin.last s)).map_sub, hmatch, sub_self]
    let qmor : AddCommGrpCat.of (ULift ℤ) ⟶
        K.obj (op (SimplexCategory.mk r)) :=
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).symm q
    have hqfac : (normalizedSubobject K r).Factors qmor := by
      rcases r with _ | r
      · apply Subobject.top_factors
      · rw [normalizedSubobject]
        apply (Subobject.finset_inf_factors _).mpr
        intro j hj
        apply kernelSubobject_factors
        apply AddCommGrpCat.ext
        intro z
        apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
        simpa [qmor] using hqcycle j
    let qN : AddCommGrpCat.of (ULift ℤ) ⟶
        Formalization.Books.Simplicial.Unit23.normalizedObject K r :=
      (normalizedSubobject K r).factorThru qmor hqfac
    let N := Formalization.Books.Simplicial.Unit23.normalizedChainComplex K
    have hqN_arrow : qN ≫ (normalizedSubobject K r).arrow = qmor :=
      Subobject.factorThru_arrow _ _ _
    have hqNzero : qN ≫ (N.sc r).g = 0 := by
      rcases r with _ | r
      · simp [N, Formalization.Books.Simplicial.Unit23.normalizedChainComplex,
          Formalization.Books.Simplicial.Unit23.normalizedBoundary]
      · apply (cancel_mono (normalizedSubobject K r).arrow).1
        rw [Category.assoc, hqN_arrow]
        simp only [N, Formalization.Books.Simplicial.Unit23.normalizedChainComplex,
          Formalization.Books.Simplicial.Unit23.normalizedBoundary,
          Category.assoc, Preadditive.comp_zsmul, ← Preadditive.zsmul_comp,
          normalizedLastFace_arrow]
        rw [← Category.assoc, hqN_arrow]
        apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
        simpa [qmor] using hqLast r rfl
    let sign : ℤ := (-1 : ℤ) ^ (r + 1)
    let qN' : AddCommGrpCat.of (ULift ℤ) ⟶ N.X r := sign • qN
    have hqN'zero : qN' ≫ (N.sc r).g = 0 := by
      simp [qN', hqNzero, Preadditive.zsmul_comp]
    have hNacyc : N.Acyclic := by
      simpa [N] using simplicialAddCommGroupKernel_normalized_acyclic
        f hf hquasi
    have hE : Epi (Limits.kernel.lift (N.sc r).g (N.sc r).f
        (N.sc r).zero) :=
      (ShortComplex.exact_iff_epi_kernel_lift _).1 (hNacyc r)
    let qcycle : AddCommGrpCat.of (ULift ℤ) ⟶
        Limits.kernel (N.sc r).g :=
      Limits.kernel.lift (N.sc r).g qN' hqN'zero
    let qcycleVal :=
      AddCommGrpCat.uliftZMultiplesAddEquiv _ qcycle
    have hsurj : Function.Surjective
        (Limits.kernel.lift (N.sc r).g (N.sc r).f (N.sc r).zero).hom := by
      exact (AddCommGrpCat.epi_iff_surjective).1 hE
    obtain ⟨yval, hyval⟩ := hsurj qcycleVal
    let ymor : AddCommGrpCat.of (ULift ℤ) ⟶ N.X (r + 1) :=
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).symm yval
    have hymor : ymor ≫ Limits.kernel.lift (N.sc r).g
          (N.sc r).f (N.sc r).zero = qcycle := by
      apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
      simpa [ymor, qcycleVal] using hyval
    have hymor_d : ymor ≫ (N.sc r).f = qN' := by
      apply (cancel_mono (Limits.kernel.ι (N.sc r).g)).1
      rw [Category.assoc, Limits.kernel.lift_ι, hymor,
        Limits.kernel.lift_ι]
    have hsign : sign * sign = 1 := by
      simp [sign, ← pow_add]
    have hymor_last : ymor ≫
        (normalizedSubobject K (r + 1)).arrow ≫ K.δ (Fin.last (r + 1)) = qmor := by
      have h := congrArg (fun z => z ≫ (normalizedSubobject K r).arrow) hymor_d
      have h' : sign •
          (ymor ≫ (normalizedSubobject K (r + 1)).arrow ≫
            K.δ (Fin.last (r + 1))) = sign • qmor := by
        simpa [N, Formalization.Books.Simplicial.Unit23.normalizedChainComplex,
          Formalization.Books.Simplicial.Unit23.normalizedBoundary, qN',
          hqN_arrow, Category.assoc, Preadditive.comp_zsmul,
          Preadditive.zsmul_comp, normalizedLastFace_arrow] using h
      have h'' := congrArg (fun z => sign • z) h'
      simpa [smul_smul, hsign] using h''
    let yK : K.obj (op (SimplexCategory.mk (r + 1))) :=
      (normalizedSubobject K (r + 1)).arrow
        (AddCommGrpCat.uliftZMultiplesAddEquiv _ ymor)
    have hyFirst : ∀ (j : Fin (r + 1)),
        K.δ (Fin.castSucc j) yK = 0 := by
      intro j
      have hk : (normalizedSubobject K (r + 1)).arrow ≫
          K.δ (Fin.castSucc j) = 0 := by
        rw [← Subobject.factorThru_arrow
          (kernelSubobject (K.δ (Fin.castSucc j)))
          (normalizedSubobject K (r + 1)).arrow
          (Subobject.finset_inf_arrow_factors Finset.univ
            (fun i : Fin (r + 1) =>
              kernelSubobject (K.δ (Fin.castSucc i))) j (by simp))]
        simp only [Category.assoc, kernelSubobject_arrow_comp, zero_comp]
      have h := congrArg (fun g => g
          (AddCommGrpCat.uliftZMultiplesAddEquiv _ ymor)) hk
      simpa [yK] using h
    have hyLast : K.δ (Fin.last (r + 1)) yK = q := by
      apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
      simpa [yK, qmor] using hymor_last
    let yX : X.obj (op (SimplexCategory.mk (r + 1))) :=
      (simplicialAddCommGroupKernelι f).app
        (op (SimplexCategory.mk (r + 1))) yK
    let z : X.obj (op (SimplexCategory.mk (r + 1))) := lval + yX
    have hyX : f.app (op (SimplexCategory.mk (r + 1))) yX = 0 := by
      change f.app (op (SimplexCategory.mk (r + 1)))
          ((simplicialAddCommGroupKernelι f).app
            (op (SimplexCategory.mk (r + 1))) yK) = 0
      exact yK.property
    refine ⟨SSet.yonedaEquiv.symm z, ?_, ?_⟩
    · apply SSet.boundary.hom_ext
      intro j
      apply SSet.yonedaEquiv.injective
      by_cases hj : j = k
      · subst j
        have hι : X.δ k yX =
            (simplicialAddCommGroupKernelι f).app
              (op (SimplexCategory.mk r)) (K.δ k yK) := by
          have h := congrArg (fun g => g yK)
            (X.δ_naturality (simplicialAddCommGroupKernelι f) k)
          simpa using h.symm
        change X.δ k z = aFace k
        rw [z, (X.δ k).map_add, hι, hyLast, q]
        simp
      · obtain ⟨j', rfl⟩ := Fin.eq_castSucc_of_ne_last
          (by simpa [k] using hj)
        have hι : X.δ (Fin.castSucc j') yX =
            (simplicialAddCommGroupKernelι f).app
              (op (SimplexCategory.mk r))
              (K.δ (Fin.castSucc j') yK) := by
          have h := congrArg (fun g => g yK)
            (X.δ_naturality (simplicialAddCommGroupKernelι f)
              (Fin.castSucc j'))
          simpa using h.symm
        change X.δ (Fin.castSucc j') z = aFace (Fin.castSucc j')
        rw [z, (X.δ (Fin.castSucc j')).map_add, hι,
          hyFirst, hfaceval (Fin.castSucc j') (by omega)]
        simp
    · apply SSet.yonedaEquiv.injective
      have h := congrArg SSet.yonedaEquiv hlf
      simpa [z, hyX, SSet.yonedaEquiv_comp,
        underlyingSimplicialAbelianGroupMap, underlyingSimplicialAbelianGroup]
        using h

/-- A homotopy equivalence of the underlying simplicial sets of simplicial
abelian groups induces a quasi-isomorphism on the associated chain complexes. -/
theorem homotopyEquivalence_simplicialAbelianGroup_quasiIso
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : Formalization.Books.Simplicial.Unit26.IsHomotopyEquivalence
      (underlyingSimplicialAbelianGroupMap f)) :
    QuasiIso
      (Formalization.Books.Simplicial.Unit23.associatedChainComplexMap f) := by
  exact HomologicalComplex.homotopyEquivalences_le_quasiIso _ _ _
    (Formalization.Books.Simplicial.Unit27.additiveAssociatedChainMap_homotopyEquivalence
      hf)

end Formalization.Books.Simplicial.Unit31
