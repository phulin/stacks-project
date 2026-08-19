import Formalization.Books.Simplicial.Unit30
import Formalization.Books.Simplicial.Unit23.SimplicialObjectsAndChainComplexes
import Mathlib.Algebra.Category.Grp.Basic
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
    KanFibration (pullback.fst f g) := by
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

/-- Every simplicial group is a Kan complex. -/
theorem simplicialGroup_kanComplex
    (X : SimplicialObject CommGrpCat.{u}) :
    KanComplex (underlyingSimplicialGroup X) := by
  sorry

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

/-- A termwise-surjective map of simplicial abelian groups is a Kan
fibration on underlying simplicial sets. -/
theorem termwiseSurjective_simplicialAbelianGroup_kanFibration
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : ∀ n : ℕ,
      Function.Surjective (f.app (op (SimplexCategory.mk n)))) :
    KanFibration (underlyingSimplicialAbelianGroupMap f) := by
  sorry

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
  sorry

/-- A homotopy equivalence of the underlying simplicial sets of simplicial
abelian groups induces a quasi-isomorphism on the associated chain complexes. -/
theorem homotopyEquivalence_simplicialAbelianGroup_quasiIso
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hf : Formalization.Books.Simplicial.Unit26.IsHomotopyEquivalence
      (underlyingSimplicialAbelianGroupMap f)) :
    QuasiIso
      (Formalization.Books.Simplicial.Unit23.associatedChainComplexMap f) := by
  sorry

end Formalization.Books.Simplicial.Unit31
