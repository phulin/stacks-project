import Formalization.Books.Categories.Unit10.Equalizers
import Mathlib.CategoryTheory.Comma.CardinalArrow
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.PathCategory.MorphismProperty
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.EquivFin

/-!
# Categories, Chapter 18: Finite limits and colimits

The source's adjectives “finite”, “nonempty”, and “connected” refer to the
index category.  We use Mathlib's canonical `FinCategory`, `Nonempty`, and
`IsConnected` interfaces directly; no parallel predicates for those index
properties are introduced.  The existence statements below package the
corresponding quantification over finite index categories.
-/

namespace Formalization.Books.Categories.Unit18

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe u v u' v'

noncomputable section

section FiniteDiagramReduction

variable {I : Type u} [Category.{v} I]

/- A finite family of arrows is represented by a finite set in the arrow
   category.  `MorphismProperty.paths` then records exactly the source's
   assertion that every arrow is a composition of members of that family. -/
def HasFiniteGeneratingMorphisms : Prop :=
  ∃ S : Set (Arrow I), S.Finite ∧
    ∀ {X Y : I} (f : X ⟶ Y),
      ∃ p : Quiver.Path X Y,
        (let W : MorphismProperty I := fun _ _ g => Arrow.mk g ∈ S
         W.paths p) ∧ CategoryTheory.composePath p = f

/- Mathlib's `Arrow.finite_iff` is the canonical equivalence between the
   source's “finitely many objects and morphisms” wording and `FinCategory`. -/
theorem finite_index_category_iff {J : Type u} [SmallCategory J] :
    Finite (Arrow J) ↔ Nonempty (FinCategory J) :=
  Arrow.finite_iff J

/- The source's finite replacement is packaged as data so that its finiteness,
   preservation, and connectedness/nonemptiness comparisons remain usable by
   later users.  `Initial` and `Final` are Mathlib's canonical interfaces for
   the limit and colimit preservation asserted by the source. -/
structure FiniteDiagramReplacement (I : Type u) [Category.{v} I] where
  J : Type
  category : SmallCategory J
  finite : @FinCategory J category
  F : @CategoryTheory.Functor J category I (inferInstance : Category.{v} I)
  initial : @Functor.Initial J category I (inferInstance : Category.{v} I) F
  final : @Functor.Final J category I (inferInstance : Category.{v} I) F
  connected_iff : @IsConnected J category ↔ IsConnected I
  nonempty_iff : Nonempty J ↔ Nonempty I

attribute [instance] FiniteDiagramReplacement.category
attribute [instance] FiniteDiagramReplacement.finite
attribute [instance] FiniteDiagramReplacement.initial
attribute [instance] FiniteDiagramReplacement.final

private abbrev finiteBipartiteTag (α β : Type) := Sum (Sum (Sum α α) β) α

private def finiteBipartiteHom {α β : Type} (src tgt : β → α)
    (X Y : Sum α α) : Type :=
  PLift (X = Y) ⊕
    {b : β // X = Sum.inl (src b) ∧ Y = Sum.inr (tgt b)} ⊕
    {a : α // X = Sum.inl a ∧ Y = Sum.inr a}

private def finiteBipartiteHomComp {α β : Type} {src tgt : β → α} {X Y Z : Sum α α}
    (f : finiteBipartiteHom src tgt X Y) (g : finiteBipartiteHom src tgt Y Z) :
      finiteBipartiteHom src tgt X Z := by
  rcases f with hf | f
  · rcases hf with ⟨hf⟩
    cases hf
    exact g
  · rcases f with f | f
    · rcases f with ⟨b, hbX, hbY⟩
      rcases g with hg | g
      · rcases hg with ⟨hg⟩
        cases hg
        exact .inr (.inl ⟨b, hbX, hbY⟩)
      · rcases g with g | g
        · rcases g with ⟨c, hcY, hcZ⟩
          have h : (Sum.inr (tgt b) : Sum α α) = Sum.inl (src c) :=
            hbY.symm.trans hcY
          cases h
        · rcases g with ⟨c, hcY, hcZ⟩
          have h : (Sum.inr (tgt b) : Sum α α) = Sum.inl c :=
            hbY.symm.trans hcY
          cases h
    · rcases f with ⟨a, haX, haY⟩
      rcases g with hg | g
      · rcases hg with ⟨hg⟩
        cases hg
        exact .inr (.inr ⟨a, haX, haY⟩)
      · rcases g with g | g
        · rcases g with ⟨c, hcY, hcZ⟩
          have h : (Sum.inr a : Sum α α) = Sum.inl (src c) :=
            haY.symm.trans hcY
          cases h
        · rcases g with ⟨c, hcY, hcZ⟩
          have h : (Sum.inr a : Sum α α) = Sum.inl c :=
            haY.symm.trans hcY
          cases h

private def finiteBipartiteCategory {α β : Type} (src tgt : β → α) :
    Category (Sum α α) where
  Hom := finiteBipartiteHom src tgt
  id := fun X => .inl ⟨rfl⟩
  comp := finiteBipartiteHomComp
  id_comp := by
    intro X Y f
    rcases f with hf | f
    · rcases hf with ⟨hf⟩
      cases hf
      rfl
    · rcases f with f | f
      · rcases f with ⟨b, hbX, hbY⟩
        rfl
      · rcases f with ⟨a, haX, haY⟩
        rfl
  comp_id := by
    intro X Y f
    rcases f with hf | f
    · rcases hf with ⟨hf⟩
      cases hf
      rfl
    · rcases f with f | f
      · rcases f with ⟨b, hbX, hbY⟩
        rfl
      · rcases f with ⟨a, haX, haY⟩
        rfl
  assoc := by
    intro W X Y Z f g h
    rcases f with hf | f
    · rcases hf with ⟨hf⟩
      cases hf
      rfl
    · rcases f with f | f
      · rcases f with ⟨b, hbW, hbX⟩
        rcases g with hg | g
        · rcases hg with ⟨hg⟩
          cases hg
          rcases h with hh | h
          · rcases hh with ⟨hh⟩
            cases hh
            rfl
          · rcases h with h | h
            · rcases h with ⟨c, hcY, hcZ⟩
              have contra : (Sum.inr (tgt b) : Sum α α) = Sum.inl (src c) :=
                hbX.symm.trans hcY
              cases contra
            · rcases h with ⟨c, hcY, hcZ⟩
              have contra : (Sum.inr (tgt b) : Sum α α) = Sum.inl c :=
                hbX.symm.trans hcY
              cases contra
        · rcases g with g | g
          · rcases g with ⟨c, hcX, hcY⟩
            have contra : (Sum.inr (tgt b) : Sum α α) = Sum.inl (src c) :=
              hbX.symm.trans hcX
            cases contra
          · rcases g with ⟨c, hcX, hcY⟩
            have contra : (Sum.inr (tgt b) : Sum α α) = Sum.inl c :=
              hbX.symm.trans hcX
            cases contra
      · rcases f with ⟨a, haW, haX⟩
        rcases g with hg | g
        · rcases hg with ⟨hg⟩
          cases hg
          rcases h with hh | h
          · rcases hh with ⟨hh⟩
            cases hh
            rfl
          · rcases h with h | h
            · rcases h with ⟨c, hcY, hcZ⟩
              have contra : (Sum.inr a : Sum α α) = Sum.inl (src c) :=
                haX.symm.trans hcY
              cases contra
            · rcases h with ⟨c, hcY, hcZ⟩
              have contra : (Sum.inr a : Sum α α) = Sum.inl c :=
                haX.symm.trans hcY
              cases contra
        · rcases g with g | g
          · rcases g with ⟨c, hcX, hcY⟩
            have contra : (Sum.inr a : Sum α α) = Sum.inl (src c) :=
              haX.symm.trans hcX
            cases contra
          · rcases g with ⟨c, hcX, hcY⟩
            have contra : (Sum.inr a : Sum α α) = Sum.inl c :=
              haX.symm.trans hcX
            cases contra

private instance finiteBipartiteHom_finite {α β : Type} [Finite α] [Finite β]
    (src tgt : β → α) (X Y : Sum α α) :
    Finite (finiteBipartiteHom src tgt X Y) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype β := Fintype.ofFinite β
  change Finite (PLift (X = Y) ⊕
    {b : β // X = Sum.inl (src b) ∧ Y = Sum.inr (tgt b)} ⊕
      {a : α // X = Sum.inl a ∧ Y = Sum.inr a})
  infer_instance

private theorem finiteBipartiteCategory_finite {α β : Type} [Finite α] [Finite β]
    (src tgt : β → α) :
    Nonempty (@FinCategory (Sum α α) (finiteBipartiteCategory src tgt)) := by
  let _ : Category (Sum α α) := finiteBipartiteCategory src tgt
  letI : ∀ X Y : Sum α α, Fintype (X ⟶ Y) :=
    fun X Y => Fintype.ofFinite (finiteBipartiteHom src tgt X Y)
  apply (finite_index_category_iff (J := Sum α α)).mp
  exact Finite.of_equiv _ (Arrow.equivSigma (Sum α α)).symm

/- The first source lemma: a finite object set together with finitely many
   generating arrows admits a finite replacement with the same (co)limits. -/
theorem finite_diagram_category [Finite I] (hI : HasFiniteGeneratingMorphisms (I := I)) :
    Nonempty (FiniteDiagramReplacement I) := by
  rcases hI with ⟨S, hS, hgen⟩
  let β := S
  letI : Finite β := Set.finite_coe_iff.mpr hS
  rcases Finite.exists_equiv_fin I with ⟨n, ⟨eI⟩⟩
  rcases Finite.exists_equiv_fin β with ⟨m, ⟨eS⟩⟩
  let src : Fin m → Fin n := fun j => eI (eS.symm j).1.left
  let tgt : Fin m → Fin n := fun j => eI (eS.symm j).1.right
  let J := Sum (Fin n) (Fin n)
  let catJ : SmallCategory J := finiteBipartiteCategory src tgt
  letI : SmallCategory J := catJ
  let tag : J → Fin n := Sum.elim id id
  let obj : J → I := fun X => eI.symm (tag X)
  let map : ∀ {X Y : J}, (X ⟶ Y) → (obj X ⟶ obj Y) := by
    intro X Y f
    rcases f with f | f
    · exact eqToHom (congrArg obj f.down)
    · rcases f with f | f
      · rcases f with ⟨j, hX, hY⟩
        have hX' : obj X = (eS.symm j).1.left := by
          simpa [obj, tag, src] using congrArg obj hX
        have hY' : obj Y = (eS.symm j).1.right := by
          simpa [obj, tag, tgt] using congrArg obj hY
        exact eqToHom hX' ≫ (eS.symm j).1.hom ≫ eqToHom hY'.symm
      · rcases f with ⟨i, hX, hY⟩
        have hX' : obj X = eI.symm i := by
          simpa [obj, tag] using congrArg obj hX
        have hY' : obj Y = eI.symm i := by
          simpa [obj, tag] using congrArg obj hY
        exact eqToHom hX' ≫ 𝟙 _ ≫ eqToHom hY'.symm
  let F : J ⥤ I :=
    { obj := obj
      map := @map
      map_id := by
        intro X
        rcases X with i | i
        · change eqToHom (congrArg obj (rfl : (Sum.inl i : J) = Sum.inl i)) =
            𝟙 (obj (Sum.inl i))
          simp
        · change eqToHom (congrArg obj (rfl : (Sum.inr i : J) = Sum.inr i)) =
            𝟙 (obj (Sum.inr i))
          simp
      map_comp := by
        intro X Y Z f g
        change map (finiteBipartiteHomComp f g) = map f ≫ map g
        rcases f with f | f
        · rcases f with ⟨f⟩
          cases f
          simp [map, obj, tag, finiteBipartiteHomComp]
        · rcases f with f | f
          · rcases f with ⟨j, hX, hY⟩
            rcases g with g | g
            · rcases g with ⟨g⟩
              cases g
              simp [map, obj, tag, finiteBipartiteHomComp]
            · rcases g with g | g
              · rcases g with ⟨k, hY', hZ⟩
                have h : (Sum.inr (tgt j) : J) = Sum.inl (src k) :=
                  hY.symm.trans hY'
                cases h
              · rcases g with ⟨k, hY', hZ⟩
                have h : (Sum.inr (tgt j) : J) = Sum.inl k :=
                  hY.symm.trans hY'
                cases h
          · rcases f with ⟨i, hX, hY⟩
            rcases g with g | g
            · rcases g with ⟨g⟩
              cases g
              simp [map, obj, tag, finiteBipartiteHomComp]
            · rcases g with g | g
              · rcases g with ⟨k, hY', hZ⟩
                have h : (Sum.inr i : J) = Sum.inl (src k) :=
                  hY.symm.trans hY'
                cases h
              · rcases g with ⟨k, hY', hZ⟩
                have h : (Sum.inr i : J) = Sum.inl k :=
                  hY.symm.trans hY'
                cases h }
  let W : MorphismProperty I := fun _ _ g => Arrow.mk g ∈ S
  have hgen' : ∀ {X Y : I} (f : X ⟶ Y),
      ∃ p : Quiver.Path X Y, W.paths p ∧ CategoryTheory.composePath p = f := by
    intro X Y f
    simpa [W] using hgen f
  let transport : ∀ {X Y : I}, (X ⟶ Y) →
      (obj (Sum.inr (eI X)) ⟶ obj (Sum.inr (eI Y))) := by
    intro X Y f
    exact eqToHom (eI.symm_apply_apply X) ≫ f ≫
      eqToHom (eI.symm_apply_apply Y).symm
  let bridge (X : I) : (Sum.inl (eI X) : J) ⟶ Sum.inr (eI X) :=
    .inr (.inr ⟨eI X, rfl, rfl⟩)
  let genEdge : ∀ {X Y : I} (f : X ⟶ Y), W f →
      ((Sum.inl (eI X) : J) ⟶ Sum.inr (eI Y)) := by
    intro X Y f hf
    let b : β := ⟨Arrow.mk f, by simpa [W] using hf⟩
    let j : Fin m := eS b
    exact .inr (.inl ⟨j, by simp [src, j, b], by simp [tgt, j, b]⟩)
  have map_bridge : ∀ (X : I), F.map (bridge X) = 𝟙 (obj (Sum.inr (eI X))) := by
    intro X
    change eqToHom (rfl : eI.symm (eI X) = eI.symm (eI X)) ≫
        𝟙 (eI.symm (eI X)) ≫
        eqToHom (rfl : eI.symm (eI X) = eI.symm (eI X)) =
      𝟙 (eI.symm (eI X))
    simp
  have map_genEdge : ∀ {X Y : I} (f : X ⟶ Y) (hf : W f),
      F.map (genEdge f hf) = transport f := by
    have map_edge : ∀ {X Y : J} (j : Fin m)
        (hX : X = Sum.inl (src j)) (hY : Y = Sum.inr (tgt j)),
        F.map (.inr (.inl ⟨j, hX, hY⟩)) =
          (let hX' : obj X = (eS.symm j).1.left := by
             simpa [obj, tag, src] using congrArg obj hX
           let hY' : obj Y = (eS.symm j).1.right := by
             simpa [obj, tag, tgt] using congrArg obj hY
           eqToHom hX' ≫ (eS.symm j).1.hom ≫ eqToHom hY'.symm) := by
      intro X Y j hX hY
      rfl
    have map_edge' : ∀ {X Y : J} (j : Fin m)
        (hX : X = Sum.inl (src j)) (hY : Y = Sum.inr (tgt j))
        (hX' : obj X = (eS.symm j).1.left)
        (hY' : obj Y = (eS.symm j).1.right),
        F.map (.inr (.inl ⟨j, hX, hY⟩)) =
          eqToHom hX' ≫ (eS.symm j).1.hom ≫ eqToHom hY'.symm := by
      intro X Y j hX hY hX' hY'
      apply Eq.trans (map_edge j hX hY)
      simp
    have hom_transport : ∀ (a : β) (j : Fin m) (h : eS.symm j = a),
        (eS.symm j).1.hom =
          eqToHom (congrArg (fun q : β => q.1.left) h) ≫ a.1.hom ≫
            eqToHom (congrArg (fun q : β => q.1.right) h).symm := by
      intro a j h
      cases h
      simp
    intro X Y f hf
    let b : β := ⟨Arrow.mk f, by simpa [W] using hf⟩
    let j : Fin m := eS b
    have hX : (Sum.inl (eI X) : J) = Sum.inl (src j) := by
      simp [src, j, b]
    have hY : (Sum.inr (eI Y) : J) = Sum.inr (tgt j) := by
      simp [tgt, j, b]
    have hedge : genEdge f hf = .inr (.inl ⟨j, hX, hY⟩) := by
      dsimp [genEdge, b, j]
    have hleft : (eS.symm j).1.left = X := by
      dsimp [j]
      exact (congrArg (fun q : β => q.1.left)
        (eS.symm_apply_apply b)).trans (by rfl)
    have hright : (eS.symm j).1.right = Y := by
      dsimp [j]
      exact (congrArg (fun q : β => q.1.right)
        (eS.symm_apply_apply b)).trans (by rfl)
    have hIX : obj (Sum.inl (eI X)) = X := by
      simpa [obj, tag] using eI.symm_apply_apply X
    have hIY : obj (Sum.inr (eI Y)) = Y := by
      simpa [obj, tag] using eI.symm_apply_apply Y
    have hXcan : obj (Sum.inl (eI X)) = (eS.symm j).1.left :=
      hIX.trans hleft.symm
    have hYcan : obj (Sum.inr (eI Y)) = (eS.symm j).1.right :=
      hIY.trans hright.symm
    have hsub : eS.symm j = b := by
      dsimp [j]
      exact eS.symm_apply_apply b
    have hmid := hom_transport b j hsub
    rw [hedge, map_edge' j hX hY hXcan hYcan, hmid]
    simp only [Category.assoc]
    change eqToHom hXcan ≫
        eqToHom (congrArg (fun q : β => q.1.left) hsub) ≫ b.1.hom ≫
          eqToHom (congrArg (fun q : β => q.1.right) hsub).symm ≫
            eqToHom hYcan.symm =
      eqToHom (eI.symm_apply_apply X) ≫ f ≫
        eqToHom (eI.symm_apply_apply Y).symm
    have hx : eqToHom hXcan ≫
        eqToHom (congrArg (fun q : β => q.1.left) hsub) =
          eqToHom (eI.symm_apply_apply X) := by
      rw [eqToHom_trans]
      apply congrArg eqToHom
      apply Subsingleton.elim
    have hy : eqToHom (congrArg (fun q : β => q.1.right) hsub).symm ≫
        eqToHom hYcan.symm = eqToHom (eI.symm_apply_apply Y).symm := by
      rw [eqToHom_trans]
      apply congrArg eqToHom
      apply Subsingleton.elim
    have hcat :
        (eqToHom hXcan ≫
          eqToHom (congrArg (fun q : β => q.1.left) hsub)) ≫
            (b.1.hom ≫
              (eqToHom (congrArg (fun q : β => q.1.right) hsub).symm ≫
                eqToHom hYcan.symm)) =
          eqToHom (eI.symm_apply_apply X) ≫
            (b.1.hom ≫ eqToHom (eI.symm_apply_apply Y).symm) := by
      rw [hx, hy]
      rfl
    have hb : b.1.hom = f := by rfl
    simpa only [Category.assoc, hb] using hcat
  have lift_path : ∀ {X Y : I} (p : Quiver.Path X Y),
      W.paths p → Zigzag (Sum.inr (eI X) : J) (Sum.inr (eI Y) : J) := by
    intro X Y p hp
    induction p with
    | nil => exact Zigzag.refl _
    | @cons Y Z p f ih =>
      rcases hp with ⟨hp, hf⟩
      have ih' := ih hp
      let b : β := ⟨Arrow.mk f, hf⟩
      let j : Fin m := eS b
      let bridge : (Sum.inl (eI Y) : J) ⟶ Sum.inr (eI Y) :=
        .inr (.inr ⟨eI Y, rfl, rfl⟩)
      let edge : (Sum.inl (eI Y) : J) ⟶ Sum.inr (eI Z) :=
        .inr (.inl ⟨j, by simp [src, j, b], by simp [tgt, j, b]⟩)
      exact ih'.trans ((Zigzag.of_inv bridge).trans (Zigzag.of_hom edge))
  let finiteJ : @FinCategory J catJ :=
    Classical.choice (finiteBipartiteCategory_finite src tgt)
  refine ⟨J, catJ, finiteJ, F, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun T => ?_⟩
    let base : CostructuredArrow F T :=
      CostructuredArrow.mk (S := F) (Y := (Sum.inr (eI T) : J))
        (eqToHom (eI.symm_apply_apply T))
    have lift_path_costr : ∀ {X Z : I} (p : Quiver.Path X Z),
        W.paths p → ∀ q : Z ⟶ T,
          Zigzag
            (CostructuredArrow.mk (S := F) (Y := (Sum.inr (eI X) : J))
              (eqToHom (eI.symm_apply_apply X) ≫
                CategoryTheory.composePath p ≫ q))
            (CostructuredArrow.mk (S := F) (Y := (Sum.inr (eI Z) : J))
              (eqToHom (eI.symm_apply_apply Z) ≫ q)) := by
      intro X Z p hp
      induction p with
      | nil =>
          intro q
          simpa using
            (Zigzag.refl
              (CostructuredArrow.mk (S := F) (Y := (Sum.inr (eI X) : J))
                (eqToHom (eI.symm_apply_apply X) ≫ q)))
      | @cons Y Z p f ih =>
          intro q
          rcases hp with ⟨hp, hf⟩
          have ih' := ih hp (f ≫ q)
          let bca : CostructuredArrow F T :=
            CostructuredArrow.mk (S := F) (Y := (Sum.inr (eI Y) : J))
              (eqToHom (eI.symm_apply_apply Y) ≫ f ≫ q)
          let eca : CostructuredArrow F T :=
            CostructuredArrow.mk (S := F) (Y := (Sum.inr (eI Z) : J))
              (eqToHom (eI.symm_apply_apply Z) ≫ q)
          let bridge' : (Sum.inl (eI Y) : J) ⟶ Sum.inr (eI Y) :=
            bridge Y
          let edge' : (Sum.inl (eI Y) : J) ⟶ Sum.inr (eI Z) :=
            genEdge f hf
          have hbca :
              CostructuredArrow.mk (S := F) (Y := (Sum.inl (eI Y) : J))
                  (eqToHom (eI.symm_apply_apply Y) ≫ f ≫ q) ⟶
                CostructuredArrow.mk (S := F) (Y := (Sum.inr (eI Y) : J))
                  (eqToHom (eI.symm_apply_apply Y) ≫ f ≫ q) :=
            CostructuredArrow.homMk bridge' (by
              have hbridge : F.map bridge' =
                  𝟙 (F.obj (Sum.inl (eI Y))) := by
                change eqToHom
                    (rfl : eI.symm (eI Y) = eI.symm (eI Y)) ≫
                    𝟙 (eI.symm (eI Y)) ≫
                    eqToHom
                      (rfl : eI.symm (eI Y) = eI.symm (eI Y)) =
                  𝟙 (eI.symm (eI Y))
                simp
              rw [hbridge]
              change 𝟙 (eI.symm (eI Y)) ≫
                  (eqToHom (eI.symm_apply_apply Y) ≫ f ≫ q) =
                eqToHom (eI.symm_apply_apply Y) ≫ f ≫ q
              simp)
          have heca :
              CostructuredArrow.mk (S := F) (Y := (Sum.inl (eI Y) : J))
                  (eqToHom (eI.symm_apply_apply Y) ≫ f ≫ q) ⟶ eca :=
            CostructuredArrow.homMk edge' (by
              change F.map (genEdge f hf) ≫ eca.hom = bca.hom
              rw [map_genEdge]
              have htransport : transport f ≫
                    eqToHom (eI.symm_apply_apply Z) =
                  eqToHom (eI.symm_apply_apply Y) ≫ f := by
                change
                  (eqToHom (eI.symm_apply_apply Y) ≫ f ≫
                    eqToHom (eI.symm_apply_apply Z).symm) ≫
                      eqToHom (eI.symm_apply_apply Z) =
                    eqToHom (eI.symm_apply_apply Y) ≫ f
                simp only [Category.assoc, eqToHom_trans, eqToHom_refl,
                  Category.id_comp, Category.comp_id]
              change transport f ≫
                  (eqToHom (eI.symm_apply_apply Z) ≫ q) =
                eqToHom (eI.symm_apply_apply Y) ≫ f ≫ q
              rw [← Category.assoc, htransport]
              exact Category.assoc _ _ _)
          simpa [eca, composePath_cons] using
            ih'.trans ((Zigzag.of_inv hbca).trans (Zigzag.of_hom heca))
    have inr_to_base : ∀ (i : Fin n) (a : F.obj (Sum.inr i) ⟶ T),
        Zigzag (CostructuredArrow.mk (S := F) (Y := (Sum.inr i : J)) a) base := by
      intro i a
      let X : I := eI.symm i
      let h : (Sum.inr (eI X) : J) = Sum.inr i :=
        congrArg Sum.inr (eI.apply_symm_apply i)
      let c0 : CostructuredArrow F T :=
        CostructuredArrow.mk (S := F) (Y := (Sum.inr (eI X) : J))
          (eqToHom (eI.symm_apply_apply X) ≫ a)
      have hc0 : c0 ⟶ CostructuredArrow.mk (S := F) (Y := (Sum.inr i : J)) a :=
        CostructuredArrow.homMk (eqToHom h) (by
          change F.map (eqToHom h) ≫ a =
            eqToHom (eI.symm_apply_apply X) ≫ a
          have hmap : F.map (eqToHom h) =
              eqToHom (eI.symm_apply_apply X) := by
            rw [eqToHom_map]
            apply congrArg eqToHom
            apply Subsingleton.elim
          rw [hmap]
          congr 1)
      rcases hgen' a with ⟨p, hp, hcomp⟩
      have hz := lift_path_costr p hp (𝟙 T)
      have hz' : Zigzag c0 base := by
        rw [hcomp] at hz
        have hstart :
            CostructuredArrow.mk (S := F) (Y := (Sum.inr (eI X) : J))
                (eqToHom (eI.symm_apply_apply X) ≫ a ≫ 𝟙 T) ⟶ c0 :=
          CostructuredArrow.homMk (𝟙 (Sum.inr (eI X))) (by
            change F.map (𝟙 (Sum.inr (eI X))) ≫ c0.hom =
              eqToHom (eI.symm_apply_apply X) ≫ a ≫ 𝟙 T
            rw [F.map_id]
            simp only [c0, CostructuredArrow.mk_hom_eq_self, Category.id_comp]
            exact congrArg
              (fun f => eqToHom (eI.symm_apply_apply X) ≫ f)
              (Category.comp_id a).symm)
        have hend :
            CostructuredArrow.mk (S := F) (Y := (Sum.inr (eI T) : J))
                (eqToHom (eI.symm_apply_apply T) ≫ 𝟙 T) ⟶ base :=
          CostructuredArrow.homMk (𝟙 (Sum.inr (eI T))) (by
            change F.map (𝟙 (Sum.inr (eI T))) ≫ base.hom =
              eqToHom (eI.symm_apply_apply T) ≫ 𝟙 T
            rw [F.map_id]
            simp only [base, CostructuredArrow.mk_hom_eq_self, Category.id_comp,
              Category.comp_id]
            change eqToHom (eI.symm_apply_apply T) =
              eqToHom (eI.symm_apply_apply T)
            rfl)
        exact (Zigzag.of_inv hstart).trans
          (hz.trans (Zigzag.of_hom hend))
      exact (Zigzag.of_inv hc0).trans hz'
    have to_base : ∀ a : CostructuredArrow F T, Zigzag a base := by
      intro a
      rcases a with ⟨j, ⟨⟨⟩⟩, a⟩
      rcases j with i | i
      · let b : (Sum.inl i : J) ⟶ Sum.inr i :=
          .inr (.inr ⟨i, rfl, rfl⟩)
        have hb : F.map b = 𝟙 _ := by
          change eqToHom (rfl : eI.symm i = eI.symm i) ≫
              𝟙 (eI.symm i) ≫
              eqToHom (rfl : eI.symm i = eI.symm i) = 𝟙 _
          simp
        have hba :
            CostructuredArrow.mk (S := F) (Y := (Sum.inl i : J)) a ⟶
              CostructuredArrow.mk (S := F) (Y := (Sum.inr i : J)) a :=
          CostructuredArrow.homMk b (by
            change F.map b ≫ a = a
            rw [hb]
            exact Category.id_comp _)
        exact (Zigzag.of_hom hba).trans (inr_to_base i a)
      · exact inr_to_base i a
    apply @zigzag_isConnected _ _ ⟨base⟩
    intro a b
    exact (to_base a).trans (to_base b).symm
  · refine ⟨fun T => ?_⟩
    let base : StructuredArrow T F :=
      StructuredArrow.mk (S := T) (T := F) (Y := (Sum.inr (eI T) : J))
        (eqToHom (eI.symm_apply_apply T).symm)
    have lift_path_struct : ∀ {X Z : I} (p : Quiver.Path X Z),
        W.paths p → ∀ q : T ⟶ X,
          Zigzag
            (StructuredArrow.mk (S := T) (T := F)
              (Y := (Sum.inr (eI X) : J))
              (q ≫ eqToHom (eI.symm_apply_apply X).symm))
            (StructuredArrow.mk (S := T) (T := F)
              (Y := (Sum.inr (eI Z) : J))
              (q ≫ CategoryTheory.composePath p ≫
                eqToHom (eI.symm_apply_apply Z).symm)) := by
      intro X Z p hp
      induction p with
      | nil =>
          intro q
          simpa using
            (Zigzag.refl
              (StructuredArrow.mk (S := T) (T := F)
                (Y := (Sum.inr (eI X) : J))
                (q ≫ eqToHom (eI.symm_apply_apply X).symm)))
      | @cons Y Z p f ih =>
          intro q
          rcases hp with ⟨hp, hf⟩
          have ih' := ih hp q
          let bridge' : (Sum.inl (eI Y) : J) ⟶ Sum.inr (eI Y) :=
            bridge Y
          let edge' : (Sum.inl (eI Y) : J) ⟶ Sum.inr (eI Z) :=
            genEdge f hf
          have hbca :
              StructuredArrow.mk (S := T) (T := F)
                  (Y := (Sum.inl (eI Y) : J))
                  (q ≫ CategoryTheory.composePath p ≫
                    eqToHom (eI.symm_apply_apply Y).symm) ⟶
                StructuredArrow.mk (S := T) (T := F)
                  (Y := (Sum.inr (eI Y) : J))
                  (q ≫ CategoryTheory.composePath p ≫
                    eqToHom (eI.symm_apply_apply Y).symm) :=
            StructuredArrow.homMk bridge' (by
              change
                (q ≫ CategoryTheory.composePath p ≫
                    eqToHom (eI.symm_apply_apply Y).symm) ≫
                    F.map bridge' =
                  q ≫ CategoryTheory.composePath p ≫
                    eqToHom (eI.symm_apply_apply Y).symm
              change
                (q ≫ CategoryTheory.composePath p ≫
                    eqToHom (eI.symm_apply_apply Y).symm) ≫
                    (eqToHom
                        (rfl : eI.symm (eI Y) = eI.symm (eI Y)) ≫
                      𝟙 (eI.symm (eI Y)) ≫
                      eqToHom
                        (rfl : eI.symm (eI Y) = eI.symm (eI Y))) =
                  q ≫ CategoryTheory.composePath p ≫
                    eqToHom (eI.symm_apply_apply Y).symm
              simp)
          have heca :
              StructuredArrow.mk (S := T) (T := F)
                  (Y := (Sum.inl (eI Y) : J))
                  (q ≫ CategoryTheory.composePath p ≫
                    eqToHom (eI.symm_apply_apply Y).symm) ⟶
                StructuredArrow.mk (S := T) (T := F)
                  (Y := (Sum.inr (eI Z) : J))
                  (q ≫ CategoryTheory.composePath p ≫ f ≫
                    eqToHom (eI.symm_apply_apply Z).symm) :=
            StructuredArrow.homMk edge' (by
              change
                (q ≫ CategoryTheory.composePath p ≫
                    eqToHom (eI.symm_apply_apply Y).symm) ≫
                    F.map (genEdge f hf) =
                  q ≫ CategoryTheory.composePath p ≫ f ≫
                    eqToHom (eI.symm_apply_apply Z).symm
              rw [map_genEdge]
              have htransport :
                  eqToHom (eI.symm_apply_apply Y).symm ≫ transport f =
                    f ≫ eqToHom (eI.symm_apply_apply Z).symm := by
                change
                  eqToHom (eI.symm_apply_apply Y).symm ≫
                      (eqToHom (eI.symm_apply_apply Y) ≫ f ≫
                        eqToHom (eI.symm_apply_apply Z).symm) =
                    f ≫ eqToHom (eI.symm_apply_apply Z).symm
                simp only [← Category.assoc, eqToHom_trans, eqToHom_refl,
                  Category.id_comp, Category.comp_id]
              change
                (q ≫ CategoryTheory.composePath p ≫
                    eqToHom (eI.symm_apply_apply Y).symm) ≫
                    (eqToHom (eI.symm_apply_apply Y) ≫ f ≫
                      eqToHom (eI.symm_apply_apply Z).symm) =
                  q ≫ CategoryTheory.composePath p ≫ f ≫
                    eqToHom (eI.symm_apply_apply Z).symm
              change eqToHom (eI.symm_apply_apply Y).symm ≫
                  (eqToHom (eI.symm_apply_apply Y) ≫ f ≫
                    eqToHom (eI.symm_apply_apply Z).symm) =
                f ≫ eqToHom (eI.symm_apply_apply Z).symm at htransport
              simpa only [Category.assoc] using
                congrArg
                  (fun k => q ≫ CategoryTheory.composePath p ≫ k)
                  htransport
              )
          simpa [composePath_cons] using
            ih'.trans ((Zigzag.of_inv hbca).trans (Zigzag.of_hom heca))
    have inr_to_base : ∀ (i : Fin n) (a : T ⟶ F.obj (Sum.inr i)),
        Zigzag (StructuredArrow.mk (S := T) (T := F)
          (Y := (Sum.inr i : J)) a) base := by
      intro i a
      let X : I := eI.symm i
      let aX : T ⟶ X := by
        change T ⟶ X
        exact a
      rcases hgen' aX with ⟨p, hp, hcomp⟩
      let c0 : StructuredArrow T F :=
        StructuredArrow.mk (S := T) (T := F)
          (Y := (Sum.inr (eI X) : J))
          (aX ≫ eqToHom (eI.symm_apply_apply X).symm)
      have hz := lift_path_struct p hp (𝟙 T)
      have hc0 : c0 ⟶ StructuredArrow.mk (S := T) (T := F)
          (Y := (Sum.inr i : J)) a := by
        let h : (Sum.inr (eI X) : J) = Sum.inr i :=
          congrArg Sum.inr (eI.apply_symm_apply i)
        exact StructuredArrow.homMk (eqToHom h) (by
          change c0.hom ≫ F.map (eqToHom h) = (show T ⟶ X from a)
          have hmap : F.map (eqToHom h) =
              eqToHom (eI.symm_apply_apply X) := by
            rw [eqToHom_map]
            apply congrArg eqToHom
            apply Subsingleton.elim
          dsimp [c0]
          rw [hmap]
          have hcancel :
              eqToHom (eI.symm_apply_apply X).symm ≫
                  eqToHom (eI.symm_apply_apply X) = 𝟙 X := by
            rw [eqToHom_trans]
            apply congrArg eqToHom
            rfl
          change
            (aX ≫ eqToHom (eI.symm_apply_apply X).symm) ≫
                eqToHom (eI.symm_apply_apply X) = aX
          rw [Category.assoc, hcancel, Category.comp_id])
      have hz' : Zigzag c0 base := by
        have hstart :
            StructuredArrow.mk (S := T) (T := F)
                (Y := (Sum.inr (eI T) : J))
                (𝟙 T ≫ eqToHom (eI.symm_apply_apply T).symm) ⟶ base :=
          StructuredArrow.homMk (𝟙 (Sum.inr (eI T))) (by
            change
              (𝟙 T ≫ eqToHom (eI.symm_apply_apply T).symm) ≫
                  F.map (𝟙 (Sum.inr (eI T))) = base.hom
            rw [F.map_id]
            change
              (𝟙 T ≫ eqToHom (eI.symm_apply_apply T).symm) ≫ 𝟙 _ =
                eqToHom (eI.symm_apply_apply T).symm
            simp)
        have hend : c0 ⟶
            StructuredArrow.mk (S := T) (T := F)
                (Y := (Sum.inr (eI X) : J))
                (𝟙 T ≫ CategoryTheory.composePath p ≫
                  eqToHom (eI.symm_apply_apply X).symm) :=
          StructuredArrow.homMk (𝟙 (Sum.inr (eI X))) (by
            change c0.hom ≫ F.map (𝟙 (Sum.inr (eI X))) =
              𝟙 T ≫ CategoryTheory.composePath p ≫
                eqToHom (eI.symm_apply_apply X).symm
            dsimp [c0]
            rw [F.map_id]
            change
              (aX ≫ eqToHom (eI.symm_apply_apply X).symm) ≫ 𝟙 _ =
                𝟙 T ≫ CategoryTheory.composePath p ≫
                  eqToHom (eI.symm_apply_apply X).symm
            rw [Category.comp_id, ← hcomp]
            simp)
        exact (Zigzag.of_hom hend).trans
          (hz.symm.trans (Zigzag.of_hom hstart))
      exact (Zigzag.of_inv hc0).trans hz'
    have to_base : ∀ a : StructuredArrow T F, Zigzag a base := by
      intro a
      rcases a with ⟨⟨⟨⟩⟩, j, a⟩
      rcases j with i | i
      · let b : (Sum.inl i : J) ⟶ Sum.inr i :=
          .inr (.inr ⟨i, rfl, rfl⟩)
        have hba :
            StructuredArrow.mk (S := T) (T := F)
                (Y := (Sum.inl i : J)) a ⟶
              StructuredArrow.mk (S := T) (T := F)
                (Y := (Sum.inr i : J)) (a ≫ F.map b) :=
          StructuredArrow.homMk b (by
            rfl)
        exact (Zigzag.of_hom hba).trans (inr_to_base i (a ≫ F.map b))
      · change T ⟶ eI.symm i at a
        exact inr_to_base i a
    apply @zigzag_isConnected _ _ ⟨base⟩
    intro a b
    exact (to_base a).trans (to_base b).symm
  · constructor
    · intro hJ
      have hJne : Nonempty J := @IsConnected.is_nonempty J _ hJ
      have hIne : Nonempty I :=
        ⟨F.obj (Classical.choice hJne)⟩
      have hzig : ∀ X Y : I, Zigzag X Y := by
        intro X Y
        have hXY : Zigzag (Sum.inr (eI X) : J) (Sum.inr (eI Y) : J) :=
          @isPreconnected_zigzag J _ hJ.toIsPreconnected
            (Sum.inr (eI X)) (Sum.inr (eI Y))
        exact
          (Zigzag.of_inv (eqToHom (eI.symm_apply_apply X))).trans
            ((zigzag_obj_of_zigzag F hXY).trans
              (Zigzag.of_hom (eqToHom (eI.symm_apply_apply Y))))
      exact @zigzag_isConnected I _ hIne hzig
    · intro hI
      have hIzig : ∀ X Y : I, Zigzag X Y := by
        intro X Y
        exact @isPreconnected_zigzag I _ hI.toIsPreconnected X Y
      have lift_hom : ∀ {X Y : I} (f : X ⟶ Y),
          Zigzag (Sum.inr (eI X) : J) (Sum.inr (eI Y) : J) := by
        intro X Y f
        rcases hgen' f with ⟨p, hp, _⟩
        exact lift_path p hp
      have lift_zigzag : ∀ {X Y : I}, Zigzag X Y →
          Zigzag (Sum.inr (eI X) : J) (Sum.inr (eI Y) : J) := by
        intro X Y h
        exact h.lift'
          (fun X => (Sum.inr (eI X) : J))
          (by
            intro X Y hXY
            rcases hXY with (⟨⟨f⟩⟩ | ⟨⟨f⟩⟩)
            · exact lift_hom f
            · exact (lift_hom f).symm)
      have to_canonical : ∀ j : J,
          Zigzag j (Sum.inr (eI (eI.symm (tag j))) : J) := by
        intro j
        rcases j with i | i
        · let b : (Sum.inl i : J) ⟶ Sum.inr i :=
            .inr (.inr ⟨i, rfl, rfl⟩)
          have h : (Sum.inr i : J) =
              Sum.inr (eI (eI.symm i)) :=
            congrArg Sum.inr (eI.apply_symm_apply i).symm
          exact (Zigzag.of_hom b).trans (Zigzag.of_hom (eqToHom h))
        · have h : (Sum.inr i : J) =
              Sum.inr (eI (eI.symm i)) :=
            congrArg Sum.inr (eI.apply_symm_apply i).symm
          exact Zigzag.of_hom (eqToHom h)
      have hJzig : ∀ j k : J, Zigzag j k := by
        intro j k
        exact (to_canonical j).trans
          ((lift_zigzag (hIzig (eI.symm (tag j)) (eI.symm (tag k)))).trans
            (to_canonical k).symm)
      exact @zigzag_isConnected J _
        ⟨Sum.inr (eI (Classical.choice (@IsConnected.is_nonempty I _ hI)))⟩ hJzig
  · constructor
    · rintro ⟨j⟩
      exact ⟨F.obj j⟩
    · rintro ⟨X⟩
      exact ⟨Sum.inr (eI X)⟩

theorem finite_diagram_replacement_has_limit_iff
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    HasLimit M ↔ HasLimit (R.F ⋙ M) := by
  exact (Functor.Initial.hasLimit_comp_iff R.F).symm

theorem finite_diagram_replacement_has_colimit_iff
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) :
    HasColimit M ↔ HasColimit (R.F ⋙ M) := by
  exact (Functor.Final.hasColimit_comp_iff R.F).symm

theorem finite_diagram_replacement_limit_iso_unique
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasLimit M] [HasLimit (R.F ⋙ M)] :
    ∃! e : limit M ≅ limit (R.F ⋙ M),
      ∀ j : R.J, e.hom ≫ limit.π (R.F ⋙ M) j = limit.π M (R.F.obj j) := by
  let c := Functor.Initial.limitConeComp R.F (getLimitCone M)
  let e : limit M ≅ limit (R.F ⋙ M) :=
    c.isLimit.conePointUniqueUpToIso (limit.isLimit (R.F ⋙ M))
  refine ⟨e, ?_, ?_⟩
  · intro j
    have h := c.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit (R.F ⋙ M)) j
    change e.hom ≫ limit.π (R.F ⋙ M) j = limit.π M (R.F.obj j) at h
    exact h
  · intro e' he'
    apply Iso.ext
    apply (limit.isLimit (R.F ⋙ M)).hom_ext
    intro j
    have h := c.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit (R.F ⋙ M)) j
    change e.hom ≫ limit.π (R.F ⋙ M) j = limit.π M (R.F.obj j) at h
    exact (he' j).trans h.symm

noncomputable def finite_diagram_replacement_limit_iso
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasLimit M] [HasLimit (R.F ⋙ M)] :
    limit M ≅ limit (R.F ⋙ M) :=
  Classical.choose (ExistsUnique.exists (finite_diagram_replacement_limit_iso_unique R M))

theorem finite_diagram_replacement_limit_iso_hom_comp
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasLimit M] [HasLimit (R.F ⋙ M)] (j : R.J) :
    (finite_diagram_replacement_limit_iso R M).hom ≫ limit.π (R.F ⋙ M) j =
      limit.π M (R.F.obj j) := by
  simpa [finite_diagram_replacement_limit_iso] using
    (Classical.choose_spec
      (ExistsUnique.exists (finite_diagram_replacement_limit_iso_unique R M))) j

theorem finite_diagram_replacement_colimit_iso_unique
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasColimit M] [HasColimit (R.F ⋙ M)] :
    ∃! e : colimit M ≅ colimit (R.F ⋙ M),
      ∀ j : R.J, colimit.ι M (R.F.obj j) ≫ e.hom =
        colimit.ι (R.F ⋙ M) j := by
  let c := Functor.Final.colimitCoconeComp R.F (getColimitCocone M)
  let e : colimit M ≅ colimit (R.F ⋙ M) :=
    c.isColimit.coconePointUniqueUpToIso (colimit.isColimit (R.F ⋙ M))
  refine ⟨e, ?_, ?_⟩
  · intro j
    have h := c.isColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (R.F ⋙ M)) j
    change colimit.ι M (R.F.obj j) ≫ e.hom = colimit.ι (R.F ⋙ M) j at h
    exact h
  · intro e' he'
    have he : ∀ j : R.J,
        colimit.ι M (R.F.obj j) ≫ e.hom = colimit.ι (R.F ⋙ M) j := by
      intro j
      have h := c.isColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit (R.F ⋙ M)) j
      change colimit.ι M (R.F.obj j) ≫ e.hom = colimit.ι (R.F ⋙ M) j at h
      exact h
    have hinv : e'.inv = e.inv := by
      apply (colimit.isColimit (R.F ⋙ M)).hom_ext
      intro j
      change colimit.ι (R.F ⋙ M) j ≫ e'.inv = colimit.ι (R.F ⋙ M) j ≫ e.inv
      calc
        colimit.ι (R.F ⋙ M) j ≫ e'.inv =
            (colimit.ι M (R.F.obj j) ≫ e'.hom) ≫ e'.inv := by rw [he' j]
        _ = colimit.ι M (R.F.obj j) := by simp
        _ = (colimit.ι M (R.F.obj j) ≫ e.hom) ≫ e.inv := by simp
        _ = colimit.ι (R.F ⋙ M) j ≫ e.inv := by rw [he j]
    apply Iso.ext
    apply (cancel_mono e'.inv).1
    rw [e'.hom_inv_id, hinv, e.hom_inv_id]

noncomputable def finite_diagram_replacement_colimit_iso
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasColimit M] [HasColimit (R.F ⋙ M)] :
    colimit M ≅ colimit (R.F ⋙ M) :=
  Classical.choose (ExistsUnique.exists (finite_diagram_replacement_colimit_iso_unique R M))

theorem finite_diagram_replacement_colimit_iso_hom_comp
    (R : FiniteDiagramReplacement I) {C : Type u'} [Category.{v'} C]
    (M : I ⥤ C) [HasColimit M] [HasColimit (R.F ⋙ M)] (j : R.J) :
    colimit.ι M (R.F.obj j) ≫
        (finite_diagram_replacement_colimit_iso R M).hom =
      colimit.ι (R.F ⋙ M) j := by
  simpa [finite_diagram_replacement_colimit_iso] using
    (Classical.choose_spec
      (ExistsUnique.exists (finite_diagram_replacement_colimit_iso_unique R M))) j

end FiniteDiagramReduction

section FiniteExistencePredicates

variable {C : Type u} [Category.{v} C]

/- These four predicates are the chapter-facing quantifiers over the canonical
   Mathlib index-category interfaces.  In particular, `IsConnected` already
   includes nonemptiness. -/
def HasNonemptyFiniteLimits : Prop :=
  ∀ {J : Type*} [SmallCategory J] [FinCategory J] [Nonempty J]
    (F : J ⥤ C), HasLimit F

def HasNonemptyFiniteColimits : Prop :=
  ∀ {J : Type*} [SmallCategory J] [FinCategory J] [Nonempty J]
    (F : J ⥤ C), HasColimit F

def HasConnectedFiniteLimits : Prop :=
  ∀ {J : Type*} [SmallCategory J] [FinCategory J] [IsConnected J]
    (F : J ⥤ C), HasLimit F

def HasConnectedFiniteColimits : Prop :=
  ∀ {J : Type*} [SmallCategory J] [FinCategory J] [IsConnected J]
    (F : J ⥤ C), HasColimit F

private theorem hasProduct_fin_succ [HasBinaryProducts C] :
    ∀ (n : ℕ) (f : Fin (n + 1) → C), HasProduct f
  | 0, f =>
      HasLimit.mk ⟨Fan.mk (f 0)
          (fun j => eqToHom (congrArg f (Fin.eq_zero j).symm)),
        Fan.IsLimit.mk _ (fun s => s.proj 0)
          (fun s j => by
            have hj : j = 0 := Fin.eq_zero j
            subst hj
            simp)
          (fun s m hm => by simpa using hm 0)⟩
  | n + 1, f =>
      let _ := hasProduct_fin_succ n (fun i : Fin (n + 1) => f i.succ)
      HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩

private theorem hasProduct_of_finite_nonempty [HasBinaryProducts C]
    {J : Type*} (f : J → C) [Finite J] [Nonempty J] : HasProduct f := by
  rcases Finite.exists_equiv_fin J with ⟨n, ⟨e⟩⟩
  have hn : n ≠ 0 := by
    intro hn
    let j : J := Classical.choice (inferInstance : Nonempty J)
    exact Fin.elim0 (hn ▸ e j)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let _ := hasProduct_fin_succ k (fun i : Fin (k + 1) => f (e.symm i))
  exact hasProduct_of_equiv_of_iso (fun i : Fin (k + 1) => f (e.symm i)) f e
    (fun x => by simpa using (Iso.refl (f x)))

private theorem hasCoproduct_fin_succ [HasBinaryCoproducts C] :
    ∀ (n : ℕ) (f : Fin (n + 1) → C), HasCoproduct f
  | 0, f =>
      HasColimit.mk ⟨Cofan.mk (f 0)
          (fun j => eqToHom (congrArg f (Fin.eq_zero j))),
        Cofan.IsColimit.mk _ (fun s => s.inj 0)
          (fun s j => by
            have hj : j = 0 := Fin.eq_zero j
            subst hj
            simp)
          (fun s m hm => by simpa using hm 0)⟩
  | n + 1, f =>
      let _ := hasCoproduct_fin_succ n (fun i : Fin (n + 1) => f i.succ)
      HasColimit.mk ⟨_, extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)⟩

private theorem hasCoproduct_of_finite_nonempty [HasBinaryCoproducts C]
    {J : Type*} (f : J → C) [Finite J] [Nonempty J] : HasCoproduct f := by
  rcases Finite.exists_equiv_fin J with ⟨n, ⟨e⟩⟩
  have hn : n ≠ 0 := by
    intro hn
    let j : J := Classical.choice (inferInstance : Nonempty J)
    exact Fin.elim0 (hn ▸ e j)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let _ := hasCoproduct_fin_succ k (fun i : Fin (k + 1) => f (e.symm i))
  exact hasCoproduct_of_equiv_of_iso (fun i : Fin (k + 1) => f (e.symm i)) f e
    (fun x => by simpa using (Iso.refl (f x)))

/- A finite family of objects, together with a finite list of equations between
   its legs, can be solved using pullbacks and equalizers.  The state below
   records the universal property needed while the family is enlarged. -/
private structure ConnectedLimitState {J C : Type*} [Category J] [Category C]
    (F : J ⥤ C) where
  α : Type*
  finite : Finite α
  obj : α → J
  pt : C
  leg : ∀ i, pt ⟶ F.obj (obj i)
  rel : ∀ (i j : α), (obj i ⟶ obj j) → Prop
  compat : ∀ (i j : α) (f : obj i ⟶ obj j),
    rel i j f → leg i ≫ F.map f = leg j
  universal : ∀ {W : C} (q : ∀ i, W ⟶ F.obj (obj i)),
    (∀ (i j : α) (f : obj i ⟶ obj j), rel i j f →
      q i ≫ F.map f = q j) →
    ∃! u : W ⟶ pt, ∀ i, u ≫ leg i = q i

private noncomputable def connectedLimitStateInitial {J C : Type*} [Category J] [Category C]
    (F : J ⥤ C) (r : J) : ConnectedLimitState F where
  α := Unit
  finite := inferInstance
  obj := fun _ => r
  pt := F.obj r
  leg := fun _ => 𝟙 _
  rel := fun _ _ _ => False
  compat := by
    intro i j f hf
    exact False.elim hf
  universal := by
    intro W q hq
    refine ⟨q (), ?_, ?_⟩
    · intro i
      simp
    · intro m hm
      simpa using hm ()

private noncomputable def connectedLimitStateExtendForward
    {J C : Type*} [Category J] [Category C] {F : J ⥤ C}
    (s : ConnectedLimitState F) (i : s.α) {X : J}
    (f : s.obj i ⟶ X) : ConnectedLimitState F := by
  letI : Finite s.α := s.finite
  exact
    { α := Sum s.α Unit
      finite := inferInstance
      obj := Sum.elim s.obj (fun _ => X)
      pt := s.pt
      leg := fun k => match k with
        | Sum.inl k => s.leg k
        | Sum.inr _ => s.leg i ≫ F.map f
      rel := fun a b g => match a, b with
        | Sum.inl a, Sum.inl b => s.rel a b g
        | Sum.inl a, Sum.inr _ => ∃ h : a = i, HEq g f
        | _, _ => False
      compat := by
        intro a b g h
        rcases a with a | a <;> rcases b with b | b
        · exact s.compat _ _ _ h
        · rcases h with ⟨rfl, h⟩
          cases h
          simp
        · exact False.elim h
        · exact False.elim h
      universal := by
        intro W q hq
        let qo : ∀ k : s.α, W ⟶ F.obj (s.obj k) := fun k => q (Sum.inl k)
        have hqo : ∀ (a b : s.α) (g : s.obj a ⟶ s.obj b),
            s.rel a b g → qo a ≫ F.map g = qo b := by
          intro a b g h
          exact hq (Sum.inl a) (Sum.inl b) g h
        obtain ⟨u, hu, huuniq⟩ := s.universal qo hqo
        refine ⟨u, ?_, ?_⟩
        · intro k
          rcases k with k | k
          · exact hu k
          · have h := hq (Sum.inl i) (Sum.inr k) f (by
              exact ⟨rfl, HEq.rfl⟩)
            change u ≫ (s.leg i ≫ F.map f) = q (Sum.inr k)
            rw [← Category.assoc, hu i]
            simpa using h
        · intro m hm
          apply huuniq
          intro k
          exact hm (Sum.inl k)
      }

private noncomputable def connectedLimitStateExtendBackward
    {J C : Type*} [Category J] [Category C] {F : J ⥤ C}
    [HasPullbacks C]
    (s : ConnectedLimitState F) (i : s.α) {X : J}
    (f : X ⟶ s.obj i) : ConnectedLimitState F := by
  letI : Finite s.α := s.finite
  let p := pullback (s.leg i) (F.map f)
  exact
    { α := Sum s.α Unit
      finite := inferInstance
      obj := Sum.elim s.obj (fun _ => X)
      pt := p
      leg := fun k => match k with
        | Sum.inl k => pullback.fst (s.leg i) (F.map f) ≫ s.leg k
        | Sum.inr _ => pullback.snd (s.leg i) (F.map f)
      rel := fun a b g => match a, b with
        | Sum.inl a, Sum.inl b => s.rel a b g
        | Sum.inr _, Sum.inl a => ∃ h : a = i, HEq g f
        | _, _ => False
      compat := by
        intro a b g h
        rcases a with a | a <;> rcases b with b | b
        · change s.obj a ⟶ s.obj b at g
          change s.rel a b g at h
          change
            (pullback.fst (s.leg i) (F.map f) ≫ s.leg a) ≫ F.map g =
              pullback.fst (s.leg i) (F.map f) ≫ s.leg b
          rw [Category.assoc, s.compat a b g h]
        · exact False.elim h
        · have hpb := (pullback.condition (f := s.leg i) (g := F.map f)).symm
          rcases h with ⟨ha, hg⟩
          cases ha
          cases hg
          exact hpb
        · exact False.elim h
      universal := by
        intro W q hq
        let qo : ∀ k : s.α, W ⟶ F.obj (s.obj k) := fun k => q (Sum.inl k)
        have hqo : ∀ (a b : s.α) (g : s.obj a ⟶ s.obj b),
            s.rel a b g → qo a ≫ F.map g = qo b := by
          intro a b g h
          exact hq (Sum.inl a) (Sum.inl b) g h
        obtain ⟨u, hu, huuniq⟩ := s.universal qo hqo
        have hcompat : q (Sum.inr ()) ≫ F.map f = q (Sum.inl i) := by
          simpa only [Sum.elim_inr, Sum.elim_inl] using
            hq (Sum.inr ()) (Sum.inl i) f (by
              exact ⟨rfl, HEq.rfl⟩)
        have hnew : q (Sum.inr ()) ≫ F.map f = u ≫ s.leg i := by
          exact hcompat.trans (by simpa [qo] using (hu i).symm)
        let v := pullback.lift u (q (Sum.inr ())) (by
          have hui : u ≫ s.leg i = q (Sum.inl i) := by simpa [qo] using hu i
          exact hui.trans hcompat.symm)
        refine ⟨v, ?_, ?_⟩
        · intro k
          rcases k with k | k
          · change v ≫ (pullback.fst (s.leg i) (F.map f) ≫ s.leg k) = q (Sum.inl k)
            have hvfst : v ≫ pullback.fst (s.leg i) (F.map f) = u :=
              pullback.lift_fst _ _ _
            have hcomp := congrArg (fun z => z ≫ s.leg k) hvfst
            exact hcomp.trans (by simpa [qo] using hu k) ▸
              (Category.assoc _ _ _).symm
          · change v ≫ pullback.snd (s.leg i) (F.map f) = q (Sum.inr k)
            exact pullback.lift_snd _ _ _
        · intro m hm
          have hmfst : m ≫ pullback.fst (s.leg i) (F.map f) = u := by
            apply huuniq
            intro k
            have hmk := hm (Sum.inl k)
            simp only [Sum.elim_inl] at hmk
            have hmk' :
                (m ≫ pullback.fst (s.leg i) (F.map f)) ≫ s.leg k =
                  q (Sum.inl k) := by
              rw [Category.assoc]
              exact hmk
            simpa [qo] using hmk'
          apply pullback.hom_ext
          · calc
              m ≫ pullback.fst (s.leg i) (F.map f) = u := hmfst
              _ = v ≫ pullback.fst (s.leg i) (F.map f) :=
                (pullback.lift_fst _ _ _).symm
          · have hmsnd : m ≫ pullback.snd (s.leg i) (F.map f) = q (Sum.inr ()) := by
              simpa only [Sum.elim_inr] using hm (Sum.inr ())
            exact hmsnd.trans (pullback.lift_snd _ _ _).symm
      }

universe w

private theorem connectedLimitStateExtendZigzag
    {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
    {F : J ⥤ C} [HasPullbacks C]
    (s : ConnectedLimitState.{u, u', w, v, v'} F) {a b : J} (i : s.α)
    (hi : s.obj i = a) (h : Zigzag a b) :
    ∃ (t : ConnectedLimitState.{u, u', w, v, v'} F) (e : s.α → t.α) (k : t.α),
      (∀ j, t.obj (e j) = s.obj j) ∧ t.obj k = b := by
  induction h generalizing s i with
  | refl =>
      exact ⟨s, id, i, by intro j; rfl, by simpa using hi⟩
  | @tail b c hab hbc ih =>
      rcases hbc with ⟨⟨g⟩⟩ | ⟨⟨g⟩⟩
      · obtain ⟨s₁, e₁, k₁, he₁, hk₁⟩ := ih s i hi
        let f : s₁.obj k₁ ⟶ c := eqToHom hk₁ ≫ g
        let s₂ := connectedLimitStateExtendForward s₁ k₁ f
        refine ⟨s₂, (fun j => Sum.inl (e₁ j)), Sum.inr (), ?_, ?_⟩
        · intro j
          change s₁.obj (e₁ j) = s.obj j
          exact he₁ j
        · change c = c
          rfl
      · obtain ⟨s₁, e₁, k₁, he₁, hk₁⟩ := ih s i hi
        let f : c ⟶ s₁.obj k₁ := g ≫ eqToHom hk₁.symm
        let s₂ := connectedLimitStateExtendBackward s₁ k₁ f
        refine ⟨s₂, (fun j => Sum.inl (e₁ j)), Sum.inr (), ?_, ?_⟩
        · intro j
          change s₁.obj (e₁ j) = s.obj j
          exact he₁ j
        · change c = c
          rfl

private theorem connectedLimitStateCoverList
    {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
    {F : J ⥤ C} [HasPullbacks C] [IsConnected J]
    (s : ConnectedLimitState.{u, u', w, v, v'} F) (r : J) (i : s.α)
    (hi : s.obj i = r) (xs : List J) :
    ∃ (t : ConnectedLimitState.{u, u', w, v, v'} F) (e : s.α → t.α)
        (root : t.α),
      (∀ j, t.obj (e j) = s.obj j) ∧ t.obj root = r ∧
        ∀ x ∈ xs, ∃ k, t.obj k = x := by
  induction xs generalizing s i with
  | nil =>
      exact ⟨s, id, i, by intro j; rfl, hi, by simp⟩
  | cons x xs ih =>
      have hz : Zigzag r x :=
        @isPreconnected_zigzag J _
          (inferInstance : IsConnected J).toIsPreconnected r x
      obtain ⟨s₁, e₁, k₁, he₁, hk₁⟩ :=
        connectedLimitStateExtendZigzag s i hi hz
      have hroot₁ : s₁.obj (e₁ i) = r := (he₁ i).trans hi
      obtain ⟨t, e₂, root, he₂, hroot₂, hcover₂⟩ :=
        ih s₁ (e₁ i) hroot₁
      refine ⟨t, (fun j => e₂ (e₁ j)), root, ?_, hroot₂, ?_⟩
      · intro j
        exact (he₂ (e₁ j)).trans (he₁ j)
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with hy | hy
        · subst y
          exact ⟨e₂ k₁, (he₂ k₁).trans hk₁⟩
        · exact hcover₂ y hy

private structure ConnectedLimitFixedState
    {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
    (F : J ⥤ C) (α : Type w) (obj : α → J) where
  pt : C
  leg : ∀ i, pt ⟶ F.obj (obj i)
  rel : ∀ (i j : α), (obj i ⟶ obj j) → Prop
  compat : ∀ (i j : α) (f : obj i ⟶ obj j),
    rel i j f → leg i ≫ F.map f = leg j
  universal : ∀ {W : C} (q : ∀ i, W ⟶ F.obj (obj i)),
    (∀ (i j : α) (f : obj i ⟶ obj j), rel i j f →
      q i ≫ F.map f = q j) →
    ∃! u : W ⟶ pt, ∀ i, u ≫ leg i = q i

private def connectedLimitFixedOfState
    {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
    {F : J ⥤ C} (s : ConnectedLimitState.{u, u', w, v, v'} F) :
    ConnectedLimitFixedState F s.α s.obj where
  pt := s.pt
  leg := s.leg
  rel := s.rel
  compat := s.compat
  universal := s.universal

private noncomputable def connectedLimitFixedAdd
    {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
    {F : J ⥤ C} [HasEqualizers C]
    {α : Type w} {obj : α → J} (s : ConnectedLimitFixedState F α obj)
    (i j : α) (f : obj i ⟶ obj j) : ConnectedLimitFixedState F α obj := by
  let a := s.leg i ≫ F.map f
  let b := s.leg j
  let e := equalizer.ι a b
  exact
    { pt := equalizer a b
      leg := fun k => e ≫ s.leg k
      rel := fun i' j' g => s.rel i' j' g ∨
        (i' = i ∧ j' = j ∧ HEq g f)
      compat := by
        intro i' j' g h
        rcases h with h | h
        · simp only [Category.assoc]
          rw [s.compat _ _ _ h]
        · rcases h with ⟨hi, hj, hf⟩
          have hcond := equalizer.condition (s.leg i ≫ F.map f) (s.leg j)
          cases hi
          cases hj
          cases hf
          simpa [e, a, b, Category.assoc] using hcond
      universal := by
        intro W q hq
        have hqold : ∀ (i' j' : α) (g : obj i' ⟶ obj j'),
            s.rel i' j' g → q i' ≫ F.map g = q j' := by
          intro i' j' g h
          exact hq _ _ _ (Or.inl h)
        obtain ⟨u, hu, huuniq⟩ := s.universal q hqold
        have hnew : u ≫ a = u ≫ b := by
          dsimp [a, b]
          rw [← Category.assoc, hu i, hu j]
          exact hq i j f (Or.inr ⟨rfl, rfl, HEq.rfl⟩)
        let v := equalizer.lift u hnew
        refine ⟨v, ?_, ?_⟩
        · intro k
          rw [← Category.assoc, equalizer.lift_ι]
          exact hu k
        · intro m hm
          apply equalizer.hom_ext
          have hm0 : ∀ k, (m ≫ e) ≫ s.leg k = q k := by
            intro k
            simpa only [Category.assoc] using hm k
          have hmeq : m ≫ e = u := huuniq (m ≫ e) hm0
          calc
            m ≫ e = u := hmeq
            _ = v ≫ e := by rw [equalizer.lift_ι] }

private theorem connectedLimitFixedAdd_old
    {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
    {F : J ⥤ C} [HasEqualizers C]
    {α : Type w} {obj : α → J} (s : ConnectedLimitFixedState F α obj)
    (i j : α) (f : obj i ⟶ obj j) {a b : α} {g : obj a ⟶ obj b} :
    s.rel a b g → (connectedLimitFixedAdd s i j f).rel a b g := by
  intro h
  change s.rel a b g ∨ _
  exact Or.inl h

private theorem connectedLimitFixedAdd_new
    {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
    {F : J ⥤ C} [HasEqualizers C]
    {α : Type w} {obj : α → J} (s : ConnectedLimitFixedState F α obj)
    (i j : α) (f : obj i ⟶ obj j) :
    (connectedLimitFixedAdd s i j f).rel i j f := by
  change s.rel i j f ∨ _
  exact Or.inr ⟨rfl, rfl, HEq.rfl⟩

private noncomputable def connectedLimitFixedAddList
    {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
    {F : J ⥤ C} [HasEqualizers C]
    {α : Type w} {obj : α → J} (s : ConnectedLimitFixedState F α obj) :
    List (Σ i j : α, obj i ⟶ obj j) → ConnectedLimitFixedState F α obj
  | [] => s
  | c :: L => connectedLimitFixedAdd
      (connectedLimitFixedAddList s L) c.1 c.2.1 c.2.2

private theorem connectedLimitFixedAddList_preserves
    {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
    {F : J ⥤ C} [HasEqualizers C]
    {α : Type w} {obj : α → J} (s : ConnectedLimitFixedState F α obj)
    (L : List (Σ i j : α, obj i ⟶ obj j))
    {a b : α} {g : obj a ⟶ obj b} :
    s.rel a b g →
      (connectedLimitFixedAddList s L).rel a b g := by
  induction L with
  | nil => exact id
  | cons c L ih =>
      intro h
      exact connectedLimitFixedAdd_old _ _ _ _ (ih h)

private theorem connectedLimitFixedAddList_mem
    {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
    {F : J ⥤ C} [HasEqualizers C]
    {α : Type w} {obj : α → J} (s : ConnectedLimitFixedState F α obj)
    (L : List (Σ i j : α, obj i ⟶ obj j)) :
    ∀ c ∈ L, (connectedLimitFixedAddList s L).rel c.1 c.2.1 c.2.2 := by
  induction L with
  | nil => simp
  | cons c L ih =>
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact connectedLimitFixedAdd_new _ _ _ _
      · exact connectedLimitFixedAdd_old _ _ _ _ (ih _ hd)

private theorem connectedLimitState_has_limit
    {J : Type u} [SmallCategory J] [FinCategory J]
    {C : Type u'} [Category.{v'} C] {F : J ⥤ C}
    [IsConnected J] [HasPullbacks C] [HasEqualizers C] : HasLimit F := by
  letI : Nonempty J := @IsConnected.is_nonempty J _ (inferInstance : IsConnected J)
  letI : Fintype J := Fintype.ofFinite J
  letI : Fintype (Arrow J) := Fintype.ofFinite (Arrow J)
  let r : J := Classical.choice (inferInstance : Nonempty J)
  let s₀ := connectedLimitStateInitial F r
  let xs : List J := (Fintype.elems : Finset J).toList
  obtain ⟨s, e, root, he, hroot, hcover⟩ :=
    connectedLimitStateCoverList s₀ r () rfl xs
  let pick : J → s.α := fun j => Classical.choose (hcover j (by
    simpa [xs] using (Fintype.complete j)))
  have hpick (j : J) : s.obj (pick j) = j :=
    Classical.choose_spec (hcover j (by
      simpa [xs] using (Fintype.complete j)))
  letI : Finite s.α := s.finite
  letI : Fintype s.α := Fintype.ofFinite s.α
  let sf := connectedLimitFixedOfState s
  let idConstraints : List (Σ i j : s.α, s.obj i ⟶ s.obj j) :=
    (Fintype.elems : Finset s.α).toList.map (fun i =>
      ⟨pick (s.obj i), i, eqToHom (hpick (s.obj i))⟩)
  let arrowConstraints : List (Σ i j : s.α, s.obj i ⟶ s.obj j) :=
    (Fintype.elems : Finset (Arrow J)).toList.map (fun a =>
      ⟨pick a.left, pick a.right,
        eqToHom (hpick a.left) ≫ a.hom ≫ eqToHom (hpick a.right).symm⟩)
  let constraints := idConstraints ++ arrowConstraints
  let t := connectedLimitFixedAddList sf constraints
  have hid (i : s.α) :
      t.rel (pick (s.obj i)) i (eqToHom (hpick (s.obj i))) := by
    have hi : i ∈ (Fintype.elems : Finset s.α) := Fintype.complete i
    have hi' : i ∈ (Fintype.elems : Finset s.α).toList := by
      simpa using hi
    have hm :
        (⟨pick (s.obj i), i, eqToHom (hpick (s.obj i))⟩ :
            Σ i j : s.α, s.obj i ⟶ s.obj j) ∈ idConstraints := by
      refine List.mem_map.mpr ⟨i, hi', ?_⟩
      rfl
    exact connectedLimitFixedAddList_mem sf constraints _
      (List.mem_append.mpr (Or.inl hm))
  have harrow {X Y : J} (f : X ⟶ Y) :
      t.rel (pick X) (pick Y)
        (eqToHom (hpick X) ≫ f ≫ eqToHom (hpick Y).symm) := by
    have ha : Arrow.mk f ∈ (Fintype.elems : Finset (Arrow J)) :=
      Fintype.complete (Arrow.mk f)
    have ha' : Arrow.mk f ∈ (Fintype.elems : Finset (Arrow J)).toList := by
      simpa using ha
    have hm :
        (⟨pick X, pick Y,
          eqToHom (hpick X) ≫ f ≫ eqToHom (hpick Y).symm⟩ :
            Σ i j : s.α, s.obj i ⟶ s.obj j) ∈ arrowConstraints := by
      refine List.mem_map.mpr ⟨Arrow.mk f, ha', ?_⟩
      rfl
    exact connectedLimitFixedAddList_mem sf constraints _
      (List.mem_append.mpr (Or.inr hm))
  let qleg : ∀ X : J, t.pt ⟶ F.obj X := fun X =>
    t.leg (pick X) ≫ F.map (eqToHom (hpick X))
  let q : Cone F :=
    { pt := t.pt
      π :=
        { app := qleg
          naturality := by
            intro X Y f
            have h := t.compat (pick X) (pick Y)
              (eqToHom (hpick X) ≫ f ≫ eqToHom (hpick Y).symm) (harrow f)
            have h' := congrArg (fun z => z ≫ F.map (eqToHom (hpick Y))) h
            simpa [qleg, Functor.map_comp, Category.assoc] using h'.symm } }
  let hc : IsLimit q := by
    refine { lift := ?_, fac := ?_, uniq := ?_ }
    · intro d
      let qd : ∀ i : s.α, d.pt ⟶ F.obj (s.obj i) := fun i =>
        d.π.app (s.obj i)
      have hqd : ∀ (i j : s.α) (f : s.obj i ⟶ s.obj j),
          t.rel i j f → qd i ≫ F.map f = qd j := by
        intro i j f hf
        simpa [qd] using (d.π.naturality f).symm
      exact Classical.choose (t.universal qd hqd)
    · intro d X
      let qd : ∀ i : s.α, d.pt ⟶ F.obj (s.obj i) := fun i =>
        d.π.app (s.obj i)
      have hqd : ∀ (i j : s.α) (f : s.obj i ⟶ s.obj j),
          t.rel i j f → qd i ≫ F.map f = qd j := by
        intro i j f hf
        simpa [qd] using (d.π.naturality f).symm
      have hu := (Classical.choose_spec (t.universal qd hqd)).1
      calc
        Classical.choose (t.universal qd hqd) ≫ q.π.app X =
            (Classical.choose (t.universal qd hqd) ≫ t.leg (pick X)) ≫
              F.map (eqToHom (hpick X)) := by
                change Classical.choose (t.universal qd hqd) ≫
                    (t.leg (pick X) ≫ F.map (eqToHom (hpick X))) = _
                simp only [Category.assoc]
        _ = d.π.app (s.obj (pick X)) ≫ F.map (eqToHom (hpick X)) := by
          rw [hu]
        _ = d.π.app X := by
          simpa using (d.π.naturality (eqToHom (hpick X))).symm
    · intro d m hm
      let qd : ∀ i : s.α, d.pt ⟶ F.obj (s.obj i) := fun i =>
        d.π.app (s.obj i)
      have hqd : ∀ (i j : s.α) (f : s.obj i ⟶ s.obj j),
          t.rel i j f → qd i ≫ F.map f = qd j := by
        intro i j f hf
        simpa [qd] using (d.π.naturality f).symm
      apply (Classical.choose_spec (t.universal qd hqd)).2 m
      intro i
      have hi := t.compat (pick (s.obj i)) i
        (eqToHom (hpick (s.obj i))) (hid i)
      calc
        m ≫ t.leg i =
            m ≫ (t.leg (pick (s.obj i)) ≫ F.map
              (eqToHom (hpick (s.obj i)))) := by rw [hi]
        _ = m ≫ q.π.app (s.obj i) := by rfl
        _ = d.π.app (s.obj i) := hm _
  exact ⟨q, hc⟩

/- Connected finite limits are exactly the limits generated by equalizers and
   fibre products. -/
theorem has_connected_finite_limits_iff :
    HasConnectedFiniteLimits (C := C) ↔ HasEqualizers C ∧ HasPullbacks C := by
  constructor
  · intro h
    let _ : Category (ULift WalkingParallelPair) :=
      CategoryTheory.uliftCategory WalkingParallelPair
    let _ : Category (ULift WalkingCospan) :=
      CategoryTheory.uliftCategory WalkingCospan
    let _ : IsConnected (ULiftHom (ULift WalkingParallelPair)) :=
      isConnected_of_equivalent (ULiftHomULiftCategory.equiv WalkingParallelPair)
    let _ : IsConnected (ULiftHom (ULift WalkingCospan)) :=
      isConnected_of_equivalent (ULiftHomULiftCategory.equiv WalkingCospan)
    let _ : ∀ {X Y : C} (f g : X ⟶ Y), HasLimit (parallelPair f g) := by
      intro X Y f g
      let _ : HasLimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g) :=
        h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      let e := (ULiftHomULiftCategory.equiv WalkingParallelPair).symm
      let _ : HasLimit (e.functor ⋙ parallelPair f g) := by
        change HasLimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
        exact h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      exact hasLimit_of_equivalence_comp e
    let _ : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),
        HasLimit (cospan f g) := by
      intro X Y Z f g
      let _ : HasLimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ cospan f g) :=
        h (ULiftHom.down ⋙ ULift.downFunctor ⋙ cospan f g)
      let e := (ULiftHomULiftCategory.equiv WalkingCospan).symm
      let _ : HasLimit (e.functor ⋙ cospan f g) := by
        change HasLimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ cospan f g)
        exact h (ULiftHom.down ⋙ ULift.downFunctor ⋙ cospan f g)
      exact hasLimit_of_equivalence_comp e
    exact ⟨hasEqualizers_of_hasLimit_parallelPair (C := C),
      hasPullbacks_of_hasLimit_cospan C⟩
  · rintro ⟨hEqualizers, hPullbacks⟩
    intro J _ _ _ F
    let _ : HasEqualizers C := hEqualizers
    let _ : HasPullbacks C := hPullbacks
    have hgen : HasFiniteGeneratingMorphisms (I := J) := by
      refine ⟨Set.univ, Set.finite_univ, ?_⟩
      intro X Y f
      refine ⟨f.toPath, ?_, ?_⟩
      · simpa [MorphismProperty.paths, Quiver.Hom.toPath] using
          (MorphismProperty.toPath_mem_paths (W := fun _ _ g : X ⟶ Y =>
            Arrow.mk g ∈ (Set.univ : Set (Arrow J))) (Set.mem_univ _))
      · exact CategoryTheory.composePath_toPath f
    obtain ⟨R⟩ := finite_diagram_category hgen
    rw [finite_diagram_replacement_has_limit_iff R F]
    letI : IsConnected R.J := R.connected_iff.mpr inferInstance
    exact connectedLimitState_has_limit

/- The dual connected-colimit statement. -/
theorem has_connected_finite_colimits_iff :
    HasConnectedFiniteColimits (C := C) ↔ HasCoequalizers C ∧ HasPushouts C := by
  constructor
  · intro h
    let _ : Category (ULift WalkingParallelPair) :=
      CategoryTheory.uliftCategory WalkingParallelPair
    let _ : Category (ULift WalkingSpan) :=
      CategoryTheory.uliftCategory WalkingSpan
    let _ : IsConnected (ULiftHom (ULift WalkingParallelPair)) :=
      isConnected_of_equivalent (ULiftHomULiftCategory.equiv WalkingParallelPair)
    let _ : IsConnected (ULiftHom (ULift WalkingSpan)) :=
      isConnected_of_equivalent (ULiftHomULiftCategory.equiv WalkingSpan)
    let _ : ∀ {X Y : C} (f g : X ⟶ Y), HasColimit (parallelPair f g) := by
      intro X Y f g
      let _ : HasColimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g) :=
        h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      let e := (ULiftHomULiftCategory.equiv WalkingParallelPair).symm
      let _ : HasColimit (e.functor ⋙ parallelPair f g) := by
        change HasColimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
        exact h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      exact hasColimit_of_equivalence_comp e
    let _ : ∀ {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z),
        HasColimit (span f g) := by
      intro X Y Z f g
      let _ : HasColimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ span f g) :=
        h (ULiftHom.down ⋙ ULift.downFunctor ⋙ span f g)
      let e := (ULiftHomULiftCategory.equiv WalkingSpan).symm
      let _ : HasColimit (e.functor ⋙ span f g) := by
        change HasColimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ span f g)
        exact h (ULiftHom.down ⋙ ULift.downFunctor ⋙ span f g)
      exact hasColimit_of_equivalence_comp e
    exact ⟨hasCoequalizers_of_hasColimit_parallelPair (C := C),
      hasPushouts_of_hasColimit_span C⟩
  · rintro ⟨hCoequalizers, hPushouts⟩
    intro J _ _ _ F
    let _ : HasCoequalizers C := hCoequalizers
    let _ : HasPushouts C := hPushouts
    have hgen : HasFiniteGeneratingMorphisms (I := J) := by
      refine ⟨Set.univ, Set.finite_univ, ?_⟩
      intro X Y f
      refine ⟨f.toPath, ?_, ?_⟩
      · simpa [MorphismProperty.paths, Quiver.Hom.toPath] using
          (MorphismProperty.toPath_mem_paths (W := fun _ _ g : X ⟶ Y =>
            Arrow.mk g ∈ (Set.univ : Set (Arrow J))) (Set.mem_univ _))
      · exact CategoryTheory.composePath_toPath f
    obtain ⟨R⟩ := finite_diagram_category hgen
    rw [finite_diagram_replacement_has_colimit_iff R F]
    letI : IsConnected R.J := R.connected_iff.mpr inferInstance
    letI : HasLimit (R.F ⋙ F).op := by
      exact connectedLimitState_has_limit
    exact hasColimit_of_hasLimit_op (R.F ⋙ F)

/- The first presentation of nonempty finite limits from the source. -/
theorem has_nonempty_finite_limits_iff :
    HasNonemptyFiniteLimits (C := C) ↔
      HasBinaryProducts C ∧ HasEqualizers C := by
  constructor
  · intro h
    let _ : Category (ULift (Discrete WalkingPair)) :=
      CategoryTheory.uliftCategory (Discrete WalkingPair)
    let _ : Category (ULift WalkingParallelPair) :=
      CategoryTheory.uliftCategory WalkingParallelPair
    let _ : ∀ {X Y : C}, HasLimit (pair X Y) := by
      intro X Y
      let _ : HasLimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y) :=
        h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      let e := (ULiftHomULiftCategory.equiv (Discrete WalkingPair)).symm
      let _ : HasLimit (e.functor ⋙ pair X Y) := by
        change HasLimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
        exact h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      exact hasLimit_of_equivalence_comp e
    let _ : ∀ {X Y : C} (f g : X ⟶ Y), HasLimit (parallelPair f g) := by
      intro X Y f g
      let _ : HasLimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g) :=
        h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      let e := (ULiftHomULiftCategory.equiv WalkingParallelPair).symm
      let _ : HasLimit (e.functor ⋙ parallelPair f g) := by
        change HasLimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
        exact h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      exact hasLimit_of_equivalence_comp e
    exact ⟨hasBinaryProducts_of_hasLimit_pair C,
      hasEqualizers_of_hasLimit_parallelPair (C := C)⟩
  · rintro ⟨hProducts, hEqualizers⟩
    intro J _ _ _ F
    let _ : HasBinaryProducts C := hProducts
    let _ : HasEqualizers C := hEqualizers
    let j : J := Classical.choice (inferInstance : Nonempty J)
    let _ : Nonempty (Σ p : J × J, p.1 ⟶ p.2) := ⟨⟨(j, j), 𝟙 j⟩⟩
    let _ : HasLimit (Discrete.functor F.obj) :=
      hasProduct_of_finite_nonempty (fun j => F.obj j)
    let _ : HasLimit
        (Discrete.functor (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)) :=
      hasProduct_of_finite_nonempty (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)
    exact hasLimit_of_equalizer_and_product F

section EqualizerFromFibreProducts

variable {C : Type u} [Category.{v} C]

/- This is the displayed construction in the proof of the source's
   `almost-finite-limits` and `finite-limits` lemmas.  The first pullback is
   `A ×_{a,B,b} A`; the second pulls it back along the diagonal of `A × A`. -/
noncomputable def equalizerViaPullbacks [HasBinaryProducts C] [HasPullbacks C]
    {A B : C} (a b : A ⟶ B) : C :=
  pullback
    (prod.lift (pullback.fst a b) (pullback.snd a b))
    (prod.lift (𝟙 A) (𝟙 A))

noncomputable def equalizerViaPullbacksMorphism [HasBinaryProducts C] [HasPullbacks C]
    {A B : C} (a b : A ⟶ B) : equalizerViaPullbacks a b ⟶ A :=
  pullback.snd
    (prod.lift (pullback.fst a b) (pullback.snd a b))
    (prod.lift (𝟙 A) (𝟙 A))

theorem equalizerViaPullbacks_isEqualizer [HasBinaryProducts C] [HasPullbacks C]
    {A B : C} (a b : A ⟶ B) :
    Formalization.Books.Categories.Unit10.IsEqualizer
      (equalizerViaPullbacksMorphism a b) a b := by
  apply Formalization.Books.Categories.Unit10.isEqualizer_iff.mpr
  have h₁ :
      pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
          (prod.lift (𝟙 A) (𝟙 A)) ≫ pullback.fst a b =
        pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b))
          (prod.lift (𝟙 A) (𝟙 A)) := by
    simpa only [Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id,
      Category.id_comp] using congrArg (fun k => k ≫ prod.fst)
      (pullback.condition
        (f := prod.lift (pullback.fst a b) (pullback.snd a b))
        (g := prod.lift (𝟙 A) (𝟙 A)))
  have h₂ :
      pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
          (prod.lift (𝟙 A) (𝟙 A)) ≫ pullback.snd a b =
        pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b))
          (prod.lift (𝟙 A) (𝟙 A)) := by
    simpa only [Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id,
      Category.id_comp] using congrArg (fun k => k ≫ prod.snd)
      (pullback.condition
        (f := prod.lift (pullback.fst a b) (pullback.snd a b))
        (g := prod.lift (𝟙 A) (𝟙 A)))
  constructor
  · dsimp [equalizerViaPullbacksMorphism, equalizerViaPullbacks]
    calc
      pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b))
          (prod.lift (𝟙 A) (𝟙 A)) ≫ a =
          (pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
            (prod.lift (𝟙 A) (𝟙 A)) ≫ pullback.fst a b) ≫ a := by rw [h₁]
      _ = pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
          (prod.lift (𝟙 A) (𝟙 A)) ≫ (pullback.fst a b ≫ a) := by simp [Category.assoc]
      _ = pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
          (prod.lift (𝟙 A) (𝟙 A)) ≫ (pullback.snd a b ≫ b) := by
        rw [pullback.condition]
      _ = (pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
          (prod.lift (𝟙 A) (𝟙 A)) ≫ pullback.snd a b) ≫ b := by
        simp [Category.assoc]
      _ = pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b))
          (prod.lift (𝟙 A) (𝟙 A)) ≫ b := by rw [h₂]
  · intro W t ht
    let u : W ⟶ pullback a b := pullback.lift t t ht
    let h : u ≫ prod.lift (pullback.fst a b) (pullback.snd a b) =
        t ≫ prod.lift (𝟙 A) (𝟙 A) := by
      apply prod.hom_ext
      · simp only [u, prod.comp_lift, pullback.lift_fst, prod.lift_fst, Category.comp_id]
      · simp only [u, prod.comp_lift, pullback.lift_snd, prod.lift_snd, Category.comp_id]
    let s : W ⟶ equalizerViaPullbacks a b := pullback.lift u t h
    refine ⟨s, ?_, ?_⟩
    · dsimp [s]
      change pullback.lift u t h ≫
        pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b))
          (prod.lift (𝟙 A) (𝟙 A)) = t
      exact pullback.lift_snd _ _ _
    · intro s' hs'
      dsimp [equalizerViaPullbacks, equalizerViaPullbacksMorphism] at s s' hs' ⊢
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · change (s' ≫ pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
            (prod.lift (𝟙 A) (𝟙 A))) ≫ pullback.fst a b =
            (s ≫ pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
              (prod.lift (𝟙 A) (𝟙 A))) ≫ pullback.fst a b
          calc
            (s' ≫ pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
                (prod.lift (𝟙 A) (𝟙 A))) ≫ pullback.fst a b =
                s' ≫ pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b))
                  (prod.lift (𝟙 A) (𝟙 A)) := by rw [Category.assoc, h₁]
            _ = t := hs'
            _ = s ≫ pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b))
              (prod.lift (𝟙 A) (𝟙 A)) := by simp only [s, pullback.lift_snd]
            _ = (s ≫ pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
                (prod.lift (𝟙 A) (𝟙 A))) ≫ pullback.fst a b := by
              rw [Category.assoc, h₁]
        · change (s' ≫ pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
            (prod.lift (𝟙 A) (𝟙 A))) ≫ pullback.snd a b =
            (s ≫ pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
              (prod.lift (𝟙 A) (𝟙 A))) ≫ pullback.snd a b
          calc
            (s' ≫ pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
                (prod.lift (𝟙 A) (𝟙 A))) ≫ pullback.snd a b =
                s' ≫ pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b))
                  (prod.lift (𝟙 A) (𝟙 A)) := by rw [Category.assoc, h₂]
            _ = t := hs'
            _ = s ≫ pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b))
              (prod.lift (𝟙 A) (𝟙 A)) := by simp only [s, pullback.lift_snd]
            _ = (s ≫ pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b))
                (prod.lift (𝟙 A) (𝟙 A))) ≫ pullback.snd a b := by
              rw [Category.assoc, h₂]
      · change s' ≫ pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b))
          (prod.lift (𝟙 A) (𝟙 A)) =
          s ≫ pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b))
            (prod.lift (𝟙 A) (𝟙 A))
        rw [hs', pullback.lift_snd]

end EqualizerFromFibreProducts

/- The second presentation of nonempty finite limits from the source. -/
theorem has_nonempty_finite_limits_iff_of_pullbacks :
    HasNonemptyFiniteLimits (C := C) ↔
      HasBinaryProducts C ∧ HasPullbacks C := by
  constructor
  · intro h
    have hProducts : HasBinaryProducts C :=
      (has_nonempty_finite_limits_iff (C := C)).mp h |>.1
    have hEqualizers : HasEqualizers C :=
      (has_nonempty_finite_limits_iff (C := C)).mp h |>.2
    let _ := hProducts
    let _ := hEqualizers
    exact ⟨hProducts, hasPullbacks_of_hasBinaryProducts_of_hasEqualizers C⟩
  · rintro ⟨hProducts, hPullbacks⟩
    apply (has_nonempty_finite_limits_iff (C := C)).mpr
    let _ := hProducts
    let _ := hPullbacks
    exact ⟨hProducts, hasEqualizers_of_hasPullbacks_and_binary_products (C := C)⟩

/- The first presentation of nonempty finite colimits from the source. -/
theorem has_nonempty_finite_colimits_iff :
    HasNonemptyFiniteColimits (C := C) ↔
      HasBinaryCoproducts C ∧ HasCoequalizers C := by
  constructor
  · intro h
    let _ : Category (ULift (Discrete WalkingPair)) :=
      CategoryTheory.uliftCategory (Discrete WalkingPair)
    let _ : Category (ULift WalkingParallelPair) :=
      CategoryTheory.uliftCategory WalkingParallelPair
    let _ : ∀ {X Y : C}, HasColimit (pair X Y) := by
      intro X Y
      let _ : HasColimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y) :=
        h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      let e := (ULiftHomULiftCategory.equiv (Discrete WalkingPair)).symm
      let _ : HasColimit (e.functor ⋙ pair X Y) := by
        change HasColimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
        exact h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      exact hasColimit_of_equivalence_comp e
    let _ : ∀ {X Y : C} (f g : X ⟶ Y), HasColimit (parallelPair f g) := by
      intro X Y f g
      let _ : HasColimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g) :=
        h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      let e := (ULiftHomULiftCategory.equiv WalkingParallelPair).symm
      let _ : HasColimit (e.functor ⋙ parallelPair f g) := by
        change HasColimit (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
        exact h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      exact hasColimit_of_equivalence_comp e
    exact ⟨hasBinaryCoproducts_of_hasColimit_pair C,
      hasCoequalizers_of_hasColimit_parallelPair (C := C)⟩
  · rintro ⟨hCoproducts, hCoequalizers⟩
    intro J _ _ _ F
    let _ : HasBinaryCoproducts C := hCoproducts
    let _ : HasCoequalizers C := hCoequalizers
    let j : J := Classical.choice (inferInstance : Nonempty J)
    let _ : Nonempty (Σ p : J × J, p.1 ⟶ p.2) := ⟨⟨(j, j), 𝟙 j⟩⟩
    let _ : HasColimit (Discrete.functor F.obj) :=
      hasCoproduct_of_finite_nonempty (fun j => F.obj j)
    let _ : HasColimit
        (Discrete.functor (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1)) :=
      hasCoproduct_of_finite_nonempty (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1)
    exact hasColimit_of_coequalizer_and_coproduct F

/- The second presentation of nonempty finite colimits from the source. -/
theorem has_nonempty_finite_colimits_iff_of_pushouts :
    HasNonemptyFiniteColimits (C := C) ↔
      HasBinaryCoproducts C ∧ HasPushouts C := by
  constructor
  · intro h
    have hCoproducts : HasBinaryCoproducts C :=
      (has_nonempty_finite_colimits_iff (C := C)).mp h |>.1
    have hCoequalizers : HasCoequalizers C :=
      (has_nonempty_finite_colimits_iff (C := C)).mp h |>.2
    let _ := hCoproducts
    let _ := hCoequalizers
    exact ⟨hCoproducts, hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers C⟩
  · rintro ⟨hCoproducts, hPushouts⟩
    apply (has_nonempty_finite_colimits_iff (C := C)).mpr
    let _ := hCoproducts
    let _ := hPushouts
    exact ⟨hCoproducts, hasCoequalizers_of_hasPushouts_and_binary_coproducts (C := C)⟩

/- The first presentation of finite limits from the source. -/
theorem has_finite_limits_iff :
    HasFiniteLimits C ↔
      HasFiniteProducts C ∧ HasEqualizers C := by
  constructor
  · intro h
    let _ := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hProducts, hEqualizers⟩
    let _ := hProducts
    let _ := hEqualizers
    exact hasFiniteLimits_of_hasEqualizers_and_finite_products (C := C)

/- The second presentation of finite limits from the source. -/
theorem has_finite_limits_iff_of_terminal_and_pullbacks :
    HasFiniteLimits C ↔ HasTerminal C ∧ HasPullbacks C := by
  constructor
  · intro h
    let _ := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hTerminal, hPullbacks⟩
    let _ := hTerminal
    let _ := hPullbacks
    exact hasFiniteLimits_of_hasTerminal_and_pullbacks (C := C)

/- The first presentation of finite colimits from the source. -/
theorem has_finite_colimits_iff :
    HasFiniteColimits C ↔
      HasFiniteCoproducts C ∧ HasCoequalizers C := by
  constructor
  · intro h
    let _ := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hCoproducts, hCoequalizers⟩
    let _ := hCoproducts
    let _ := hCoequalizers
    exact hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts (C := C)

/- The second presentation of finite colimits from the source. -/
theorem has_finite_colimits_iff_of_initial_and_pushouts :
    HasFiniteColimits C ↔ HasInitial C ∧ HasPushouts C := by
  constructor
  · intro h
    let _ := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hInitial, hPushouts⟩
    let _ := hInitial
    let _ := hPushouts
    exact hasFiniteColimits_of_hasInitial_and_pushouts (C := C)

end FiniteExistencePredicates

end

end Formalization.Books.Categories.Unit18
