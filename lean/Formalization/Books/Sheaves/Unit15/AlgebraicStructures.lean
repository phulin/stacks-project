import Formalization.Books.Sheaves.Unit05.PresheavesOfAlgebraicStructures
import Formalization.Books.Sheaves.Unit09.SheavesOfAlgebraicStructures
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.MonCat.FilteredColimits
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Lie.Basic
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Sheaves on Spaces, Chapter 15: Algebraic structures

The source span `books/sheaves.tex:1177--1332` is the chapter's section
`Algebraic structures`.  The declarations below keep category-valued
presheaves canonical (`TopCat.Presheaf`) and express the source's underlying
set convention through the forgetful functor from Chapter 5.
-/

namespace Formalization.Books.Sheaves.Unit15

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit09

universe u v r k

noncomputable section

/-! ## Types of algebraic structures -/

/--
A category-valued functor is a type of algebraic structure when it has the
faithfulness, limit, filtered-colimit, and isomorphism-reflection properties
used throughout this section.
-/
class AlgebraicStructureType (C : Type u) [Category.{v} C]
    (F : C ⥤ Type v) : Prop extends
  F.Faithful,
  HasLimitsOfSize.{v, v} C,
  PreservesLimitsOfSize.{v, v} F,
  HasFilteredColimitsOfSize.{v, v} C,
  PreservesFilteredColimitsOfSize.{v, v} F,
  F.ReflectsIsomorphisms

/-!
The category of Lie algebras is not bundled in this Mathlib version.  The
small category below supplies the source-facing object and morphism types so
that the textbook's Lie-algebra example has a precise Lean interface.
-/

/-- The structure carried by an object of the fixed-field Lie-algebra category. -/
structure LieAlgebraObject (K : Type k) [Field K] (L : Type u) where
  lieRing : LieRing L
  lieAlgebra : @LieAlgebra K L _ lieRing

/-- The category of Lie algebras over a fixed field, with Lie homomorphisms. -/
structure LieAlgebraCat (K : Type k) [Field K] : Type (max k u + 1) where
  carrier : Type u
  structureData : LieAlgebraObject K carrier

namespace LieAlgebraCat

variable {K : Type k} [Field K]

instance : CoeSort (LieAlgebraCat K) (Type u) := ⟨LieAlgebraCat.carrier⟩

instance (X : LieAlgebraCat K) : LieRing (X : Type u) := X.structureData.lieRing

instance (X : LieAlgebraCat K) : LieAlgebra K (X : Type u) :=
  X.structureData.lieAlgebra

/-- Bundle an existing Lie algebra as an object. -/
def of (L : Type u) [LieRing L] [LieAlgebra K L] : LieAlgebraCat K :=
  ⟨L, { lieRing := inferInstance, lieAlgebra := inferInstance }⟩

/-- Morphisms in the fixed-field Lie-algebra category. -/
@[ext]
structure Hom (X Y : LieAlgebraCat K) where
  hom : (X : Type u) →ₗ⁅K⁆ (Y : Type u)

instance : Category (LieAlgebraCat K) where
  Hom := Hom
  id X := ⟨LieHom.id⟩
  comp f g := ⟨LieHom.comp g.hom f.hom⟩
  id_comp f := by
    apply Hom.ext
    exact LieHom.comp_id f.hom
  comp_id f := by
    apply Hom.ext
    exact LieHom.id_comp f.hom
  assoc f g h := by
    apply Hom.ext
    rfl

instance : ConcreteCategory (LieAlgebraCat K)
    (fun X Y => (X : Type u) →ₗ⁅K⁆ (Y : Type u)) where
  hom f := f.hom
  ofHom f := ⟨f⟩
  hom_ofHom _ := rfl
  ofHom_hom f := by cases f; rfl
  id_apply := by intro X x; rfl
  comp_apply := by intro X Y Z f g x; rfl

end LieAlgebraCat

/-!
The standard examples in the source use the canonical forgetful functors.
The theorem is left as an interface statement at this stage; its proof is
the routine verification of the listed Mathlib limit and filtered-colimit
instances (and the corresponding Lie-algebra constructions).
-/

/-- Pointed sets, abelian groups, groups, monoids, rings, modules, and Lie
algebras are types of algebraic structures in the sense above. -/
theorem standardAlgebraicStructureTypes :
    AlgebraicStructureType (Pointed.{u}) (forget Pointed) ∧
      AlgebraicStructureType (AddCommGrpCat.{u}) (forget AddCommGrpCat) ∧
      AlgebraicStructureType (GrpCat.{u}) (forget GrpCat) ∧
      AlgebraicStructureType (MonCat.{u}) (forget MonCat) ∧
      AlgebraicStructureType (RingCat.{u}) (forget RingCat) ∧
      (∀ (R : Type r) [Ring R],
        AlgebraicStructureType (ModuleCat.{u} R) (forget (ModuleCat.{u} R))) ∧
      (∀ (K : Type k) [Field K],
        AlgebraicStructureType (LieAlgebraCat.{u} K) (forget (LieAlgebraCat.{u} K))) := by
  let pointedLimits : HasLimitsOfSize.{u, u} (Pointed.{u}) := by
    refine ⟨fun J => ?_⟩
    refine ⟨fun F => ?_⟩
    let G : J ⥤ Type u := F ⋙ forget Pointed
    let pc : Cone G :=
      { pt := PUnit
        π :=
          { app := fun j => ↾fun _ => (F.obj j).point
            naturality := by
              intro i j f
              ext x
              change (F.obj j).point = (F.map f).toFun (F.obj i).point
              exact (F.map f).map_point.symm } }
    let p : limit G := (limit.isLimit G).lift pc PUnit.unit
    let lc : Cone F :=
      { pt := Pointed.of p
        π :=
          { app := fun j =>
              ⟨limit.π G j, by
                change limit.π G j ((limit.isLimit G).lift pc PUnit.unit) =
                  (F.obj j).point
                simp [pc]⟩
            naturality := by
              intro i j f
              apply Pointed.Hom.ext
              funext x
              change (limit.π G j) x = (F.map f).toFun ((limit.π G i) x)
              have h := (limit.cone G).π.naturality f
              have hx := congrArg (fun q => q x) h
              calc
                (limit.π G j) x =
                    (ConcreteCategory.hom
                      (((Functor.const J).obj (limit.cone G).pt).map f ≫
                        (limit.cone G).π.app j)) x := by
                  simp
                _ = (ConcreteCategory.hom ((limit.cone G).π.app i ≫ G.map f)) x := hx
                _ = (F.map f).toFun ((limit.π G i) x) := by
                  simp [G]
                  change (F.map f).toFun ((limit.π G i) x) =
                    (F.map f).toFun ((limit.π G i) x)
                  rfl } }
    let l : ∀ s : Cone F, s.pt ⟶ lc.pt := fun s =>
      { toFun := (limit.isLimit G).lift ((forget Pointed).mapCone s)
        map_point := by
          apply Types.limit_ext G
          intro j
          have hs := congrArg (fun h => h s.pt.point)
            ((limit.isLimit G).fac ((forget Pointed).mapCone s) j)
          have hp := congrArg (fun h => h PUnit.unit)
            ((limit.isLimit G).fac pc j)
          change limit.π G j ((limit.isLimit G).lift ((forget Pointed).mapCone s)
              s.pt.point) = limit.π G j ((limit.isLimit G).lift pc PUnit.unit)
          calc
            limit.π G j ((limit.isLimit G).lift ((forget Pointed).mapCone s)
                s.pt.point) = (s.π.app j).toFun s.pt.point := by
                  calc
                    _ = (ConcreteCategory.hom (((forget Pointed).mapCone s).π.app j))
                        s.pt.point := by
                          simpa only [limit.π, ConcreteCategory.comp_apply,
                            Function.comp_apply] using hs
                    _ = (s.π.app j).toFun s.pt.point := by
                      change (s.π.app j).toFun s.pt.point = (s.π.app j).toFun s.pt.point
                      rfl
            _ = (F.obj j).point := (s.π.app j).map_point
            _ = limit.π G j ((limit.isLimit G).lift pc PUnit.unit) := by
              symm
              simp [pc] }
    refine ⟨⟨lc, ?_⟩⟩
    exact
      { lift := l
        fac := by
          intro s j
          apply Pointed.Hom.ext
          funext x
          change ((limit.isLimit G).lift ((forget Pointed).mapCone s) ≫
              limit.π G j) x = ((forget Pointed).mapCone s).π.app j x
          exact congrArg (fun q => q x)
            ((limit.isLimit G).fac ((forget Pointed).mapCone s) j)
        uniq := by
          intro s m hm
          apply Pointed.Hom.ext
          have huniq :
              (forget Pointed).map m =
                (limit.isLimit G).lift ((forget Pointed).mapCone s) := by
            apply (limit.isLimit G).uniq ((forget Pointed).mapCone s)
              ((forget Pointed).map m)
            intro j
            ext x
            have hmj := congrArg (fun q => q.toFun x) (hm j)
            change ((forget Pointed).map m ≫ limit.π G j) x =
              ((forget Pointed).mapCone s).π.app j x
            exact hmj
          funext x
          have hx := congrArg (fun q => q x) huniq
          change m.toFun x =
            ((limit.isLimit G).lift ((forget Pointed).mapCone s)) x at hx
          exact hx }
  let pointedFiltered : HasFilteredColimitsOfSize.{u, u} (Pointed.{u}) := by
    refine ⟨fun J => ?_⟩
    refine ⟨fun F => ?_⟩
    let G : J ⥤ Type u := F ⋙ forget Pointed
    let j0 : J := IsFiltered.nonempty.some
    let p : colimit G := colimit.ι G j0 (F.obj j0).point
    let c : Cocone F :=
      { pt := Pointed.of p
        ι :=
          { app := fun j =>
              ⟨colimit.ι G j, by
                apply (Types.FilteredColimit.colimit_eq_iff G).2
                obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs j j0
                refine ⟨k, f, g, ?_⟩
                change (F.map f).toFun (F.obj j).point =
                  (F.map g).toFun (F.obj j0).point
                exact (F.map f).map_point.trans (F.map g).map_point.symm⟩
            naturality := by
              intro i j f
              apply Pointed.Hom.ext
              funext x
              change (colimit.ι G j) ((F.map f).toFun x) =
                (colimit.ι G i) x
              have h := ConcreteCategory.congr_hom (colimit.w G f) x
              change (colimit.ι G j) ((F.map f).toFun x) =
                (colimit.ι G i) x at h
              exact h } }
    refine ⟨⟨c, ?_⟩⟩
    exact
      { desc := fun s =>
          { toFun := colimit.desc G ((forget Pointed).mapCocone s)
            map_point := by
              change colimit.desc G ((forget Pointed).mapCocone s)
                  (colimit.ι G j0 (F.obj j0).point) = s.pt.point
              have h := ConcreteCategory.congr_hom
                (colimit.ι_desc ((forget Pointed).mapCocone s) j0)
                (F.obj j0).point
              exact h.trans (s.ι.app j0).map_point }
        fac := by
          intro s j
          apply Pointed.Hom.ext
          funext x
          change (colimit.ι G j ≫
              colimit.desc G ((forget Pointed).mapCocone s)) x =
            ((forget Pointed).mapCocone s).ι.app j x
          exact congrArg (fun q => q x)
            (colimit.ι_desc ((forget Pointed).mapCocone s) j)
        uniq := by
          intro s m hm
          apply Pointed.Hom.ext
          have huniq :
              (forget Pointed).map m =
                colimit.desc G ((forget Pointed).mapCocone s) := by
            apply (colimit.isColimit G).uniq ((forget Pointed).mapCocone s)
              ((forget Pointed).map m)
            intro j
            ext x
            have hmj := congrArg (fun q => q.toFun x) (hm j)
            change (colimit.ι G j ≫ (forget Pointed).map m) x =
              ((forget Pointed).mapCocone s).ι.app j x
            exact hmj
          funext x
          have hx := congrArg (fun q => q x) huniq
          change m.toFun x =
            (colimit.desc G ((forget Pointed).mapCocone s)) x at hx
          exact hx }
  let pointedPreservesFiltered :
      PreservesFilteredColimitsOfSize.{u, u} (forget Pointed) := by
    refine ⟨fun J => ?_⟩
    refine ⟨?_⟩
    intro F
    let G : J ⥤ Type u := F ⋙ forget Pointed
    let j0 : J := IsFiltered.nonempty.some
    let p : colimit G := colimit.ι G j0 (F.obj j0).point
    let c : Cocone F :=
      { pt := Pointed.of p
        ι :=
          { app := fun j =>
              ⟨colimit.ι G j, by
                apply (Types.FilteredColimit.colimit_eq_iff G).2
                obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs j j0
                refine ⟨k, f, g, ?_⟩
                change (F.map f).toFun (F.obj j).point =
                  (F.map g).toFun (F.obj j0).point
                exact (F.map f).map_point.trans (F.map g).map_point.symm⟩
            naturality := by
              intro i j f
              apply Pointed.Hom.ext
              funext x
              change (colimit.ι G j) ((F.map f).toFun x) =
                (colimit.ι G i) x
              have h := ConcreteCategory.congr_hom (colimit.w G f) x
              change (colimit.ι G j) ((F.map f).toFun x) =
                (colimit.ι G i) x at h
              exact h } }
    let hc : IsColimit c := by
      exact
        { desc := fun s =>
            { toFun := colimit.desc G ((forget Pointed).mapCocone s)
              map_point := by
                change colimit.desc G ((forget Pointed).mapCocone s)
                    (colimit.ι G j0 (F.obj j0).point) = s.pt.point
                have h := ConcreteCategory.congr_hom
                  (colimit.ι_desc ((forget Pointed).mapCocone s) j0)
                  (F.obj j0).point
                exact h.trans (s.ι.app j0).map_point }
          fac := by
            intro s j
            apply Pointed.Hom.ext
            funext x
            change (colimit.ι G j ≫
                colimit.desc G ((forget Pointed).mapCocone s)) x =
              ((forget Pointed).mapCocone s).ι.app j x
            exact congrArg (fun q => q x)
              (colimit.ι_desc ((forget Pointed).mapCocone s) j)
          uniq := by
            intro s m hm
            apply Pointed.Hom.ext
            have huniq :
                (forget Pointed).map m =
                  colimit.desc G ((forget Pointed).mapCocone s) := by
              apply (colimit.isColimit G).uniq ((forget Pointed).mapCocone s)
                ((forget Pointed).map m)
              intro j
              ext x
              have hmj := congrArg (fun q => q.toFun x) (hm j)
              change (colimit.ι G j ≫ (forget Pointed).map m) x =
                ((forget Pointed).mapCocone s).ι.app j x
              exact hmj
            funext x
            have hx := congrArg (fun q => q x) huniq
            change m.toFun x =
              (colimit.desc G ((forget Pointed).mapCocone s)) x at hx
            exact hx }
    have hG : IsColimit ((forget Pointed).mapCocone c) := by
      apply IsColimit.ofIsoColimit (colimit.isColimit G)
      exact Cocone.ext (Iso.refl _) (by intro j; rfl)
    exact preservesColimit_of_preserves_colimit_cocone hc hG
  let pointedReflectsIso : (forget Pointed).ReflectsIsomorphisms := by
    refine ⟨?_⟩
    intro X Y f hu
    let u := (forget Pointed).map f
    let : IsIso u := hu
    let g : Y ⟶ X :=
      { toFun := inv u
        map_point := by
          change inv u Y.point = X.point
          rw [← f.map_point]
          change inv u (u X.point) = X.point
          have h := ConcreteCategory.congr_hom (IsIso.hom_inv_id u) X.point
          change inv u (u X.point) = X.point at h
          exact h }
    refine ⟨⟨g, ?_, ?_⟩⟩
    · apply Pointed.Hom.ext
      funext x
      change inv u (u x) = x
      have h := ConcreteCategory.congr_hom (IsIso.hom_inv_id u) x
      change inv u (u x) = x at h
      exact h
    · apply Pointed.Hom.ext
      funext y
      change u (inv u y) = y
      have h := ConcreteCategory.congr_hom (IsIso.inv_hom_id u) y
      change u (inv u y) = y at h
      exact h
  let : HasLimitsOfSize.{u, u} (Pointed.{u}) := pointedLimits
  let : HasFilteredColimitsOfSize.{u, u} (Pointed.{u}) := pointedFiltered
  let : PreservesLimitsOfSize.{u, u} (forget Pointed) :=
    typeToPointedForgetAdjunction.rightAdjoint_preservesLimits
  let : PreservesFilteredColimitsOfSize.{u, u} (forget Pointed) :=
    pointedPreservesFiltered
  let : (forget Pointed).ReflectsIsomorphisms := pointedReflectsIso
  let grpFiltered : HasFilteredColimitsOfSize.{u, u} (GrpCat.{u}) := by
    refine ⟨fun J => ?_⟩
    refine ⟨fun F => ?_⟩
    exact ⟨⟨GrpCat.FilteredColimits.colimitCocone F,
      GrpCat.FilteredColimits.colimitCoconeIsColimit F⟩⟩
  let monFiltered : HasFilteredColimitsOfSize.{u, u} (MonCat.{u}) := by
    refine ⟨fun J => ?_⟩
    refine ⟨fun F => ?_⟩
    exact ⟨⟨MonCat.FilteredColimits.colimitCocone F,
      MonCat.FilteredColimits.colimitCoconeIsColimit F⟩⟩
  let modulePreserves :
      ∀ (R : Type r) [Ring R],
        PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u} R)) := by
    intro R _
    refine ⟨fun J => ?_⟩
    refine ⟨?_⟩
    intro F
    let : PreservesColimitsOfShape J
        (forget₂ (ModuleCat.{u, r} R) AddCommGrpCat.{u}) := by
      infer_instance
    let : PreservesColimitsOfShape J (forget AddCommGrpCat.{u}) := by
      infer_instance
    change PreservesColimit F
      ((forget₂ (ModuleCat.{u, r} R) AddCommGrpCat.{u}) ⋙
        (forget AddCommGrpCat.{u}))
    infer_instance
  let : HasFilteredColimitsOfSize.{u, u} (GrpCat.{u}) := grpFiltered
  let : HasFilteredColimitsOfSize.{u, u} (MonCat.{u}) := monFiltered
  refine ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ?_, ?_⟩
  · intro R _
    let : PreservesFilteredColimitsOfSize.{u, u}
        (forget (ModuleCat.{u} R)) := modulePreserves R
    exact ⟨⟩
  · intro K _
    let lieLimitData :
        ∀ (J : Type u) [Category.{u} J] (F : J ⥤ LieAlgebraCat.{u} K),
          Σ t : LimitCone F,
            IsLimit ((forget (LieAlgebraCat.{u} K)).mapCone t.cone) := by
      intro J _ F
      let G := F ⋙ forget (LieAlgebraCat K)
      let L := G.sections
      let addL : L → L → L := fun x y =>
        ⟨fun j => show (F.obj j : Type u) from
            (show (F.obj j : Type u) from x.1 j) +
              (show (F.obj j : Type u) from y.1 j), by
          intro i j f
          change (F.map f).hom
              ((show (F.obj i : Type u) from x.1 i) +
                (show (F.obj i : Type u) from y.1 i)) =
            (show (F.obj j : Type u) from x.1 j) +
              (show (F.obj j : Type u) from y.1 j)
          rw [map_add]
          have hx := x.2 f
          have hy := y.2 f
          change (F.map f).hom (show (F.obj i : Type u) from x.1 i) =
            show (F.obj j : Type u) from x.1 j at hx
          change (F.map f).hom (show (F.obj i : Type u) from y.1 i) =
            show (F.obj j : Type u) from y.1 j at hy
          rw [hx, hy]⟩
      let zeroL : L :=
        ⟨fun _ => show (F.obj _) from 0, by
          intro i j f
          change (F.map f).hom 0 = 0
          exact map_zero _⟩
      let negL : L → L := fun x =>
        ⟨fun j => show (F.obj j : Type u) from
            -(show (F.obj j : Type u) from x.1 j), by
          intro i j f
          change (F.map f).hom (-(show (F.obj i : Type u) from x.1 i)) =
            -(show (F.obj j : Type u) from x.1 j)
          rw [map_neg]
          have hx := x.2 f
          change (F.map f).hom (show (F.obj i : Type u) from x.1 i) =
            show (F.obj j : Type u) from x.1 j at hx
          rw [hx]⟩
      letI : AddCommGroup L := by
        letI : Add L := ⟨addL⟩
        letI : Zero L := ⟨zeroL⟩
        letI : Neg L := ⟨negL⟩
        exact
          { add_assoc := by
              intro x y z
              apply Subtype.ext
              funext j
              change
                ((show (F.obj j : Type u) from x.1 j) +
                    (show (F.obj j : Type u) from y.1 j)) +
                  (show (F.obj j : Type u) from z.1 j) =
                (show (F.obj j : Type u) from x.1 j) +
                  ((show (F.obj j : Type u) from y.1 j) +
                    (show (F.obj j : Type u) from z.1 j))
              exact add_assoc _ _ _
            zero_add := by
              intro x
              apply Subtype.ext
              funext j
              change (0 : (F.obj j : Type u)) +
                  (show (F.obj j : Type u) from x.1 j) =
                (show (F.obj j : Type u) from x.1 j)
              exact zero_add _
            add_zero := by
              intro x
              apply Subtype.ext
              funext j
              change (show (F.obj j : Type u) from x.1 j) +
                  (0 : (F.obj j : Type u)) =
                (show (F.obj j : Type u) from x.1 j)
              exact add_zero _
            add_comm := by
              intro x y
              apply Subtype.ext
              funext j
              change (show (F.obj j : Type u) from x.1 j) +
                  (show (F.obj j : Type u) from y.1 j) =
                (show (F.obj j : Type u) from y.1 j) +
                  (show (F.obj j : Type u) from x.1 j)
              exact add_comm _ _
            neg_add_cancel := by
              intro x
              apply Subtype.ext
              funext j
              change -(show (F.obj j : Type u) from x.1 j) +
                  (show (F.obj j : Type u) from x.1 j) =
                (0 : (F.obj j : Type u))
              exact neg_add_cancel _
            nsmul := nsmulRec
            zsmul := zsmulRec
            sub_eq_add_neg := by
              intro x y
              rfl }
      let smulL : K → L → L := fun a x =>
        ⟨fun j => show (F.obj j : Type u) from
            a • (show (F.obj j : Type u) from x.1 j), by
          intro i j f
          change (F.map f).hom (a • (show (F.obj i : Type u) from x.1 i)) =
            a • (show (F.obj j : Type u) from x.1 j)
          rw [map_smul]
          have hx := x.2 f
          change (F.map f).hom (show (F.obj i : Type u) from x.1 i) =
            show (F.obj j : Type u) from x.1 j at hx
          rw [hx]⟩
      letI : Module K L := by
        letI : SMul K L := ⟨smulL⟩
        exact
          { mul_smul := by
              intro a b x
              apply Subtype.ext
              funext j
              change (a * b) • (show (F.obj j : Type u) from x.1 j) =
                a • b • (show (F.obj j : Type u) from x.1 j)
              exact mul_smul _ _ _
            one_smul := by
              intro x
              apply Subtype.ext
              funext j
              change (1 : K) • (show (F.obj j : Type u) from x.1 j) =
                show (F.obj j : Type u) from x.1 j
              exact one_smul _ _
            smul_add := by
              intro a x y
              apply Subtype.ext
              funext j
              change a • ((show (F.obj j : Type u) from x.1 j) +
                  (show (F.obj j : Type u) from y.1 j)) =
                a • (show (F.obj j : Type u) from x.1 j) +
                  a • (show (F.obj j : Type u) from y.1 j)
              exact smul_add _ _ _
            add_smul := by
              intro a b x
              apply Subtype.ext
              funext j
              change (a + b) • (show (F.obj j : Type u) from x.1 j) =
                a • (show (F.obj j : Type u) from x.1 j) +
                  b • (show (F.obj j : Type u) from x.1 j)
              exact add_smul _ _ _
            smul_zero := by
              intro a
              apply Subtype.ext
              funext j
              change a • (0 : (F.obj j : Type u)) = 0
              exact smul_zero _
            zero_smul := by
              intro x
              apply Subtype.ext
              funext j
              change (0 : K) • (show (F.obj j : Type u) from x.1 j) = 0
              exact zero_smul K _ }
      let bracketL : L → L → L := fun x y =>
        ⟨fun j =>
            show (F.obj j : Type u) from
              ⁅(show (F.obj j : Type u) from x.1 j),
                (show (F.obj j : Type u) from y.1 j)⁆, by
          intro i j f
          change (F.map f).hom
              ⁅(show (F.obj i : Type u) from x.1 i),
                (show (F.obj i : Type u) from y.1 i)⁆ =
            ⁅(show (F.obj j : Type u) from x.1 j),
              (show (F.obj j : Type u) from y.1 j)⁆
          rw [LieHom.map_lie]
          have hx := x.2 f
          have hy := y.2 f
          change (F.map f).hom (show (F.obj i : Type u) from x.1 i) =
            show (F.obj j : Type u) from x.1 j at hx
          change (F.map f).hom (show (F.obj i : Type u) from y.1 i) =
            show (F.obj j : Type u) from y.1 j at hy
          rw [hx, hy]⟩
      let lieRingL : LieRing L := by
        letI : Bracket L L := ⟨bracketL⟩
        exact
          { add_lie := by
              intro x y z
              apply Subtype.ext
              funext j
              change ⁅
                  (show (F.obj j : Type u) from x.1 j) +
                    (show (F.obj j : Type u) from y.1 j),
                  (show (F.obj j : Type u) from z.1 j)⁆ =
                ⁅(show (F.obj j : Type u) from x.1 j),
                  (show (F.obj j : Type u) from z.1 j)⁆ +
                  ⁅(show (F.obj j : Type u) from y.1 j),
                    (show (F.obj j : Type u) from z.1 j)⁆
              exact LieRing.add_lie _ _ _
            lie_add := by
              intro x y z
              apply Subtype.ext
              funext j
              change ⁅(show (F.obj j : Type u) from x.1 j),
                  (show (F.obj j : Type u) from y.1 j) +
                    (show (F.obj j : Type u) from z.1 j)⁆ =
                ⁅(show (F.obj j : Type u) from x.1 j),
                  (show (F.obj j : Type u) from y.1 j)⁆ +
                  ⁅(show (F.obj j : Type u) from x.1 j),
                    (show (F.obj j : Type u) from z.1 j)⁆
              exact LieRing.lie_add _ _ _
            lie_self := by
              intro x
              apply Subtype.ext
              funext j
              change ⁅(show (F.obj j : Type u) from x.1 j),
                  (show (F.obj j : Type u) from x.1 j)⁆ = 0
              exact LieRing.lie_self _
            leibniz_lie := by
              intro x y z
              apply Subtype.ext
              funext j
              change ⁅(show (F.obj j : Type u) from x.1 j),
                    ⁅(show (F.obj j : Type u) from y.1 j),
                      (show (F.obj j : Type u) from z.1 j)⁆⁆ =
                ⁅⁅(show (F.obj j : Type u) from x.1 j),
                    (show (F.obj j : Type u) from y.1 j)⁆,
                  (show (F.obj j : Type u) from z.1 j)⁆ +
                  ⁅(show (F.obj j : Type u) from y.1 j),
                    ⁅(show (F.obj j : Type u) from x.1 j),
                      (show (F.obj j : Type u) from z.1 j)⁆⁆
              exact LieRing.leibniz_lie _ _ _ }
      letI : LieRing L := lieRingL
      letI : Bracket L L := ⟨bracketL⟩
      letI : LieAlgebra K L := by
        exact
          { lie_smul := by
              intro a x y
              apply Subtype.ext
              funext j
              change ⁅(show (F.obj j : Type u) from x.1 j),
                  a • (show (F.obj j : Type u) from y.1 j)⁆ =
                a • ⁅(show (F.obj j : Type u) from x.1 j),
                  (show (F.obj j : Type u) from y.1 j)⁆
              exact LieAlgebra.lie_smul _ _ _ }
      let P : LieAlgebraCat.{u} K := LieAlgebraCat.of L
      let p : ∀ j, P ⟶ F.obj j := fun j =>
        { hom :=
            { toLinearMap :=
                { toFun := fun x => x.1 j
                  map_add' := by
                    intro x y
                    rfl
                  map_smul' := by
                    intro a x
                    rfl }
              map_lie' := by
                intro x y
                rfl } }
      let lc : Cone F :=
        { pt := P
          π :=
            { app := p
              naturality := by
                intro i j f
                apply LieAlgebraCat.Hom.ext
                apply LieHom.ext
                intro x
                change (p j).hom x = (F.map f).hom ((p i).hom x)
                change x.1 j = (F.map f).hom (x.1 i)
                exact (x.2 f).symm } }
      let l : ∀ s : Cone F, s.pt ⟶ P := fun s =>
        { hom :=
            { toLinearMap :=
                { toFun := fun x =>
                    ⟨fun j => (s.π.app j).hom x, by
                      intro i j f
                      have h := ConcreteCategory.congr_hom
                        (s.π.naturality f) x
                      change (s.π.app j).hom x =
                        (F.map f).hom ((s.π.app i).hom x) at h
                      exact h.symm⟩
                  map_add' := by
                    intro x y
                    apply Subtype.ext
                    funext j
                    change (s.π.app j).hom (x + y) =
                      (s.π.app j).hom x + (s.π.app j).hom y
                    exact (s.π.app j).hom.map_add x y
                  map_smul' := by
                    intro a x
                    apply Subtype.ext
                    funext j
                    change (s.π.app j).hom (a • x) =
                      a • (s.π.app j).hom x
                    exact (s.π.app j).hom.map_smul a x }
              map_lie' := by
                intro x y
                apply Subtype.ext
                funext j
                have h := (s.π.app j).hom.map_lie x y
                dsimp [P, LieAlgebraCat.of, lieRingL, bracketL] at h ⊢
                exact h } }
      let hlim : IsLimit lc :=
        { lift := l
          fac := by
            intro s j
            apply LieAlgebraCat.Hom.ext
            apply LieHom.ext
            intro x
            change (p j).hom ((l s).hom x) = (s.π.app j).hom x
            rfl
          uniq := by
            intro s m hm
            apply LieAlgebraCat.Hom.ext
            apply LieHom.ext
            intro x
            apply Subtype.ext
            funext j
            have h := ConcreteCategory.congr_hom (hm j) x
            change (m.hom x).1 j = (s.π.app j).hom x at h
            exact h }
      have hmap :
          IsLimit ((forget (LieAlgebraCat.{u} K)).mapCone lc) := by
        exact Types.limitConeIsLimit G
      exact ⟨⟨lc, hlim⟩, hmap⟩
    let lieLimits : HasLimitsOfSize.{u, u} (LieAlgebraCat.{u} K) := by
      refine ⟨fun J => ?_⟩
      refine ⟨fun F => ?_⟩
      exact ⟨⟨(lieLimitData J F).1⟩⟩
    let : HasLimitsOfSize.{u, u} (LieAlgebraCat.{u} K) := lieLimits
    let liePreserves :
        PreservesLimitsOfSize.{u, u} (forget (LieAlgebraCat.{u} K)) := by
      refine ⟨?_⟩
      intro J
      refine ⟨?_⟩
      intro F
      exact preservesLimit_of_preserves_limit_cone
        (lieLimitData J F).1.isLimit (lieLimitData J F).2
    let : PreservesLimitsOfSize.{u, u} (forget (LieAlgebraCat.{u} K)) :=
      liePreserves
    let lieColimitData :
        ∀ (J : Type u) [Category.{u} J] [IsFiltered J]
          (F : J ⥤ LieAlgebraCat.{u} K),
          Σ c : Cocone F, IsColimit c ×
            IsColimit ((forget (LieAlgebraCat.{u} K)).mapCocone c) := by
      intro J _ _ F
      let Fadd : J ⥤ AddCommGrpCat.{u} :=
        { obj := fun j => AddCommGrpCat.of (F.obj j : Type u)
          map := fun {i j} f =>
            AddCommGrpCat.ofHom (F.map f).hom.toLinearMap.toAddMonoidHom
          map_id := by
            intro j
            apply AddCommGrpCat.hom_ext
            change (F.map (𝟙 j)).hom.toLinearMap.toAddMonoidHom =
              AddMonoidHom.id (F.obj j).carrier
            rw [F.map_id]
            rfl
          map_comp := by
            intro i j l f g
            apply AddCommGrpCat.hom_ext
            change (F.map (f ≫ g)).hom.toLinearMap.toAddMonoidHom =
              (F.map g).hom.toLinearMap.toAddMonoidHom.comp
                (F.map f).hom.toLinearMap.toAddMonoidHom
            rw [F.map_comp]
            rfl }
      let Fmon : J ⥤ AddMonCat.{u} :=
        { obj := fun j => AddMonCat.of (F.obj j : Type u)
          map := fun {i j} f =>
            AddMonCat.ofHom (F.map f).hom.toLinearMap.toAddMonoidHom
          map_id := by
            intro j
            apply AddMonCat.hom_ext
            change (F.map (𝟙 j)).hom.toLinearMap.toAddMonoidHom =
              AddMonoidHom.id (F.obj j).carrier
            rw [F.map_id]
            rfl
          map_comp := by
            intro i j l f g
            apply AddMonCat.hom_ext
            change (F.map (f ≫ g)).hom.toLinearMap.toAddMonoidHom =
              (F.map g).hom.toLinearMap.toAddMonoidHom.comp
                (F.map f).hom.toLinearMap.toAddMonoidHom
            rw [F.map_comp]
            rfl }
      let Gadd : J ⥤ Type u := Fadd ⋙ forget AddCommGrpCat
      let L : AddCommGrpCat.{u} :=
        AddCommGrpCat.FilteredColimits.colimit Fadd
      let ι (j : J) (x : (F.obj j : Type u)) : (L : Type u) :=
        Gadd.ιColimitType j x
      have add_mk (x y : (Σ j, Fmon.obj j)) (k : J)
          (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
          ι x.1 x.2 + ι y.1 y.2 =
            ι k ((F.map f).hom x.2 + (F.map g).hom y.2) := by
        exact AddMonCat.FilteredColimits.colimit_add_mk_eq Fmon x y k f g
      have zero_mk (i : J) : (0 : (L : Type u)) = ι i 0 := by
        exact AddMonCat.FilteredColimits.colimit_zero_eq Fmon i
      have map_comp_apply {i j l : J} (p : i ⟶ j) (q : j ⟶ l)
          (x : (F.obj i : Type u)) :
          (F.map q).hom ((F.map p).hom x) = (F.map (p ≫ q)).hom x := by
        change (F.map p ≫ F.map q) x = (F.map (p ≫ q)).hom x
        rw [F.map_comp]
        rfl
      let smulL : K → L → L := by
        change K → Gadd.ColimitType → Gadd.ColimitType
        intro a
        exact Quot.lift
          (fun x =>
            Gadd.ιColimitType x.1
              (a • (show (F.obj x.1 : Type u) from x.2)))
          (by
            rintro x y ⟨f, h⟩
            apply Gadd.ιColimitType_eq_of_map_eq_map
              (show (F.obj x.1 : Type u) from
                a • (show (F.obj x.1 : Type u) from x.2))
              (show (F.obj y.1 : Type u) from
                a • (show (F.obj y.1 : Type u) from y.2))
              f (𝟙 _)
            dsimp [Gadd, Fadd] at h ⊢
            rw [F.map_id]
            change (F.map f).hom (a • (show (F.obj x.1 : Type u) from x.2)) =
              a • (show (F.obj y.1 : Type u) from y.2)
            rw [map_smul, ← h])
      have smul_mk (a : K) (i : J) (x : (F.obj i : Type u)) :
          smulL a (ι i x) = ι i (a • x) := by
        rfl
      let bracketL : L → L → L := by
        change Gadd.ColimitType → Gadd.ColimitType → Gadd.ColimitType
        intro r s
        refine Quot.liftOn₂ r s
          (fun Ua Vb =>
            letI : LieRing (F.obj (IsFiltered.max Ua.1 Vb.1) : Type u) :=
              (F.obj (IsFiltered.max Ua.1 Vb.1)).structureData.lieRing
            Gadd.ιColimitType (IsFiltered.max Ua.1 Vb.1)
              (show (F.obj (IsFiltered.max Ua.1 Vb.1) : Type u) from
                ⁅(show (F.obj (IsFiltered.max Ua.1 Vb.1) : Type u) from
                    (F.map (IsFiltered.leftToMax Ua.1 Vb.1)).hom Ua.2),
                  (show (F.obj (IsFiltered.max Ua.1 Vb.1) : Type u) from
                    (F.map (IsFiltered.rightToMax Ua.1 Vb.1)).hom Vb.2)⁆))
          (by
            rintro ⟨U, a⟩ ⟨V₁, b₁⟩ ⟨V₂, b₂⟩
              ⟨f : V₁ ⟶ V₂, rfl : b₂ = Gadd.map f b₁⟩
            obtain ⟨s, α, β, h₁, h₂⟩ :=
              IsFiltered.bowtie (IsFiltered.leftToMax U V₁) (IsFiltered.leftToMax U V₂)
                (IsFiltered.rightToMax U V₁) (f ≫ IsFiltered.rightToMax U V₂)
            refine Gadd.ιColimitType_eq_of_map_eq_map _ _ α β ?_
            change (F.map α).hom ⁅(F.map (IsFiltered.leftToMax U V₁)).hom a,
                (F.map (IsFiltered.rightToMax U V₁)).hom b₁⁆ =
              (F.map β).hom ⁅(F.map (IsFiltered.leftToMax U V₂)).hom a,
                (F.map (IsFiltered.rightToMax U V₂)).hom ((F.map f).hom b₁)⁆
            rw [LieHom.map_lie, LieHom.map_lie]
            simp only [map_comp_apply]
            rw [h₁, h₂])
          (by
            rintro ⟨U₁, a₁⟩ ⟨U₂, a₂⟩ ⟨V, b⟩
              ⟨f : U₁ ⟶ U₂, rfl : a₂ = Gadd.map f a₁⟩
            obtain ⟨s, α, β, h₁, h₂⟩ :=
              IsFiltered.bowtie (IsFiltered.leftToMax U₁ V) (f ≫ IsFiltered.leftToMax U₂ V)
                (IsFiltered.rightToMax U₁ V) (IsFiltered.rightToMax U₂ V)
            refine Gadd.ιColimitType_eq_of_map_eq_map _ _ α β ?_
            change (F.map α).hom ⁅(F.map (IsFiltered.leftToMax U₁ V)).hom a₁,
                (F.map (IsFiltered.rightToMax U₁ V)).hom b⁆ =
              (F.map β).hom ⁅(F.map (IsFiltered.leftToMax U₂ V)).hom ((F.map f).hom a₁),
                (F.map (IsFiltered.rightToMax U₂ V)).hom b⁆
            rw [LieHom.map_lie, LieHom.map_lie]
            simp only [map_comp_apply]
            rw [h₁, h₂])
      let id_hom (X : LieAlgebraCat.{u} K) :
          LieAlgebraCat.Hom.hom (𝟙 X) = LieHom.id := rfl
      have bracket_common (i j s : J) (f : i ⟶ s) (g : j ⟶ s)
          (x : (F.obj i : Type u)) (y : (F.obj j : Type u)) :
          bracketL (ι i x) (ι j y) =
            ι s (show (F.obj s : Type u) from
              letI : LieRing (F.obj s : Type u) := (F.obj s).structureData.lieRing
              ⁅(F.map f).hom x, (F.map g).hom y⁆) := by
        let m := IsFiltered.max i j
        let : LieRing (F.obj m : Type u) := (F.obj m).structureData.lieRing
        let : LieRing (F.obj s : Type u) := (F.obj s).structureData.lieRing
        obtain ⟨t, α, β, h₁, h₂⟩ :=
          IsFiltered.bowtie (IsFiltered.leftToMax i j) f
            (IsFiltered.rightToMax i j) g
        dsimp [bracketL, ι]
        refine Gadd.ιColimitType_eq_of_map_eq_map _ _ α β ?_
        change (F.map α).hom ⁅(F.map (IsFiltered.leftToMax i j)).hom x,
            (F.map (IsFiltered.rightToMax i j)).hom y⁆ =
          (F.map β).hom ⁅(F.map f).hom x, (F.map g).hom y⁆
        rw [LieHom.map_lie, LieHom.map_lie]
        simp only [map_comp_apply]
        rw [h₁, h₂]
      letI : SMul K L := ⟨smulL⟩
      let moduleL : Module K L := by
        exact
          { mul_smul := by
              intro a b x
              obtain ⟨i, x, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
              change ι i ((a * b) • (show (F.obj i : Type u) from x)) =
                ι i (a • b • (show (F.obj i : Type u) from x))
              rw [mul_smul]
            one_smul := by
              intro x
              obtain ⟨i, x, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
              change ι i ((1 : K) • (show (F.obj i : Type u) from x)) = ι i x
              rw [one_smul]
            smul_add := by
              intro a x y
              obtain ⟨i, x, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
              obtain ⟨j, y, rfl⟩ := Gadd.ιColimitType_jointly_surjective y
              obtain ⟨s, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
              let x' : (F.obj s : Type u) := (F.map f).hom x
              let y' : (F.obj s : Type u) := (F.map g).hom y
              let : LieRing (F.obj s : Type u) := (F.obj s).structureData.lieRing
              calc
                smulL a (ι i x + ι j y) = smulL a (ι s (x' + y')) := by
                  rw [add_mk ⟨i, x⟩ ⟨j, y⟩ s f g]
                _ = ι s (a • (x' + y')) := by rw [smul_mk]
                _ = ι s (a • x' + a • y') := by rw [smul_add]
                _ = smulL a (ι i x) + smulL a (ι j y) := by
                  rw [smul_mk, smul_mk]
                  simpa [x', y', map_smul] using
                    (add_mk ⟨i, a • (show (F.obj i : Type u) from x)⟩
                      ⟨j, a • (show (F.obj j : Type u) from y)⟩ s f g).symm
            add_smul := by
              intro a b x
              obtain ⟨i, x, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
              change ι i ((a + b) • (show (F.obj i : Type u) from x)) =
                ι i (a • (show (F.obj i : Type u) from x)) +
                  ι i (b • (show (F.obj i : Type u) from x))
              rw [add_smul]
              simpa [F.map_id, id_hom] using
                (add_mk ⟨i, a • (show (F.obj i : Type u) from x)⟩
                  ⟨i, b • (show (F.obj i : Type u) from x)⟩ i (𝟙 _) (𝟙 _)).symm
            smul_zero := by
              intro a
              let i : J := IsFiltered.nonempty.some
              calc
                smulL a (0 : L) = smulL a (ι i 0) := by rw [zero_mk i]
                _ = ι i (a • (0 : (F.obj i : Type u))) := by rw [smul_mk]
                _ = ι i 0 := by rw [smul_zero]
                _ = 0 := (zero_mk i).symm
            zero_smul := by
              intro x
              obtain ⟨i, x, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
              calc
                smulL 0 (ι i x) =
                    ι i ((0 : K) • (show (F.obj i : Type u) from x)) := by rw [smul_mk]
                _ = ι i 0 := by rw [zero_smul]
                _ = 0 := (zero_mk i).symm }
      letI : Module K L := moduleL
      have add_lie_test :
          ∀ x y z : L, bracketL (x + y) z = bracketL x z + bracketL y z := by
        intro x y z
        obtain ⟨i, a, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
        obtain ⟨j, b, rfl⟩ := Gadd.ιColimitType_jointly_surjective y
        obtain ⟨k, c, rfl⟩ := Gadd.ιColimitType_jointly_surjective z
        obtain ⟨s₁, fᵢ, fⱼ, _⟩ := IsFilteredOrEmpty.cocone_objs i j
        obtain ⟨s, h₁, fₖ, _⟩ := IsFilteredOrEmpty.cocone_objs s₁ k
        let fᵢ' := fᵢ ≫ h₁
        let fⱼ' := fⱼ ≫ h₁
        let a' : (F.obj s : Type u) := (F.map fᵢ').hom a
        let b' : (F.obj s : Type u) := (F.map fⱼ').hom b
        let c' : (F.obj s : Type u) := (F.map fₖ).hom c
        let : LieRing (F.obj s : Type u) := (F.obj s).structureData.lieRing
        calc
          bracketL (ι i a + ι j b) (ι k c) =
              bracketL (ι s (a' + b')) (ι k c) := by
                rw [add_mk ⟨i, a⟩ ⟨j, b⟩ s fᵢ' fⱼ']
          _ = ι s ⁅a' + b', c'⁆ := by
            simpa [a', b', c', fᵢ', fⱼ', id_hom] using
              bracket_common s k s (𝟙 _) fₖ (a' + b') c
          _ = ι s (⁅a', c'⁆ + ⁅b', c'⁆) := by rw [LieRing.add_lie]
          _ = bracketL (ι i a) (ι k c) + bracketL (ι j b) (ι k c) := by
            rw [bracket_common i k s fᵢ' fₖ a c,
              bracket_common j k s fⱼ' fₖ b c]
            simpa [a', b', c', fᵢ', fⱼ', id_hom] using
              (add_mk ⟨s, ⁅a', c'⁆⟩ ⟨s, ⁅b', c'⁆⟩ s (𝟙 _) (𝟙 _)).symm
      have lie_add_test :
          ∀ x y z : L, bracketL x (y + z) = bracketL x y + bracketL x z := by
        intro x y z
        obtain ⟨i, a, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
        obtain ⟨j, b, rfl⟩ := Gadd.ιColimitType_jointly_surjective y
        obtain ⟨k, c, rfl⟩ := Gadd.ιColimitType_jointly_surjective z
        obtain ⟨s₁, fⱼ, fₖ, _⟩ := IsFilteredOrEmpty.cocone_objs j k
        obtain ⟨s, fᵢ, h₁, _⟩ := IsFilteredOrEmpty.cocone_objs i s₁
        let fⱼ' := fⱼ ≫ h₁
        let fₖ' := fₖ ≫ h₁
        let a' : (F.obj s : Type u) := (F.map fᵢ).hom a
        let b' : (F.obj s : Type u) := (F.map fⱼ').hom b
        let c' : (F.obj s : Type u) := (F.map fₖ').hom c
        let : LieRing (F.obj s : Type u) := (F.obj s).structureData.lieRing
        calc
          bracketL (ι i a) (ι j b + ι k c) =
              bracketL (ι i a) (ι s (b' + c')) := by
                rw [add_mk ⟨j, b⟩ ⟨k, c⟩ s fⱼ' fₖ']
          _ = ι s ⁅a', b' + c'⁆ := by
            simpa [a', b', c', fⱼ', fₖ', id_hom] using
              bracket_common i s s fᵢ (𝟙 _) a (b' + c')
          _ = ι s (⁅a', b'⁆ + ⁅a', c'⁆) := by rw [LieRing.lie_add]
          _ = bracketL (ι i a) (ι j b) + bracketL (ι i a) (ι k c) := by
            rw [bracket_common i j s fᵢ fⱼ' a b,
              bracket_common i k s fᵢ fₖ' a c]
            simpa [a', b', c', fⱼ', fₖ', id_hom] using
              (add_mk ⟨s, ⁅a', b'⁆⟩ ⟨s, ⁅a', c'⁆⟩ s (𝟙 _) (𝟙 _)).symm
      have lie_self_test : ∀ x : L, bracketL x x = 0 := by
        intro x
        obtain ⟨i, a, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
        let : LieRing (F.obj i : Type u) := (F.obj i).structureData.lieRing
        calc
          bracketL (ι i a) (ι i a) =
              ι i (show (F.obj i : Type u) from
                ⁅(show (F.obj i : Type u) from a), (show (F.obj i : Type u) from a)⁆) := by
            simpa [id_hom] using
              bracket_common i i i (𝟙 _) (𝟙 _) a a
          _ = 0 := by
            rw [LieRing.lie_self]
            exact (zero_mk i).symm
      have leibniz_lie_test :
          ∀ x y z : L,
            bracketL x (bracketL y z) =
              bracketL (bracketL x y) z + bracketL y (bracketL x z) := by
        intro x y z
        obtain ⟨i, a, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
        obtain ⟨j, b, rfl⟩ := Gadd.ιColimitType_jointly_surjective y
        obtain ⟨k, c, rfl⟩ := Gadd.ιColimitType_jointly_surjective z
        obtain ⟨s₁, fᵢ, fⱼ, _⟩ := IsFilteredOrEmpty.cocone_objs i j
        obtain ⟨s, h₁, fₖ, _⟩ := IsFilteredOrEmpty.cocone_objs s₁ k
        let fᵢ' := fᵢ ≫ h₁
        let fⱼ' := fⱼ ≫ h₁
        let a' : (F.obj s : Type u) := (F.map fᵢ').hom a
        let b' : (F.obj s : Type u) := (F.map fⱼ').hom b
        let c' : (F.obj s : Type u) := (F.map fₖ).hom c
        let : LieRing (F.obj s : Type u) := (F.obj s).structureData.lieRing
        calc
          bracketL (ι i a) (bracketL (ι j b) (ι k c)) =
              bracketL (ι i a) (ι s ⁅b', c'⁆) := by
                rw [bracket_common j k s fⱼ' fₖ b c]
          _ = ι s ⁅a', ⁅b', c'⁆⁆ := by
            simpa [a', b', c', fᵢ', id_hom] using
              bracket_common i s s fᵢ' (𝟙 _) a ⁅b', c'⁆
          _ = ι s (⁅⁅a', b'⁆, c'⁆ + ⁅b', ⁅a', c'⁆⁆) := by
            rw [LieRing.leibniz_lie]
          _ = bracketL (bracketL (ι i a) (ι j b)) (ι k c) +
              bracketL (ι j b) (bracketL (ι i a) (ι k c)) := by
            calc
              ι s (⁅⁅a', b'⁆, c'⁆ + ⁅b', ⁅a', c'⁆⁆) =
                  ι s ⁅⁅a', b'⁆, c'⁆ + ι s ⁅b', ⁅a', c'⁆⁆ := by
                    simpa [F.map_id, id_hom] using (add_mk
                      ⟨s, (show (F.obj s : Type u) from ⁅⁅a', b'⁆, c'⁆)⟩
                      ⟨s, (show (F.obj s : Type u) from ⁅b', ⁅a', c'⁆⁆)⟩
                      s (𝟙 _) (𝟙 _)).symm
              _ = bracketL (ι s ⁅a', b'⁆) (ι k c) +
                    bracketL (ι j b) (ι s ⁅a', c'⁆) := by
                rw [bracket_common s k s (𝟙 _) fₖ ⁅a', b'⁆ c,
                  bracket_common j s s fⱼ' (𝟙 _) b ⁅a', c'⁆]
                simp [a', b', c', id_hom]
              _ = bracketL (bracketL (ι i a) (ι j b)) (ι k c) +
                    bracketL (ι j b) (bracketL (ι i a) (ι k c)) := by
                rw [bracket_common i j s fᵢ' fⱼ' a b,
                  bracket_common i k s fᵢ' fₖ a c]
      let lieRingL : LieRing L := by
        letI : Bracket L L := ⟨bracketL⟩
        exact
          { add_lie := add_lie_test
            lie_add := lie_add_test
            lie_self := lie_self_test
            leibniz_lie := leibniz_lie_test }
      letI : LieRing L := lieRingL
      letI : Bracket L L := ⟨bracketL⟩
      have lie_smul_test :
          ∀ (a : K) (x y : L), bracketL x (smulL a y) = smulL a (bracketL x y) := by
        intro a x y
        obtain ⟨i, x, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
        obtain ⟨j, y, rfl⟩ := Gadd.ιColimitType_jointly_surjective y
        obtain ⟨s, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
        let x' : (F.obj s : Type u) := (F.map f).hom x
        let y' : (F.obj s : Type u) := (F.map g).hom y
        let : LieRing (F.obj s : Type u) := (F.obj s).structureData.lieRing
        let : LieAlgebra K (F.obj s : Type u) := (F.obj s).structureData.lieAlgebra
        calc
          bracketL (ι i x) (smulL a (ι j y)) =
              bracketL (ι i x) (ι j (a • (show (F.obj j : Type u) from y))) := by
                rw [smul_mk]
          _ = ι s ⁅x', (F.map g).hom (a • (show (F.obj j : Type u) from y))⁆ := by
            simpa [x', y'] using
              bracket_common i j s f g x (a • (show (F.obj j : Type u) from y))
          _ = ι s (a • ⁅x', y'⁆) := by
            rw [map_smul, LieAlgebra.lie_smul]
          _ = smulL a (ι s ⁅x', y'⁆) := by rw [smul_mk]
          _ = smulL a (bracketL (ι i x) (ι j y)) := by
            rw [bracket_common i j s f g x y]
      let lieAlgebraL : LieAlgebra K L := by
        exact
          { lie_smul := by
              intro a x y
              change bracketL x (smulL a y) = smulL a (bracketL x y)
              exact lie_smul_test a x y }
      letI : LieAlgebra K L := lieAlgebraL
      let P : LieAlgebraCat.{u} K := LieAlgebraCat.of L
      let p : ∀ j, F.obj j ⟶ P := fun j =>
        { hom :=
            { toLinearMap :=
                { toFun := fun x => ι j x
                  map_add' := by
                    intro x y
                    change ι j (x + y) = ι j x + ι j y
                    simpa [F.map_id, id_hom] using
                      (add_mk ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)).symm
                  map_smul' := by
                    intro a x
                    exact (smul_mk a j x).symm }
              map_lie' := by
                intro x y
                change ι j (show (F.obj j : Type u) from ⁅x, y⁆) =
                  bracketL (ι j x) (ι j y)
                simpa [id_hom] using
                  (bracket_common j j j (𝟙 _) (𝟙 _) x y).symm } }
      let c : Cocone F :=
        { pt := P
          ι :=
            { app := p
              naturality := by
                intro i j f
                apply LieAlgebraCat.Hom.ext
                apply LieHom.ext
                intro x
                change ι j ((F.map f).hom x) = ι i x
                exact Gadd.ιColimitType_map f x } }
      let l : ∀ s : Cocone F, P ⟶ s.pt := fun s =>
        let dC : Gadd.CoconeTypes :=
          { pt := (s.pt : Type u)
            ι := fun j => (s.ι.app j).hom
            ι_naturality := by
              intro i j f
              funext x
              exact ConcreteCategory.congr_hom (s.ι.naturality f) x }
        let d : L → (s.pt : Type u) := Gadd.descColimitType dC
        have hd (j : J) (x : (F.obj j : Type u)) :
            d (ι j x) = (s.ι.app j).hom x := by
          rfl
        { hom :=
            { toLinearMap :=
                { toFun := d
                  map_add' := by
                    intro x y
                    obtain ⟨i, a, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
                    obtain ⟨j, b, rfl⟩ := Gadd.ιColimitType_jointly_surjective y
                    obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
                    change d (ι i a + ι j b) = d (ι i a) + d (ι j b)
                    rw [add_mk ⟨i, a⟩ ⟨j, b⟩ k f g, hd, hd, hd]
                    rw [map_add]
                    have hf := ConcreteCategory.congr_hom (s.ι.naturality f) a
                    have hg := ConcreteCategory.congr_hom (s.ι.naturality g) b
                    change (s.ι.app k).hom ((F.map f).hom a) =
                      (s.ι.app i).hom a at hf
                    change (s.ι.app k).hom ((F.map g).hom b) =
                      (s.ι.app j).hom b at hg
                    rw [hf, hg]
                  map_smul' := by
                    intro a x
                    obtain ⟨i, x, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
                    change d (smulL a (ι i x)) = a • d (ι i x)
                    rw [smul_mk, hd]
                    exact (s.ι.app i).hom.map_smul a x }
              map_lie' := by
                intro x y
                obtain ⟨i, x, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
                obtain ⟨j, y, rfl⟩ := Gadd.ιColimitType_jointly_surjective y
                obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
                change d (bracketL (ι i x) (ι j y)) =
                  ⁅d (ι i x), d (ι j y)⁆
                rw [bracket_common i j k f g x y, hd, hd, hd]
                rw [LieHom.map_lie]
                have hf := ConcreteCategory.congr_hom (s.ι.naturality f) x
                have hg := ConcreteCategory.congr_hom (s.ι.naturality g) y
                change (s.ι.app k).hom ((F.map f).hom x) =
                  (s.ι.app i).hom x at hf
                change (s.ι.app k).hom ((F.map g).hom y) =
                  (s.ι.app j).hom y at hg
                rw [hf, hg] } }
      let hc : IsColimit c :=
        { desc := l
          fac := by
            intro s j
            apply LieAlgebraCat.Hom.ext
            apply LieHom.ext
            intro x
            dsimp [l]
            rfl
          uniq := by
            intro s m hm
            apply LieAlgebraCat.Hom.ext
            apply LieHom.ext
            intro x
            obtain ⟨j, x, rfl⟩ := Gadd.ιColimitType_jointly_surjective x
            have h := ConcreteCategory.congr_hom (hm j) x
            change m.hom (ι j x) = (s.ι.app j).hom x at h
            calc
              m.hom (ι j x) = (s.ι.app j).hom x := h
              _ = (l s).hom (ι j x) := by
                dsimp [l]
                rfl }
      have hG :
          IsColimit ((forget (LieAlgebraCat.{u} K)).mapCocone c) := by
        apply IsColimit.ofIsoColimit (Types.TypeMax.colimitCoconeIsColimit Gadd)
        exact Cocone.ext (Iso.refl _) (by intro j; rfl)
      exact ⟨c, hc, hG⟩
    let lieFiltered : HasFilteredColimitsOfSize.{u, u} (LieAlgebraCat.{u} K) := by
      refine ⟨fun J => ?_⟩
      refine ⟨fun F => ?_⟩
      exact ⟨⟨(lieColimitData J F).1, (lieColimitData J F).2.1⟩⟩
    let liePreservesFiltered :
        PreservesFilteredColimitsOfSize.{u, u}
          (forget (LieAlgebraCat.{u} K)) := by
      refine ⟨fun J => ?_⟩
      refine ⟨?_⟩
      intro F
      exact preservesColimit_of_preserves_colimit_cocone
        (lieColimitData J F).2.1 (lieColimitData J F).2.2
    let : HasFilteredColimitsOfSize.{u, u} (LieAlgebraCat.{u} K) := lieFiltered
    let : PreservesFilteredColimitsOfSize.{u, u}
        (forget (LieAlgebraCat.{u} K)) := liePreservesFiltered
    let lieReflectsIso :
        (forget (LieAlgebraCat.{u} K)).ReflectsIsomorphisms := by
      refine ⟨?_⟩
      intro X Y f hu
      let u := (forget (LieAlgebraCat.{u} K)).map f
      let : IsIso u := hu
      have hbij : Function.Bijective f.hom := by
        change Function.Bijective u
        exact ConcreteCategory.bijective_of_isIso u
      let e : (X : Type u) ≃ₗ⁅K⁆ (Y : Type u) :=
        LieEquiv.ofBijective f.hom hbij
      let g : Y ⟶ X := { hom := e.symm }
      refine ⟨⟨g, ?_, ?_⟩⟩
      · apply LieAlgebraCat.Hom.ext
        apply LieHom.ext
        intro x
        change e.symm (e x) = x
        exact e.symm_apply_apply x
      · apply LieAlgebraCat.Hom.ext
        apply LieHom.ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y
    let : (forget (LieAlgebraCat.{u} K)).ReflectsIsomorphisms := lieReflectsIso
    exact ⟨⟩

/-! ## Consequences of the definition -/

/-- The source's terminal-object, product, pullback, equalizer, mono, epi,
and filtered-colimit consequences of being an algebraic structure type. -/
structure AlgebraicStructureProperties
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] : Prop where
  /-- A terminal object has a singleton underlying set. -/
  terminal :
    ∃ (zero : C), Nonempty (IsTerminal zero) ∧
      Nonempty (F.obj zero) ∧ Subsingleton (F.obj zero)
  /-- Products are computed by products of underlying sets. -/
  products :
    ∀ {ι : Type v} (A : ι → C),
      Nonempty
        (F.obj (limit (Discrete.functor A)) ≅
          limit (Discrete.functor (fun i => F.obj (A i))))
  /-- Fibre products are computed by fibre products of underlying sets. -/
  fibreProducts :
    ∀ {A B C' : C} (f : A ⟶ B) (g : C' ⟶ B),
      Nonempty
        (F.obj (pullback f g) ≅ pullback (F.map f) (F.map g))
  /-- Equalizers are computed by equalizers of underlying sets. -/
  equalizers :
    ∀ {A B : C} (f g : A ⟶ B),
      Nonempty (IsLimit (F.mapCone (limit.cone (parallelPair f g))))
  /-- Monomorphisms are exactly the morphisms injective on underlying sets. -/
  monomorphisms :
    ∀ {A B : C} (f : A ⟶ B),
      Mono f ↔ Function.Injective (F.map f)
  /-- Surjectivity on underlying sets implies categorical epimorphy. -/
  epimorphisms :
    ∀ {A B : C} (f : A ⟶ B),
      Function.Surjective (F.map f) → Epi f
  /-- Filtered colimits are computed by filtered colimits of underlying sets. -/
  filteredColimits :
    ∀ {J : Type v} [Category.{v} J] [IsFiltered J] (D : J ⥤ C),
      Nonempty
        (F.obj (colimit D) ≅ colimit (D ⋙ F))

/-- The structural properties lemma from the source. -/
theorem algebraicStructureType_properties {C : Type u} [Category.{v} C]
    {F : C ⥤ Type v} [AlgebraicStructureType C F] :
    AlgebraicStructureProperties (C := C) (F := F) := by
  exact
    { terminal := by
        refine ⟨limit (Functor.empty C), ?_⟩
        refine ⟨⟨(isLimitEquivIsTerminalOfIsEmpty C (limit.cone (Functor.empty C))).toFun
          (limit.isLimit _)⟩, ?_⟩
        let hFz : IsTerminal (F.obj (limit (Functor.empty C))) :=
          (isLimitEquivIsTerminalOfIsEmpty (Type v)
            (F.mapCone (limit.cone (Functor.empty C)))).toFun
            (isLimitOfPreserves F (limit.isLimit _))
        let hUnique : Unique (F.obj (limit (Functor.empty C))) :=
          (Types.isTerminalEquivUnique _).toFun hFz
        exact ⟨⟨hUnique.default⟩,
          ⟨fun a b => (hUnique.uniq a).trans (hUnique.uniq b).symm⟩⟩
      products := by
        intro ι A
        exact ⟨(preservesLimitIso F (Discrete.functor A)).trans
          (HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete A F))⟩
      fibreProducts := by
        intro A B C' f g
        exact ⟨(preservesLimitIso F (cospan f g)).trans
          (HasLimit.isoOfNatIso (diagramIsoCospan (cospan f g ⋙ F)))⟩
      equalizers := by
        intro A B f g
        exact ⟨isLimitOfPreserves F (limit.isLimit _)⟩
      monomorphisms := by
        intro A B f
        constructor
        · intro hf
          exact (mono_iff_injective (F.map f)).1
            (@Functor.map_mono _ _ _ _ F _ _ _ f hf)
        · intro hf
          let hReflectsLimits : ReflectsLimitsOfShape WalkingCospan F :=
            reflectsLimitsOfShape_of_reflectsIsomorphisms
          let hReflectsMonomorphisms : F.ReflectsMonomorphisms :=
            @reflectsMonomorphisms_of_reflectsLimitsOfShape _ _ _ _ F hReflectsLimits
          exact @Functor.mono_of_mono_map _ _ _ _ F hReflectsMonomorphisms _ _ f
            ((mono_iff_injective (F.map f)).2 hf)
      epimorphisms := by
        intro A B f hf
        exact Functor.epi_of_epi_map F ((epi_iff_surjective (F.map f)).2 hf)
      filteredColimits := by
        intro J _ _ D
        exact ⟨preservesColimitIso F D⟩ }

/-! ## Image containment and factorization -/

/-- An underlying image containment through an underlying injection lifts to a
factorization in the category of algebraic structures. -/
theorem factor_through_of_image_subset
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F]
    {A B C' : C} (f : A ⟶ B) (g : C' ⟶ B)
    (hg : Function.Injective (F.map g))
    (himage : Set.range (F.map f) ⊆ Set.range (F.map g)) :
    ∃ t : A ⟶ C', t ≫ g = f := by
  let hP := Functor.map_isPullback F (IsPullback.of_hasPullback f g)
  have hbij : Function.Bijective (F.map (pullback.fst f g)) := by
    constructor
    · intro x y hxy
      apply PullbackCone.IsLimit.type_ext hP.isLimit
      · exact hxy
      · apply hg
        have hx := congrArg (fun k => k x) (congrArg F.map (pullback.condition))
        have hy := congrArg (fun k => k y) (congrArg F.map (pullback.condition))
        change (F.map g) ((F.map (pullback.snd f g)) x) =
          (F.map g) ((F.map (pullback.snd f g)) y)
        calc
          (F.map g) ((F.map (pullback.snd f g)) x) =
              (F.map f) ((F.map (pullback.fst f g)) x) := by
            simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hx.symm
          _ = (F.map f) ((F.map (pullback.fst f g)) y) := congrArg (F.map f) hxy
          _ = (F.map g) ((F.map (pullback.snd f g)) y) := by
            simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hy
    · intro a
      obtain ⟨b, hb⟩ := himage ⟨a, rfl⟩
      let z : Types.PullbackObj (F.map f) (F.map g) :=
        ⟨⟨a, b⟩, hb.symm⟩
      refine ⟨(PullbackCone.IsLimit.equivPullbackObj hP.isLimit).symm z, ?_⟩
      change (F.map (pullback.fst f g))
          ((PullbackCone.IsLimit.equivPullbackObj hP.isLimit).symm z) = z.1.1
      exact PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst hP.isLimit z
  let hMap : IsIso (F.map (pullback.fst f g)) := (isIso_iff_bijective _).2 hbij
  let hPullback : IsIso (pullback.fst f g) :=
    @isIso_of_reflects_iso _ _ _ _ _ _ (pullback.fst f g) F hMap inferInstance
  refine ⟨@inv _ _ _ _ (pullback.fst f g) hPullback ≫ pullback.snd f g, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    @IsIso.inv_hom_id _ _ _ _ (pullback.fst f g) hPullback, Category.id_comp]

/-! ## The commutative-square application -/

/-- The source's diagrammatic application of the image-containment lemma. -/
theorem exists_square_lift
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F]
    {A B C' D : C} (f : A ⟶ B) (g : B ⟶ D) (h : C' ⟶ D)
    (hh : Function.Injective (F.map h))
    (himage : Set.range (F.map (f ≫ g)) ⊆ Set.range (F.map h)) :
    ∃ k : A ⟶ C', k ≫ h = f ≫ g := by
  exact factor_through_of_image_subset (f ≫ g) h hh himage

/-! ## Pointwise products on a space -/

/-- The product object indexed by the points of an open. -/
noncomputable abbrev pointwiseProductObject
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) (U : Opens X) : C :=
  limit (Discrete.functor (fun x : U => A x))

/-- Restriction of a pointwise product along an inclusion of opens. -/
noncomputable def pointwiseProductRestriction
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) {U V : Opens X} (h : V ≤ U) :
    pointwiseProductObject (F := F) A U ⟶ pointwiseProductObject (F := F) A V :=
  limit.lift (Discrete.functor (fun x : V => A x))
    (Fan.mk _ fun x =>
        limit.π (Discrete.functor (fun x : U => A x))
        (Discrete.mk ⟨x, h x.property⟩))

theorem pointwiseProductRestriction_π
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) {U V : Opens X} (h : V ≤ U) (x : Discrete V) :
    pointwiseProductRestriction (F := F) A h ≫
        limit.π (Discrete.functor (fun x : V => A x)) x =
      limit.π (Discrete.functor (fun x : U => A x))
        (Discrete.mk ⟨x.as, h x.as.property⟩) := by
  unfold pointwiseProductRestriction pointwiseProductObject
  rw [limit.lift_π]
  rfl

/-- The category-valued pointwise product presheaf `U ↦ ∏ x ∈ U, A x`. -/
def pointwiseProductPresheaf
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) : TopCat.Presheaf C X where
  obj U := pointwiseProductObject (F := F) A U.unop
  map {U V} f := pointwiseProductRestriction (F := F) A f.unop.le
  map_id U := by
    unfold pointwiseProductObject
    apply (limit.isLimit _).hom_ext
    intro x
    rw [limit.cone_π]
    rw [pointwiseProductRestriction_π]
    simp
  map_comp f g := by
    unfold pointwiseProductObject
    apply (limit.isLimit _).hom_ext
    intro x
    rw [limit.cone_π]
    rw [Category.assoc, pointwiseProductRestriction_π,
      pointwiseProductRestriction_π, pointwiseProductRestriction_π]

@[simp]
theorem pointwiseProductPresheaf_obj
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) (U : Opens X) :
    (pointwiseProductPresheaf (F := F) A).obj (op U) =
      pointwiseProductObject (F := F) A U :=
  rfl

/-- The underlying pointwise product has the expected product of underlying
sets on every open. -/
theorem pointwiseProductPresheaf_underlying_sections
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) (U : Opens X) :
    Nonempty
      (F.obj (pointwiseProductObject (F := F) A U) ≃
        ∀ x : U, F.obj (A x)) := by
  exact ⟨((preservesLimitIso F (Discrete.functor (fun x : U => A x))).trans
    (HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete (fun x : U => A x) F))).trans
      (Types.productIso (F.obj ∘ fun x : U => A x)) |>.toEquiv⟩

/-- A category-valued presheaf is a sheaf of algebraic structures in the
category-valued equalizer-of-products sense from Chapter 9. -/
abbrev IsSheafOfAlgebraicStructures
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (𝒜 : TopCat.Presheaf C X) : Prop :=
  CategoryValuedSheaf 𝒜

/-- For a type of algebraic structures, the category-valued sheaf condition
is equivalent to the sheaf condition on the underlying presheaf of sets. -/
theorem isSheafOfAlgebraicStructures_iff_underlying_isSheaf
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (𝒜 : TopCat.Presheaf C X) :
    IsSheafOfAlgebraicStructures (F := F) 𝒜 ↔
      TopCat.Presheaf.IsSheaf (underlyingPresheaf F 𝒜) := by
  exact categoryValuedSheaf_iff_underlying_isSheaf F 𝒜

/-- The underlying presheaf of the pointwise product is a sheaf of sets,
matching the pointwise-product example from the preceding sheaf section. -/
theorem pointwiseProductPresheaf_underlying_isSheaf
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) :
    TopCat.Presheaf.IsSheaf
      (underlyingPresheaf F (pointwiseProductPresheaf (F := F) A)) := by
  let sectionIso (U : Opens X) :
      F.obj (pointwiseProductObject (F := F) A U) ≅
        ∀ x : U, F.obj (A x) :=
    ((preservesLimitIso F (Discrete.functor (fun x : U => A x))).trans
      (HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete (fun x : U => A x) F))).trans
        (Types.productIso (F.obj ∘ fun x : U => A x))
  let e : underlyingPresheaf F (pointwiseProductPresheaf (F := F) A) ≅
      TopCat.presheafToTypes X (fun x => F.obj (A x)) := by
    refine NatIso.ofComponents (fun U => sectionIso U.unop) ?_
    intro U V i
    change F.map (pointwiseProductRestriction (F := F) A i.unop.le) ≫
        (sectionIso V.unop).hom =
      (sectionIso U.unop).hom ≫
        (TopCat.presheafToTypes X (fun x => F.obj (A x))).map i
    apply ConcreteCategory.hom_ext
    intro s
    funext x
    change (F.map (pointwiseProductRestriction (F := F) A i.unop.le) ≫
        (sectionIso V.unop).hom ≫ (↾fun z => z x)) s =
      ((sectionIso U.unop).hom ≫
        (TopCat.presheafToTypes X (fun x => F.obj (A x))).map i ≫
          (↾fun z => z x)) s
    apply ConcreteCategory.congr_hom
    simp [sectionIso, TopCat.presheafToTypes, Category.assoc,
      Types.productIso_hom_comp_eval, ← Functor.map_comp,
      pointwiseProductRestriction_π]
    have htarget :
        (↾fun g : (∀ y : U.unop, F.obj (A y)) =>
          (fun y : V.unop => g (i.unop y))) ≫
          (↾fun z : (∀ y : V.unop, F.obj (A y)) => z x) =
          (↾fun g : (∀ y : U.unop, F.obj (A y)) => g (i.unop x)) := by
      ext g
      rfl
    rw [htarget, Types.productIso_hom_comp_eval]
    rw [HasLimit.isoOfNatIso_hom_π, preservesLimitIso_hom_π_assoc]
    simp
    congr 1
  exact TopCat.Presheaf.isSheaf_of_iso e.symm
    (TopCat.Presheaf.toTypes_isSheaf X (fun x => F.obj (A x)))

/-- The pointwise product presheaf is a sheaf of algebraic structures. -/
theorem pointwiseProductPresheaf_isSheaf
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) :
    IsSheafOfAlgebraicStructures (F := F)
      (pointwiseProductPresheaf (F := F) A) := by
  exact (isSheafOfAlgebraicStructures_iff_underlying_isSheaf
    (F := F) (pointwiseProductPresheaf (F := F) A)).2
    (pointwiseProductPresheaf_underlying_isSheaf (F := F) A)

end

end Formalization.Books.Sheaves.Unit15
