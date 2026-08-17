import Formalization.Books.Categories.Unit19.FilteredColimits
import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Colimit.Module
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.Homology
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Commutative Algebra, Chapter 8: Colimits

This file formalizes the precise definitions, constructions, examples, and
exactness statements in the `Colimits` section of `books/algebra.tex`.
Systems of modules are represented by the existing functor category over a
preorder; the explicit quotient models use Mathlib's direct-sum and directed
colimit constructions.
-/

namespace Formalization.Books.Algebra.Unit08

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21

universe u v w v' w'

noncomputable section

variable {R : Type u} [CommRing R] {I : Type v} [Preorder I]

/-! ## Systems of modules and the general colimit quotient -/

/-- A system of `R`-modules over a preorder, represented by the canonical
functor from the associated preorder category. -/
abbrev ModuleSystem (R : Type u) [CommRing R] (I : Type v) [Preorder I] :=
  I ⥤ ModuleCat.{max v w} R

/-- The transition linear map attached to a morphism in a module system. -/
def moduleSystemMap (M : ModuleSystem R I) {i j : I} (h : i ≤ j) :
    (M.obj i : Type (max v w)) →ₗ[R] (M.obj j : Type (max v w)) :=
  (M.map (homOfLE h)).hom

/- The identity and composition requirements in the source definition are
   precisely `Functor.map_id` and `Functor.map_comp` for `M`. -/
theorem moduleSystemMap_id (M : ModuleSystem R I) (i : I)
    (x : (M.obj i : Type (max v w))) :
    moduleSystemMap M (le_refl i) x = x := by
  simp [moduleSystemMap]

theorem moduleSystemMap_comp (M : ModuleSystem R I) {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) (x : (M.obj i : Type (max v w))) :
    moduleSystemMap M hjk (moduleSystemMap M hij x) =
      moduleSystemMap M (hij.trans hjk) x := by
  simp [moduleSystemMap, ← ModuleCat.comp_apply, ← M.map_comp, homOfLE_comp]

/-- The categorical colimit of a module system. -/
abbrev moduleSystemColimit (M : ModuleSystem R I) : ModuleCat.{max v w} R :=
  colimit M

/- The direct sum of the stages and its canonical inclusions. -/
abbrev moduleColimitDirectSum (M : ModuleSystem R I) :=
  DirectSum I (fun i => (M.obj i : Type (max v w)))

noncomputable def moduleColimitDirectSumInclusion (M : ModuleSystem R I) (i : I) :
    (M.obj i : Type (max v w)) →ₗ[R] moduleColimitDirectSum M := by
  classical
  exact DirectSum.lof R I (fun i => (M.obj i : Type (max v w))) i

/- The relation generators in the source's quotient presentation. -/
def moduleColimitRelationSet (M : ModuleSystem R I) :
    Set (moduleColimitDirectSum M) :=
  {x | ∃ (i j : I) (h : i ≤ j) (m : (M.obj i : Type (max v w))),
    x = moduleColimitDirectSumInclusion M i m -
      moduleColimitDirectSumInclusion M j (moduleSystemMap M h m)}

def moduleColimitRelations (M : ModuleSystem R I) :
    Submodule R (moduleColimitDirectSum M) :=
  Submodule.span R (moduleColimitRelationSet M)

/-- The quotient module in the direct-sum presentation of the colimit. -/
abbrev moduleColimitQuotient (M : ModuleSystem R I) :=
  moduleColimitDirectSum M ⧸ moduleColimitRelations M

/-- The projection from the direct sum to the quotient presentation. -/
def moduleColimitProjection (M : ModuleSystem R I) :
    moduleColimitDirectSum M →ₗ[R] moduleColimitQuotient M :=
  (moduleColimitRelations M).mkQ

/-- The canonical map from a stage into the quotient presentation. -/
def moduleColimitQuotientInclusion (M : ModuleSystem R I) (i : I) :
    (M.obj i : Type (max v w)) →ₗ[R] moduleColimitQuotient M :=
  (moduleColimitProjection M).comp (moduleColimitDirectSumInclusion M i)

/- This is the source's assertion that the relation generators vanish and that
   the maps from stages form a cocone. -/
theorem moduleColimitQuotient_relation_generator_eq_zero
    (M : ModuleSystem R I) {i j : I} (h : i ≤ j)
    (m : (M.obj i : Type (max v w))) :
    moduleColimitProjection M
        (moduleColimitDirectSumInclusion M i m -
          moduleColimitDirectSumInclusion M j (moduleSystemMap M h m)) = 0 := by
  rw [moduleColimitProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨i, j, h, m, rfl⟩

theorem moduleColimitQuotientInclusion_compatibility
    (M : ModuleSystem R I) {i j : I} (h : i ≤ j) :
    (moduleColimitQuotientInclusion M j).comp (moduleSystemMap M h) =
      moduleColimitQuotientInclusion M i := by
  ext m
  have hz := moduleColimitQuotient_relation_generator_eq_zero M h m
  rw [map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

/- The quotient maps form the cocone displayed in the source. -/
def moduleColimitQuotientCocone (M : ModuleSystem R I) : Cocone M where
  pt := ModuleCat.of R (moduleColimitQuotient M)
  ι :=
    { app := fun i => ModuleCat.ofHom (moduleColimitQuotientInclusion M i)
      naturality := by
        intro i j h
        ext x
        exact congrArg (fun f => f x)
          (moduleColimitQuotientInclusion_compatibility M h.le) }

/- The direct-sum quotient is canonically the categorical colimit. -/
theorem moduleColimitQuotient_is_colimit_exists
    (M : ModuleSystem R I) :
    Nonempty (IsColimit (moduleColimitQuotientCocone M)) := by
  classical
  let desc (s : Cocone M) : (moduleColimitQuotientCocone M).pt ⟶ s.pt := by
    let f := DirectSum.toModule R I s.pt
      (fun i => (s.ι.app i).hom)
    have hf : moduleColimitRelations M ≤ LinearMap.ker f := by
      apply Submodule.span_le.2
      rintro z ⟨i, j, h, m, rfl⟩
      change f (moduleColimitDirectSumInclusion M i m -
        moduleColimitDirectSumInclusion M j (moduleSystemMap M h m)) = 0
      have hs :
          (s.ι.app j).hom (moduleSystemMap M h m) =
            (s.ι.app i).hom m := by
        simp [moduleSystemMap]
      rw [map_sub]
      simpa [f, moduleColimitDirectSumInclusion, DirectSum.toModule_lof] using
        sub_eq_zero.mpr hs.symm
    exact ModuleCat.ofHom ((moduleColimitRelations M).liftQ f hf)
  have desc_proj (s : Cocone M) :
      (desc s).hom.comp (moduleColimitProjection M) =
        DirectSum.toModule R I s.pt (fun i => (s.ι.app i).hom) := by
    dsimp [desc, moduleColimitProjection]
    exact Submodule.liftQ_mkQ (moduleColimitRelations M)
      (DirectSum.toModule R I s.pt (fun i => (s.ι.app i).hom)) _
  refine ⟨{
    desc := fun s => desc s
    fac := fun s i => by
      apply ModuleCat.hom_ext
      change (desc s).hom.comp (moduleColimitQuotientInclusion M i) =
        (s.ι.app i).hom
      ext m
      change (desc s).hom (moduleColimitProjection M
        (moduleColimitDirectSumInclusion M i m)) = (s.ι.app i).hom m
      have h := congrArg (fun f => f (moduleColimitDirectSumInclusion M i m))
        (desc_proj s)
      rw [show (desc s).hom.comp (moduleColimitProjection M)
          (moduleColimitDirectSumInclusion M i m) =
          (desc s).hom (moduleColimitProjection M
            (moduleColimitDirectSumInclusion M i m)) by rfl] at h
      rw [h]
      simp [moduleColimitDirectSumInclusion, DirectSum.toModule_lof]
    uniq := fun s g hg => by
      apply ModuleCat.hom_ext
      apply Submodule.quot_hom_ext
      intro z
      have hz :
          g.hom.comp (moduleColimitProjection M) =
            DirectSum.toModule R I s.pt
              (fun i => (s.ι.app i).hom) := by
        dsimp [moduleColimitQuotientCocone]
        apply DirectSum.linearMap_ext
        intro i
        have hi := congrArg (fun q => q.hom) (hg i)
        dsimp [moduleColimitQuotientCocone] at hi
        change g.hom.comp (moduleColimitQuotientInclusion M i) =
          (s.ι.app i).hom at hi
        have hleft :
            (g.hom.comp (moduleColimitProjection M)).comp
                (moduleColimitDirectSumInclusion M i) =
              (s.ι.app i).hom := by
          apply LinearMap.ext
          intro m
          have him := congrArg (fun f => f m) hi
          dsimp [moduleColimitQuotientInclusion] at him
          change g.hom (moduleColimitProjection M
            (moduleColimitDirectSumInclusion M i m)) =
            (s.ι.app i).hom m at him
          calc
            ((g.hom.comp (moduleColimitProjection M)).comp
                (moduleColimitDirectSumInclusion M i)) m =
              g.hom (moduleColimitProjection M
                (moduleColimitDirectSumInclusion M i m)) := rfl
            _ = (s.ι.app i).hom m := him
        have hright :
            (DirectSum.toModule R I s.pt (fun i => (s.ι.app i).hom)).comp
                (moduleColimitDirectSumInclusion M i) =
              (s.ι.app i).hom := by
          ext m
          calc
            ((DirectSum.toModule R I s.pt (fun i => (s.ι.app i).hom)).comp
                (moduleColimitDirectSumInclusion M i)) m =
              DirectSum.toModule R I s.pt (fun i => (s.ι.app i).hom)
                (moduleColimitDirectSumInclusion M i m) := rfl
            _ = (s.ι.app i).hom m := by
              simp [moduleColimitDirectSumInclusion]
        exact hleft.trans hright.symm
      change g.hom (moduleColimitProjection M z) =
        (desc s).hom (moduleColimitProjection M z)
      exact LinearMap.congr_fun (hz.trans (desc_proj s).symm) z }⟩

noncomputable def moduleColimitQuotient_is_colimit
    (M : ModuleSystem R I) :
    IsColimit (moduleColimitQuotientCocone M) :=
  (moduleColimitQuotient_is_colimit_exists M).some

/-! ## Directed colimits -/

instance moduleSystemDirectedSystem (M : ModuleSystem R I) :
    DirectedSystem (fun i => (M.obj i : Type (max v w)))
      (fun _i _j h => moduleSystemMap M h) where
  map_self := by
    intro i x
    exact moduleSystemMap_id M i x
  map_map := by
    intro i j k hij hjk x
    exact moduleSystemMap_comp M hij hjk x

/-- The directed colimit as Mathlib's direct-sum quotient. -/
abbrev directedModuleColimit (M : ModuleSystem R I)
    (_hI : IsDirectedSet I) : Type (max v w) :=
  moduleColimitQuotient M

/-- The same directed colimit presented as the quotient of the disjoint union. -/
noncomputable abbrev directedModuleColimitDisjointUnion (M : ModuleSystem R I)
    (hI : IsDirectedSet I) : Type (max v w) := by
  classical
  letI : IsDirectedOrder I := hI.2
  exact _root_.DirectLimit
    (fun i => (M.obj i : Type (max v w)))
    (fun i j h => moduleSystemMap M h)

/- The canonical linear map from a stage to the disjoint-union presentation. -/
noncomputable def directedModuleColimitDisjointUnionMap (M : ModuleSystem R I)
    (hI : IsDirectedSet I) (i : I) :
    letI : IsDirectedOrder I := hI.2
    letI : Nonempty I := hI.1
    (M.obj i : Type (max v w)) →ₗ[R] directedModuleColimitDisjointUnion M hI := by
  classical
  letI : IsDirectedOrder I := hI.2
  letI : Nonempty I := hI.1
  exact _root_.DirectLimit.Module.of R I
    (fun i => (M.obj i : Type (max v w)))
    (fun _i _j h => moduleSystemMap M h) i

/- The class of an element of a stage in the directed-colimit quotient. -/
noncomputable def directedModuleColimitClass (M : ModuleSystem R I)
    (hI : IsDirectedSet I) (i : I) (x : (M.obj i : Type (max v w))) :
    directedModuleColimit M hI :=
  moduleColimitQuotientInclusion M i x

noncomputable def directedModuleColimitDisjointUnionClass (M : ModuleSystem R I)
    (hI : IsDirectedSet I) (i : I) (x : (M.obj i : Type (max v w))) :
    directedModuleColimitDisjointUnion M hI := by
  exact directedModuleColimitDisjointUnionMap M hI i x

private noncomputable def moduleColimitQuotientDisjointUnionLinearEquiv
    (M : ModuleSystem R I) (hI : IsDirectedSet I) :
    letI : IsDirectedOrder I := hI.2
    letI : Nonempty I := hI.1
    moduleColimitQuotient M ≃ₗ[R] directedModuleColimitDisjointUnion M hI := by
  classical
  letI : IsDirectedOrder I := hI.2
  letI : Nonempty I := hI.1
  let f := DirectSum.toModule R I (directedModuleColimitDisjointUnion M hI)
    (fun i => directedModuleColimitDisjointUnionMap M hI i)
  have hf : moduleColimitRelations M ≤ LinearMap.ker f := by
    apply Submodule.span_le.2
    rintro z ⟨i, j, h, x, rfl⟩
    change f (moduleColimitDirectSumInclusion M i x -
      moduleColimitDirectSumInclusion M j (moduleSystemMap M h x)) = 0
    rw [map_sub]
    have hcompat :
        directedModuleColimitDisjointUnionMap M hI j (moduleSystemMap M h x) =
          directedModuleColimitDisjointUnionMap M hI i x := by
      apply _root_.DirectLimit.Module.of_f
    simpa [f, moduleColimitDirectSumInclusion] using sub_eq_zero.mpr hcompat.symm
  let toDisjoint : moduleColimitQuotient M →ₗ[R]
      directedModuleColimitDisjointUnion M hI :=
    (moduleColimitRelations M).liftQ f hf
  let fromDisjoint : directedModuleColimitDisjointUnion M hI →ₗ[R]
      moduleColimitQuotient M :=
    _root_.DirectLimit.Module.lift R I
      (fun i => (M.obj i : Type (max v w)))
      (fun i j h => moduleSystemMap M h)
      (fun i => moduleColimitQuotientInclusion M i)
      (fun i j h x => LinearMap.congr_fun
        (moduleColimitQuotientInclusion_compatibility M h) x)
  have hto (i : I) (x : (M.obj i : Type (max v w))) :
      toDisjoint (moduleColimitQuotientInclusion M i x) =
        directedModuleColimitDisjointUnionMap M hI i x := by
    have hq := Submodule.liftQ_mkQ (moduleColimitRelations M) f hf
    have hq' := congrArg
      (fun q => q (moduleColimitDirectSumInclusion M i x)) hq
    simpa only [toDisjoint, moduleColimitQuotientInclusion,
      moduleColimitProjection, LinearMap.comp_apply, f,
      moduleColimitDirectSumInclusion,
      DirectSum.toModule_lof] using hq'
  apply LinearEquiv.ofLinear toDisjoint fromDisjoint
  · apply _root_.DirectLimit.Module.hom_ext
    intro i
    ext x
    change toDisjoint (fromDisjoint
      (_root_.DirectLimit.Module.of R I (fun i => (M.obj i : Type (max v w)))
        (fun i j h => moduleSystemMap M h) i x)) =
      directedModuleColimitDisjointUnionMap M hI i x
    dsimp [fromDisjoint]
    rw [_root_.DirectLimit.Module.lift_of, hto]
  · apply Submodule.quot_hom_ext (moduleColimitRelations M)
    intro z
    have hz :
        (fromDisjoint.comp toDisjoint).comp (moduleColimitProjection M) =
          moduleColimitProjection M := by
      apply DirectSum.linearMap_ext
      intro i
      ext x
      change fromDisjoint (toDisjoint
        (moduleColimitQuotientInclusion M i x)) =
        moduleColimitProjection M (moduleColimitDirectSumInclusion M i x)
      rw [hto]
      change fromDisjoint
          (_root_.DirectLimit.Module.of R I
            (fun i => (M.obj i : Type (max v w)))
            (fun i j h => moduleSystemMap M h) i x) =
        moduleColimitProjection M (moduleColimitDirectSumInclusion M i x)
      dsimp [fromDisjoint]
      rw [_root_.DirectLimit.Module.lift_of]
      simp [moduleColimitQuotientInclusion, LinearMap.comp_apply]
    exact LinearMap.congr_fun hz z

theorem directedModuleColimit_disjointUnion_equiv (M : ModuleSystem R I)
    (hI : IsDirectedSet I) :
    letI : IsDirectedOrder I := hI.2
    letI : Nonempty I := hI.1
    Nonempty
      (directedModuleColimit M hI ≃ₗ[R] directedModuleColimitDisjointUnion M hI) := by
  exact ⟨moduleColimitQuotientDisjointUnionLinearEquiv M hI⟩

theorem directedModuleColimit_eq_iff (M : ModuleSystem R I)
    (hI : IsDirectedSet I) {i j : I}
    (x : (M.obj i : Type (max v w))) (y : (M.obj j : Type (max v w))) :
    directedModuleColimitClass M hI i x = directedModuleColimitClass M hI j y ↔
      ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
        moduleSystemMap M hik x = moduleSystemMap M hjk y := by
  classical
  letI : IsDirectedOrder I := hI.2
  letI : Nonempty I := hI.1
  let e := moduleColimitQuotientDisjointUnionLinearEquiv M hI
  have hclass (i : I) (x : (M.obj i : Type (max v w))) :
        e (directedModuleColimitClass M hI i x) =
        directedModuleColimitDisjointUnionMap M hI i x := by
    let f := DirectSum.toModule R I (directedModuleColimitDisjointUnion M hI)
      (fun i => directedModuleColimitDisjointUnionMap M hI i)
    have hf : moduleColimitRelations M ≤ LinearMap.ker f := by
      apply Submodule.span_le.2
      rintro z ⟨i, j, h, x, rfl⟩
      change f (moduleColimitDirectSumInclusion M i x -
        moduleColimitDirectSumInclusion M j (moduleSystemMap M h x)) = 0
      rw [map_sub]
      have hcompat :
          directedModuleColimitDisjointUnionMap M hI j
              (moduleSystemMap M h x) =
            directedModuleColimitDisjointUnionMap M hI i x := by
        apply _root_.DirectLimit.Module.of_f
      simpa [f, moduleColimitDirectSumInclusion] using
        sub_eq_zero.mpr hcompat.symm
    have hq := Submodule.liftQ_mkQ (moduleColimitRelations M) f hf
    have hq' := congrArg
      (fun f => f (moduleColimitDirectSumInclusion M i x)) hq
    simpa only [e, LinearEquiv.ofLinear_apply, directedModuleColimitClass,
      moduleColimitQuotientDisjointUnionLinearEquiv, f,
      moduleColimitQuotientInclusion, moduleColimitProjection,
      LinearMap.comp_apply, moduleColimitDirectSumInclusion,
      DirectSum.toModule_lof] using hq'
  constructor
  · intro h
    have h' := congrArg e h
    rw [hclass, hclass] at h'
    obtain ⟨k, hik, hjk, hxy⟩ := Quotient.exact h'
    exact ⟨k, hik, hjk, hxy⟩
  · rintro ⟨k, hik, hjk, hxy⟩
    apply e.injective
    rw [hclass, hclass]
    exact Quotient.sound ⟨k, hik, hjk, hxy⟩

theorem directedModuleColimit_add (M : ModuleSystem R I)
    (hI : IsDirectedSet I) {i j : I}
    (x : (M.obj i : Type (max v w))) (y : (M.obj j : Type (max v w)))
    (k : I) (hik : i ≤ k) (hjk : j ≤ k) :
    letI : IsDirectedOrder I := hI.2
    letI : Nonempty I := hI.1
    directedModuleColimitClass M hI i x +
        directedModuleColimitClass M hI j y =
        directedModuleColimitClass M hI k
        (moduleSystemMap M hik x + moduleSystemMap M hjk y) := by
  classical
  letI : IsDirectedOrder I := hI.2
  letI : Nonempty I := hI.1
  let e := moduleColimitQuotientDisjointUnionLinearEquiv M hI
  have hclass (i : I) (x : (M.obj i : Type (max v w))) :
        e (directedModuleColimitClass M hI i x) =
        directedModuleColimitDisjointUnionMap M hI i x := by
    let f := DirectSum.toModule R I (directedModuleColimitDisjointUnion M hI)
      (fun i => directedModuleColimitDisjointUnionMap M hI i)
    have hf : moduleColimitRelations M ≤ LinearMap.ker f := by
      apply Submodule.span_le.2
      rintro z ⟨i, j, h, x, rfl⟩
      change f (moduleColimitDirectSumInclusion M i x -
        moduleColimitDirectSumInclusion M j (moduleSystemMap M h x)) = 0
      rw [map_sub]
      have hcompat :
          directedModuleColimitDisjointUnionMap M hI j
              (moduleSystemMap M h x) =
            directedModuleColimitDisjointUnionMap M hI i x := by
        apply _root_.DirectLimit.Module.of_f
      simpa [f, moduleColimitDirectSumInclusion] using
        sub_eq_zero.mpr hcompat.symm
    have hq := Submodule.liftQ_mkQ (moduleColimitRelations M) f hf
    have hq' := congrArg
      (fun f => f (moduleColimitDirectSumInclusion M i x)) hq
    simpa only [e, LinearEquiv.ofLinear_apply, directedModuleColimitClass,
      moduleColimitQuotientDisjointUnionLinearEquiv, f,
      moduleColimitQuotientInclusion, moduleColimitProjection,
      LinearMap.comp_apply, moduleColimitDirectSumInclusion,
      DirectSum.toModule_lof] using hq'
  apply e.injective
  rw [map_add, hclass i x, hclass j y, hclass k _]
  change
    (_root_.DirectLimit.Module.of R I
      (fun i => (M.obj i : Type (max v w)))
      (fun i j h => moduleSystemMap M h) i x) +
      (_root_.DirectLimit.Module.of R I
        (fun i => (M.obj i : Type (max v w)))
        (fun i j h => moduleSystemMap M h) j y) =
      _root_.DirectLimit.Module.of R I
        (fun i => (M.obj i : Type (max v w)))
        (fun i j h => moduleSystemMap M h) k
          (moduleSystemMap M hik x + moduleSystemMap M hjk y)
  change
    (⟦⟨i, x⟩⟧ : _root_.DirectLimit
      (fun i => (M.obj i : Type (max v w)))
      (fun i j h => moduleSystemMap M h)) +
      ⟦⟨j, y⟩⟧ =
      ⟦⟨k, moduleSystemMap M hik x + moduleSystemMap M hjk y⟩⟧
  have hi :
      (⟦⟨i, x⟩⟧ : _root_.DirectLimit
        (fun i => (M.obj i : Type (max v w)))
        (fun i j h => moduleSystemMap M h)) =
        ⟦⟨k, moduleSystemMap M hik x⟩⟧ :=
    _root_.DirectLimit.eq_of_le
      (f := fun i j h => moduleSystemMap M h) ⟨i, x⟩ k hik
  have hj :
      (⟦⟨j, y⟩⟧ : _root_.DirectLimit
        (fun i => (M.obj i : Type (max v w)))
        (fun i j h => moduleSystemMap M h)) =
        ⟦⟨k, moduleSystemMap M hjk y⟩⟧ :=
    _root_.DirectLimit.eq_of_le
      (f := fun i j h => moduleSystemMap M h) ⟨j, y⟩ k hjk
  rw [hi, hj, _root_.DirectLimit.add_def]

theorem directedModuleColimit_smul (M : ModuleSystem R I)
    (hI : IsDirectedSet I) {i : I}
    (r : R) (x : (M.obj i : Type (max v w))) :
    letI : IsDirectedOrder I := hI.2
    letI : Nonempty I := hI.1
    r • directedModuleColimitClass M hI i x =
      directedModuleColimitClass M hI i (r • x) := by
  classical
  letI : IsDirectedOrder I := hI.2
  letI : Nonempty I := hI.1
  let e := moduleColimitQuotientDisjointUnionLinearEquiv M hI
  have hclass (i : I) (x : (M.obj i : Type (max v w))) :
        e (directedModuleColimitClass M hI i x) =
        directedModuleColimitDisjointUnionMap M hI i x := by
    let f := DirectSum.toModule R I (directedModuleColimitDisjointUnion M hI)
      (fun i => directedModuleColimitDisjointUnionMap M hI i)
    have hf : moduleColimitRelations M ≤ LinearMap.ker f := by
      apply Submodule.span_le.2
      rintro z ⟨i, j, h, x, rfl⟩
      change f (moduleColimitDirectSumInclusion M i x -
        moduleColimitDirectSumInclusion M j (moduleSystemMap M h x)) = 0
      rw [map_sub]
      have hcompat :
          directedModuleColimitDisjointUnionMap M hI j
              (moduleSystemMap M h x) =
            directedModuleColimitDisjointUnionMap M hI i x := by
        apply _root_.DirectLimit.Module.of_f
      simpa [f, moduleColimitDirectSumInclusion] using
        sub_eq_zero.mpr hcompat.symm
    have hq := Submodule.liftQ_mkQ (moduleColimitRelations M) f hf
    have hq' := congrArg
      (fun f => f (moduleColimitDirectSumInclusion M i x)) hq
    simpa only [e, LinearEquiv.ofLinear_apply, directedModuleColimitClass,
      moduleColimitQuotientDisjointUnionLinearEquiv, f,
      moduleColimitQuotientInclusion, moduleColimitProjection,
      LinearMap.comp_apply, moduleColimitDirectSumInclusion,
      DirectSum.toModule_lof] using hq'
  apply e.injective
  rw [map_smul, hclass i (r • x), hclass i x]
  change
    r • (⟦⟨i, x⟩⟧ : _root_.DirectLimit
      (fun i => (M.obj i : Type (max v w)))
      (fun i j h => moduleSystemMap M h)) =
      ⟦⟨i, r • x⟩⟧
  exact _root_.DirectLimit.smul_def
    (G := fun i => (M.obj i : Type (max v w)))
    (f := fun i j h => moduleSystemMap M h) i x r

/-- The canonical maps into the directed-colimit quotient. -/
def directedModuleColimitMap (M : ModuleSystem R I) (hI : IsDirectedSet I) (i : I) :
    (M.obj i : Type (max v w)) →ₗ[R] directedModuleColimit M hI :=
  moduleColimitQuotientInclusion M i

theorem directedModuleColimitMap_apply (M : ModuleSystem R I)
    (hI : IsDirectedSet I) (i : I)
    (x : (M.obj i : Type (max v w))) :
    directedModuleColimitMap M hI i x = directedModuleColimitClass M hI i x := by
  rfl

theorem directedModuleColimitMap_compatibility (M : ModuleSystem R I)
    (hI : IsDirectedSet I) {i j : I} (h : i ≤ j) :
    (directedModuleColimitMap M hI j).comp (moduleSystemMap M h) =
      directedModuleColimitMap M hI i := by
  exact moduleColimitQuotientInclusion_compatibility M h

/- The canonical quotient maps form the directed colimit cocone. -/
def directedModuleColimitCocone (M : ModuleSystem R I)
    (hI : IsDirectedSet I) : Cocone M where
  pt := ModuleCat.of R (directedModuleColimit M hI)
  ι :=
    { app := fun i => ModuleCat.ofHom (directedModuleColimitMap M hI i)
      naturality := by
        intro i j h
        ext x
        exact congrArg (fun f => f x)
          (directedModuleColimitMap_compatibility M hI h.le) }

/- The directed-colimit quotient is canonically a colimit of the system. -/
theorem directedModuleColimit_is_colimit_exists (M : ModuleSystem R I)
    (hI : IsDirectedSet I) :
    Nonempty (IsColimit (directedModuleColimitCocone M hI)) := by
  change Nonempty (IsColimit (moduleColimitQuotientCocone M))
  exact moduleColimitQuotient_is_colimit_exists M

noncomputable def directedModuleColimit_is_colimit (M : ModuleSystem R I)
    (hI : IsDirectedSet I) :
    IsColimit (directedModuleColimitCocone M hI) :=
  (directedModuleColimit_is_colimit_exists M hI).some

/-- The zero criterion for an element in a directed module colimit. -/
theorem moduleSystemColimit_ι_eq_zero_iff
    (M : ModuleSystem R I) (hI : IsDirectedSet I) {i : I}
    (x : (M.obj i : Type (max v w))) :
    (colimit.ι M i) x = 0 ↔
      ∃ (j : I) (hij : i ≤ j), moduleSystemMap M hij x = 0 := by
  classical
  letI : IsDirectedOrder I := hI.2
  letI : Nonempty I := hI.1
  let e : ModuleCat.of R (moduleColimitQuotient M) ≅ colimit M :=
    (moduleColimitQuotient_is_colimit M).coconePointUniqueUpToIso
      (colimit.isColimit M)
  have hfac (j : I) :
      ModuleCat.ofHom (moduleColimitQuotientInclusion M j) ≫ e.hom =
        colimit.ι M j := by
    change (moduleColimitQuotientCocone M).ι.app j ≫ e.hom =
      (colimit.cocone M).ι.app j
    exact (moduleColimitQuotient_is_colimit M).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit M) j
  constructor
  · intro hx
    let j₀ : I := hI.1.some
    have hq : moduleColimitQuotientInclusion M i x =
        moduleColimitQuotientInclusion M j₀ 0 := by
      apply (ConcreteCategory.bijective_of_isIso e.hom).1
      have hi := congrArg (fun f => f.hom x) (hfac i)
      have hj := congrArg (fun f => f.hom 0) (hfac j₀)
      change e.hom.hom (moduleColimitQuotientInclusion M i x) =
        (colimit.ι M i).hom x at hi
      change e.hom.hom (moduleColimitQuotientInclusion M j₀ 0) =
        (colimit.ι M j₀).hom 0 at hj
      change e.hom.hom (moduleColimitQuotientInclusion M i x) =
        e.hom.hom (moduleColimitQuotientInclusion M j₀ 0)
      rw [hi, hj, hx]
      simp
    have hclasszero :
        directedModuleColimitClass M hI i x =
          directedModuleColimitClass M hI j₀ 0 := by
      change moduleColimitQuotientInclusion M i x =
        moduleColimitQuotientInclusion M j₀ 0
      exact hq
    obtain ⟨k, hik, hjk, hzero⟩ :=
      (directedModuleColimit_eq_iff M hI x
        (0 : (M.obj j₀ : Type (max v w)))).mp hclasszero
    refine ⟨k, hik, ?_⟩
    simpa using hzero
  · rintro ⟨j, hij, hx⟩
    calc
      (colimit.ι M i).hom x =
          (colimit.ι M j).hom (moduleSystemMap M hij x) := by
        simpa [moduleSystemMap] using colimit.w_apply M (homOfLE hij) x
      _ = 0 := by rw [hx]; simp

/-! ## The three-object fork example -/

abbrev ThreeForkIndex := WalkingSpan

/-- A system over the fork `a → b`, `a → c`, with arbitrary stage modules and
transition maps. -/
def threeForkSystem {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    ThreeForkIndex ⥤ ModuleCat.{w} R :=
  span uab uac

/-- The map `M_a → M_b ⊕ M_c` given by `μ_ab ⊕ -μ_ac`. -/
def threeForkRelationLinearMap {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    (A : Type w) →ₗ[R] (B × C) where
  toFun x := (uab.hom x, -uac.hom x)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' r x := by simp

def threeForkRelationMap {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    A ⟶ ModuleCat.of R (B × C) :=
  ModuleCat.ofHom (threeForkRelationLinearMap uab uac)

/-- The cokernel presentation of the fork colimit. -/
def threeForkCokernel {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) : ModuleCat.{w} R :=
  cokernel (threeForkRelationMap uab uac)

theorem threeFork_colimit_is_cokernel {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    Nonempty
      (colimit (threeForkSystem uab uac) ≅ threeForkCokernel uab uac) := by
  let q : A ⟶ B ⊞ C := biprod.lift uab (-uac)
  have hrel :
      threeForkRelationMap uab uac = q ≫ (ModuleCat.biprodIsoProd B C).hom := by
    have hrel' :
        threeForkRelationMap uab uac ≫ (ModuleCat.biprodIsoProd B C).inv = q := by
      apply biprod.hom_ext
      · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst, biprod.lift_fst]
        ext x
        rfl
      · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd, biprod.lift_snd]
        ext x
        simp [threeForkRelationMap, threeForkRelationLinearMap]
    apply (cancel_mono (ModuleCat.biprodIsoProd B C).inv).1
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact hrel'
  let hpush : IsColimit
      (CokernelCofork.ofπ (f := threeForkRelationMap uab uac)
        ((ModuleCat.biprodIsoProd B C).inv ≫
          Abelian.BiproductToPushoutIsCokernel.biproductToPushout uab uac) (by
            rw [hrel, Category.assoc, Iso.hom_inv_id_assoc]
            exact
              (Abelian.BiproductToPushoutIsCokernel.biproductToPushoutCofork uab uac).condition)) :=
    CokernelCofork.isColimitOfIsColimitOfIff
      (Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout uab uac)
      (threeForkRelationMap uab uac) (ModuleCat.biprodIsoProd B C).symm (by
        intro W φ
        change q ≫ φ = 0 ↔
          threeForkRelationMap uab uac ≫
            (ModuleCat.biprodIsoProd B C).inv ≫ φ = 0
        constructor
        · intro h
          rw [hrel, Category.assoc, Iso.hom_inv_id_assoc]
          exact h
        · intro h
          rw [hrel, Category.assoc, Iso.hom_inv_id_assoc] at h
          exact h)
  let e : pushout uab uac ≅ threeForkCokernel uab uac :=
    hpush.coconePointUniqueUpToIso
      (colimit.isColimit (parallelPair (threeForkRelationMap uab uac) 0))
  let t : Cocone (threeForkSystem uab uac) :=
    Cocone.extend (colimit.cocone (threeForkSystem uab uac)) e.hom
  have ht : IsColimit t := by
    apply IsColimit.ofIsoColimit (colimit.isColimit (threeForkSystem uab uac))
    exact Cocone.ext e (by intro j; rfl)
  exact ⟨(colimit.isColimit (threeForkSystem uab uac)).coconePointUniqueUpToIso ht⟩

private def threeForkQuotientLeft {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    B →ₗ[R] ((B × C) ⧸ LinearMap.range (threeForkRelationLinearMap uab uac)) :=
  (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ.comp (LinearMap.inl R B C)

private def threeForkQuotientRight {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    C →ₗ[R] ((B × C) ⧸ LinearMap.range (threeForkRelationLinearMap uab uac)) :=
  (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ.comp (LinearMap.inr R B C)

private abbrev threeForkQuotientCocone {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    PushoutCocone uab uac :=
  PushoutCocone.mk (ModuleCat.ofHom (threeForkQuotientLeft uab uac))
    (ModuleCat.ofHom (threeForkQuotientRight uab uac)) (by
      apply ModuleCat.hom_ext
      ext x
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
      change (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ
          (uab.hom x, 0) =
        (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ
          (0, uac.hom x)
      rw [← sub_eq_zero]
      rw [← map_sub]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact LinearMap.mem_range.mpr ⟨x, by
        simp [threeForkRelationLinearMap]⟩)

private def threeForkQuotientIsColimit {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    IsColimit (threeForkQuotientCocone uab uac) := by
  apply PushoutCocone.isColimitAux'
  intro s
  let f : (B × C) →ₗ[R] (s.pt : Type w) :=
    LinearMap.coprod s.inl.hom s.inr.hom
  have hf : LinearMap.range (threeForkRelationLinearMap uab uac) ≤ LinearMap.ker f := by
    rintro z ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have hs := congrArg (fun q => q.hom x) s.condition
    change s.inl.hom (uab.hom x) = s.inr.hom (uac.hom x) at hs
    change s.inl.hom (uab.hom x) + s.inr.hom (-uac.hom x) = 0
    rw [map_neg, ← hs, add_neg_cancel]
  let l := (LinearMap.range (threeForkRelationLinearMap uab uac)).liftQ f hf
  refine ⟨ModuleCat.ofHom l, ?_, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    ext b
    change l ((LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ (b, 0)) = _
    simp [l, f]
  · apply ModuleCat.hom_ext
    ext c
    change l ((LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ (0, c)) = _
    simp [l, f]
  · intro m hm₁ hm₂
    let m' : ModuleCat.of R
        ((B × C) ⧸ LinearMap.range (threeForkRelationLinearMap uab uac)) ⟶ s.pt := m
    have hm₁' : m'.hom.comp (threeForkQuotientLeft uab uac) = s.inl.hom := by
      have h := congrArg (fun q => q.hom) hm₁
      change m'.hom.comp (threeForkQuotientLeft uab uac) = s.inl.hom at h
      exact h
    have hm₂' : m'.hom.comp (threeForkQuotientRight uab uac) = s.inr.hom := by
      have h := congrArg (fun q => q.hom) hm₂
      change m'.hom.comp (threeForkQuotientRight uab uac) = s.inr.hom at h
      exact h
    have hml : m' = ModuleCat.ofHom l := by
      apply ModuleCat.hom_ext
      change m'.hom = l
      apply LinearMap.ext
      intro q
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
        (LinearMap.range (threeForkRelationLinearMap uab uac)) q
      rcases z with ⟨b, c⟩
      change m'.hom ((LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ (b, c)) =
        l ((LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ (b, c))
      have hsplit : (b, c) = (b, 0) + (0, c) := by ext <;> simp
      have hsplitQ :
          (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ (b, c) =
            (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ (b, 0) +
              (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ (0, c) := by
        rw [hsplit, map_add]
      rw [hsplitQ, (m'.hom).map_add, l.map_add]
      change (m'.hom.comp (threeForkQuotientLeft uab uac)) b +
          (m'.hom.comp (threeForkQuotientRight uab uac)) c =
        l ((LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ (b, 0)) +
          l ((LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ (0, c))
      rw [hm₁', hm₂']
      have hlb :
          l ((LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ (b, 0)) =
            s.inl.hom b := by
        simp [l, Submodule.liftQ_apply, f]
      have hlc :
          l ((LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ (0, c)) =
            s.inr.hom c := by
        simp [l, Submodule.liftQ_apply, f]
      rw [hlb, hlc]
    change m' = ModuleCat.ofHom l
    exact hml

private def threeForkQuotientIso {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    colimit (span uab uac) ≅ ModuleCat.of R
      ((B × C) ⧸ LinearMap.range (threeForkRelationLinearMap uab uac)) :=
  (colimit.isColimit (span uab uac)).coconePointUniqueUpToIso
    (threeForkQuotientIsColimit uab uac)

private lemma threeForkQuotientIso_left {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    colimit.ι (span uab uac) WalkingSpan.left ≫ (threeForkQuotientIso uab uac).hom =
      ModuleCat.ofHom (threeForkQuotientLeft uab uac) := by
  change colimit.ι (span uab uac) WalkingSpan.left ≫
      ((colimit.isColimit (span uab uac)).coconePointUniqueUpToIso
        (threeForkQuotientIsColimit uab uac)).hom =
    (threeForkQuotientCocone uab uac).ι.app WalkingSpan.left
  exact (colimit.isColimit (span uab uac)).comp_coconePointUniqueUpToIso_hom
    (threeForkQuotientIsColimit uab uac) WalkingSpan.left

private lemma threeForkQuotientIso_right {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    colimit.ι (span uab uac) WalkingSpan.right ≫ (threeForkQuotientIso uab uac).hom =
      ModuleCat.ofHom (threeForkQuotientRight uab uac) := by
  change colimit.ι (span uab uac) WalkingSpan.right ≫
      ((colimit.isColimit (span uab uac)).coconePointUniqueUpToIso
        (threeForkQuotientIsColimit uab uac)).hom =
    (threeForkQuotientCocone uab uac).ι.app WalkingSpan.right
  exact (colimit.isColimit (span uab uac)).comp_coconePointUniqueUpToIso_hom
    (threeForkQuotientIsColimit uab uac) WalkingSpan.right

private lemma threeForkQuotientIso_zero {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    colimit.ι (span uab uac) WalkingSpan.zero ≫ (threeForkQuotientIso uab uac).hom =
      uab ≫ ModuleCat.ofHom (threeForkQuotientLeft uab uac) := by
  have h := colimit.w (span uab uac) WalkingSpan.Hom.fst
  rw [← h, Category.assoc, span_map_fst, threeForkQuotientIso_left]
  rfl

/- The following are the two kernel calculations displayed in the source;
   `⊔` is the submodule sum. -/
theorem threeFork_kernel_at_a {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    LinearMap.ker (colimit.ι (threeForkSystem uab uac) .zero).hom =
      LinearMap.ker uab.hom ⊔ LinearMap.ker uac.hom := by
  let i : A ⟶ colimit (span uab uac) :=
    colimit.ι (threeForkSystem uab uac) WalkingSpan.zero
  change LinearMap.ker i.hom = LinearMap.ker uab.hom ⊔ LinearMap.ker uac.hom
  ext (x : (A : Type w))
  constructor
  · intro hx
    have hz := congrArg (fun q => q.hom x) (threeForkQuotientIso_zero uab uac)
    change (threeForkQuotientIso uab uac).hom (i.hom x) =
        threeForkQuotientLeft uab uac (uab.hom x) at hz
    have hx' : i.hom x = 0 := (LinearMap.mem_ker.mp hx)
    rw [hx', map_zero] at hz
    have hq : threeForkQuotientLeft uab uac (uab.hom x) = 0 := hz.symm
    have hmem : (uab.hom x, 0) ∈
        LinearMap.range (threeForkRelationLinearMap uab uac) := by
      change (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ
          (uab.hom x, 0) = 0 at hq
      have hk : (uab.hom x, 0) ∈
          (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ.ker :=
        (LinearMap.mem_ker).2 hq
      simpa only [Submodule.ker_mkQ] using hk
    rcases LinearMap.mem_range.mp hmem with ⟨y, hy⟩
    have hxy : uab.hom y = uab.hom x := by
      have := congrArg Prod.fst hy
      simpa [threeForkRelationLinearMap] using this
    have hyker : uac.hom y = 0 := by
      have := congrArg Prod.snd hy
      simpa [threeForkRelationLinearMap] using this
    apply (Submodule.mem_sup).2
    refine ⟨x - y, ?_, y, ?_, sub_add_cancel x y⟩
    · rw [LinearMap.mem_ker, map_sub, hxy.symm, sub_self]
    · exact (LinearMap.mem_ker).2 hyker
  · intro hx
    rcases (Submodule.mem_sup).1 hx with ⟨y, hy, z, hz, rfl⟩
    have hy' : uab.hom y = 0 := (LinearMap.mem_ker).1 hy
    have hz' : uac.hom z = 0 := (LinearMap.mem_ker).1 hz
    have hrel : threeForkQuotientLeft uab uac (uab.hom z) =
        threeForkQuotientRight uab uac (uac.hom z) := by
      change (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ
          (uab.hom z, 0) =
        (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ
          (0, uac.hom z)
      rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact LinearMap.mem_range.mpr ⟨z, by simp [threeForkRelationLinearMap]⟩
    have hq : threeForkQuotientLeft uab uac (uab.hom (y + z)) = 0 := by
      rw [map_add, hy', zero_add, hrel, hz', map_zero]
    apply (LinearMap.mem_ker).2
    apply (ConcreteCategory.bijective_of_isIso (threeForkQuotientIso uab uac).hom).1
    have he := congrArg (fun q => q.hom (y + z)) (threeForkQuotientIso_zero uab uac)
    change (threeForkQuotientIso uab uac).hom (i.hom (y + z)) =
      threeForkQuotientLeft uab uac (uab.hom (y + z)) at he
    rw [hq] at he
    simpa using he

theorem threeFork_kernel_at_b {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    LinearMap.ker (colimit.ι (threeForkSystem uab uac) .left).hom =
      Submodule.map uab.hom (LinearMap.ker uac.hom) := by
  let i : B ⟶ colimit (span uab uac) :=
    colimit.ι (threeForkSystem uab uac) WalkingSpan.left
  change LinearMap.ker i.hom = Submodule.map uab.hom (LinearMap.ker uac.hom)
  ext (x : (B : Type w))
  constructor
  · intro hx
    have hz := congrArg (fun q => q.hom x) (threeForkQuotientIso_left uab uac)
    change (threeForkQuotientIso uab uac).hom (i.hom x) =
        threeForkQuotientLeft uab uac x at hz
    have hx' : i.hom x = 0 := (LinearMap.mem_ker.mp hx)
    rw [hx', map_zero] at hz
    have hq : threeForkQuotientLeft uab uac x = 0 := hz.symm
    have hmem : (x, 0) ∈
        LinearMap.range (threeForkRelationLinearMap uab uac) := by
      change (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ (x, 0) = 0 at hq
      have hk : (x, 0) ∈
          (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ.ker :=
        (LinearMap.mem_ker).2 hq
      simpa only [Submodule.ker_mkQ] using hk
    rcases LinearMap.mem_range.mp hmem with ⟨y, hy⟩
    have hxy : uab.hom y = x := by
      have := congrArg Prod.fst hy
      simpa [threeForkRelationLinearMap] using this
    have hyker : uac.hom y = 0 := by
      have := congrArg Prod.snd hy
      simpa [threeForkRelationLinearMap] using this
    exact (Submodule.mem_map).2 ⟨y, (LinearMap.mem_ker).2 hyker, hxy⟩
  · intro hx
    rcases (Submodule.mem_map).1 hx with ⟨y, hy, hxy⟩
    have hy' : uac.hom y = 0 := (LinearMap.mem_ker).1 hy
    have hrel : threeForkQuotientLeft uab uac (uab.hom y) =
        threeForkQuotientRight uab uac (uac.hom y) := by
      change (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ
          (uab.hom y, 0) =
        (LinearMap.range (threeForkRelationLinearMap uab uac)).mkQ
          (0, uac.hom y)
      rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact LinearMap.mem_range.mpr ⟨y, by simp [threeForkRelationLinearMap]⟩
    have hq : threeForkQuotientLeft uab uac (uab.hom y) = 0 := by
      rw [hrel, hy', map_zero]
    rw [← hxy]
    apply (LinearMap.mem_ker).2
    apply (ConcreteCategory.bijective_of_isIso (threeForkQuotientIso uab uac).hom).1
    have he := congrArg (fun q => q.hom (uab.hom y))
      (threeForkQuotientIso_left uab uac)
    change (threeForkQuotientIso uab uac).hom (i.hom (uab.hom y)) =
      threeForkQuotientLeft uab uac (uab.hom y) at he
    rw [hq] at he
    simpa using he

/-! ## Homomorphisms of systems -/

/-- A homomorphism of module systems is the existing natural-transformation
interface between the associated functors. -/
abbrev ModuleSystemHom (M N : ModuleSystem R I) := M ⟶ N

/-- The homomorphism induced on categorical colimits. -/
noncomputable def moduleSystemColimitMap {M N : ModuleSystem R I}
    (Φ : ModuleSystemHom M N) : moduleSystemColimit M ⟶ moduleSystemColimit N :=
  colim.map Φ

theorem moduleSystemColimitMap_ι {M N : ModuleSystem R I}
    (Φ : ModuleSystemHom M N) (i : I) :
    colimit.ι M i ≫ moduleSystemColimitMap Φ =
      Φ.app i ≫ colimit.ι N i := by
  exact colimit.ι_map Φ i

theorem moduleSystemColimitMap_unique {M N : ModuleSystem R I}
    (Φ : ModuleSystemHom M N) (g : moduleSystemColimit M ⟶ moduleSystemColimit N)
    (hg : ∀ i : I, colimit.ι M i ≫ g = Φ.app i ≫ colimit.ι N i) :
    g = moduleSystemColimitMap Φ := by
  apply colimit.hom_ext
  intro i
  exact (hg i).trans (colimit.ι_map Φ i).symm

/-! A concrete instance of the fork illustrates why the zero criterion needs
directedness. -/

abbrev integerZeroModule : ModuleCat ℤ := ModuleCat.of ℤ (Fin 0 → ℤ)

def nonDirectedSourceSystem : ThreeForkIndex ⥤ ModuleCat ℤ :=
  threeForkSystem
    (0 : integerZeroModule ⟶ ModuleCat.of ℤ ℤ)
    (0 : integerZeroModule ⟶ ModuleCat.of ℤ ℤ)

def nonDirectedTargetSystem : ThreeForkIndex ⥤ ModuleCat ℤ :=
  threeForkSystem (𝟙 (ModuleCat.of ℤ ℤ)) (𝟙 (ModuleCat.of ℤ ℤ))

def nonDirectedSystemMap :
    nonDirectedSourceSystem ⟶ nonDirectedTargetSystem :=
  spanHomMk (0 : integerZeroModule ⟶ ModuleCat.of ℤ ℤ)
    (𝟙 (ModuleCat.of ℤ ℤ)) (𝟙 (ModuleCat.of ℤ ℤ))

theorem nonDirectedSystemMap_stagewise_injective :
    ∀ i : ThreeForkIndex,
      Function.Injective ((nonDirectedSystemMap.app i).hom) := by
  intro i
  cases i with
  | none =>
      intro x y _
      funext z
      exact Fin.elim0 z
  | some j =>
      cases j with
      | left =>
          intro x y h
          change x = y at h
          exact h
      | right =>
          intro x y h
          change x = y at h
          exact h

theorem nonDirected_colimit_map_not_injective :
    ¬ Function.Injective ((colim.map nonDirectedSystemMap).hom) := by
  intro hinj
  let c : Cocone nonDirectedSourceSystem :=
    PushoutCocone.mk (𝟙 (ModuleCat.of ℤ ℤ)) 0 (by
      simp [nonDirectedSourceSystem])
  let d := colimit.desc nonDirectedSourceSystem c
  let x : ℤ := 1
  have hxy :
      (colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom x ≠
        (colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom x := by
    intro h
    have hd := congrArg (fun q => d.hom q) h
    have hleft := colimit.ι_desc c WalkingSpan.left
    have hright := colimit.ι_desc c WalkingSpan.right
    have hleft_lin :
        d.hom.comp (colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom =
          (c.ι.app WalkingSpan.left).hom := by
      simpa only [d, ModuleCat.hom_comp] using congrArg (fun q => q.hom) hleft
    have hright_lin :
        d.hom.comp (colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom =
          (c.ι.app WalkingSpan.right).hom := by
      simpa only [d, ModuleCat.hom_comp] using congrArg (fun q => q.hom) hright
    have hleft' := congrArg (fun q => q x) hleft_lin
    have hright' := congrArg (fun q => q x) hright_lin
    have hleft_eval :
        d.hom ((colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom x) =
          (c.ι.app WalkingSpan.left).hom x := by
      calc
        d.hom ((colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom x) =
            (d.hom.comp (colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom) x :=
          (LinearMap.comp_apply _ _ _).symm
        _ = (c.ι.app WalkingSpan.left).hom x := hleft'
    have hright_eval :
        d.hom ((colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom x) =
          (c.ι.app WalkingSpan.right).hom x := by
      calc
        d.hom ((colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom x) =
            (d.hom.comp (colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom) x :=
          (LinearMap.comp_apply _ _ _).symm
        _ = (c.ι.app WalkingSpan.right).hom x := hright'
    rw [hleft_eval, hright_eval] at hd
    dsimp [c, x] at hd
    change (1 : ℤ) = 0 at hd
    exact one_ne_zero hd
  apply hxy
  apply hinj
  have hlegs :
      colimit.ι nonDirectedTargetSystem WalkingSpan.left =
        colimit.ι nonDirectedTargetSystem WalkingSpan.right := by
    have hleft := colimit.w nonDirectedTargetSystem WalkingSpan.Hom.fst
    have hright := colimit.w nonDirectedTargetSystem WalkingSpan.Hom.snd
    change colimit.ι nonDirectedTargetSystem WalkingSpan.left =
      colimit.ι nonDirectedTargetSystem WalkingSpan.zero at hleft
    change colimit.ι nonDirectedTargetSystem WalkingSpan.right =
      colimit.ι nonDirectedTargetSystem WalkingSpan.zero at hright
    exact hleft.trans hright.symm
  have hleg := congrArg (fun q => q.hom x) hlegs
  have hl := congrArg (fun q => q.hom x)
    (colimit.ι_map nonDirectedSystemMap WalkingSpan.left)
  have hr := congrArg (fun q => q.hom x)
    (colimit.ι_map nonDirectedSystemMap WalkingSpan.right)
  have hl' :
      (colim.map nonDirectedSystemMap).hom
          ((colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom x) =
        (colimit.ι nonDirectedTargetSystem WalkingSpan.left).hom x := by
    change (colim.map nonDirectedSystemMap).hom
        ((colimit.ι nonDirectedSourceSystem WalkingSpan.left).hom x) =
      (colimit.ι nonDirectedTargetSystem WalkingSpan.left).hom x at hl
    exact hl
  have hr' :
      (colim.map nonDirectedSystemMap).hom
          ((colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom x) =
        (colimit.ι nonDirectedTargetSystem WalkingSpan.right).hom x := by
    change (colim.map nonDirectedSystemMap).hom
        ((colimit.ι nonDirectedSourceSystem WalkingSpan.right).hom x) =
      (colimit.ι nonDirectedTargetSystem WalkingSpan.right).hom x at hr
    exact hr
  exact hl'.trans (hleg.trans hr'.symm)

/-! ## Exactness of directed colimits -/

/-- The system of short complexes associated to levelwise maps of systems. -/
def moduleSystemShortComplex {R : Type u} [CommRing R]
    {I : Type v} [Preorder I]
    {L M N : ModuleSystem R I} (φ : L ⟶ M) (ψ : M ⟶ N)
    (hcomplex : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    I ⥤ ShortComplex (ModuleCat.{max v w} R) where
  obj i := ShortComplex.mk (φ.app i) (ψ.app i) (hcomplex i)
  map {i j} h :=
    ShortComplex.homMk (L.map h) (M.map h) (N.map h)
      (φ.naturality h) (ψ.naturality h)
  map_id := by
    intro i
    apply ShortComplex.hom_ext <;> simp
  map_comp := by
    intro i j k hij hjk
    apply ShortComplex.hom_ext <;> simp

/-! The homology modules form the induced system of homology objects. -/
noncomputable def moduleSystemHomologySystem {R : Type u} [CommRing R]
    {I : Type v} [Preorder I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v w} R)) :
    I ⥤ ModuleCat.{max v w} R :=
  S ⋙ ShortComplex.homologyFunctor (ModuleCat.{max v w} R)

/- The first and second maps of a system of short complexes. -/
def moduleShortComplexFirstMap {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    (S ⋙ ShortComplex.π₁) ⟶ (S ⋙ ShortComplex.π₂) where
  app i := (S.obj i).f
  naturality _i _j f := (S.map f).comm₁₂

def moduleShortComplexSecondMap {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    (S ⋙ ShortComplex.π₂) ⟶ (S ⋙ ShortComplex.π₃) where
  app i := (S.obj i).g
  naturality _i _j f := (S.map f).comm₂₃

/-- The sequence obtained by taking colimits of a system of short complexes is
a complex. -/
theorem moduleShortComplexColimit_is_complex {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    colim.map (moduleShortComplexFirstMap S) ≫
        colim.map (moduleShortComplexSecondMap S) = 0 := by
  apply colimit.hom_ext
  intro i
  rw [← Category.assoc, colimit.ι_map, Category.assoc, colimit.ι_map]
  have hi :
      (moduleShortComplexFirstMap S).app i ≫
          (moduleShortComplexSecondMap S).app i = 0 := by
    change (S.obj i).f ≫ (S.obj i).g = 0
    exact (S.obj i).zero
  rw [← Category.assoc, hi, zero_comp, comp_zero]

/-- The colimit short complex associated to a system of short complexes. -/
noncomputable def moduleShortComplexColimit {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    ShortComplex (ModuleCat.{max v v' w} R) :=
  ShortComplex.mk (colim.map (moduleShortComplexFirstMap S))
    (colim.map (moduleShortComplexSecondMap S))
    (moduleShortComplexColimit_is_complex S)

theorem directed_colimit_homology {R : Type u} [CommRing R]
    {I : Type v} [Preorder I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v w} R)) (hI : IsDirectedSet I) :
    Nonempty
      ((moduleShortComplexColimit S).homology ≅
        colimit (moduleSystemHomologySystem S)) := by
  letI : IsDirectedOrder I := hI.2
  letI : Nonempty I := hI.1
  letI : IsFiltered I := inferInstance
  letI : AB5OfSize.{v, v} (AddCommGrpCat.{max v w}) :=
    AB5OfSize_of_univLE (AddCommGrpCat.{max v w})
  letI : HasExactColimitsOfShape I (ModuleCat.{max v w} R) :=
    HasExactColimitsOfShape.domain_of_functor I
      (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat)
  have hF : (colim : (I ⥤ ModuleCat.{max v w} R) ⥤
      ModuleCat.{max v w} R).PreservesHomology := by infer_instance
  let T := ShortComplex.FunctorEquivalence.inverse I (ModuleCat.{max v w} R)
  let ST := T.obj S
  have hfirst : S.whiskerLeft ShortComplex.π₁Toπ₂ =
      moduleShortComplexFirstMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hsecond : S.whiskerLeft ShortComplex.π₂Toπ₃ =
      moduleShortComplexSecondMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hff : colim.map ST.f = colim.map (moduleShortComplexFirstMap S) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hfirst
  have hgg : colim.map ST.g = colim.map (moduleShortComplexSecondMap S) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hsecond
  let q : ST.map colim ≅ moduleShortComplexColimit S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
        exact hff.symm)
      (by
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
        exact hgg.symm)
  let E := ShortComplex.FunctorEquivalence.functor I (ModuleCat.{max v w} R)
  let HST := E.obj ST ⋙ ShortComplex.homologyFunctor (ModuleCat.{max v w} R)
  let p₀ : ST.homology ≅ HST :=
    NatIso.ofComponents (fun i => by
      simpa [HST, E, T, ST, ShortComplex.FunctorEquivalence.functor,
        ShortComplex.FunctorEquivalence.inverse] using
        (ST.mapHomologyIso ((evaluation I (ModuleCat.{max v w} R)).obj i)).symm) (by
      intro i j h
      let eᵢ := ST.mapHomologyIso ((evaluation I (ModuleCat.{max v w} R)).obj i)
      let eⱼ := ST.mapHomologyIso ((evaluation I (ModuleCat.{max v w} R)).obj j)
      change ST.homology.map h ≫ eⱼ.inv =
        eᵢ.inv ≫ ShortComplex.homologyMap (ST.mapNatTrans
          ((evaluation I (ModuleCat.{max v w} R)).map h))
      rw [ShortComplex.homologyMap_mapNatTrans]
      change ST.homology.map h ≫ eⱼ.inv =
        eᵢ.inv ≫ eᵢ.hom ≫
          ((evaluation I (ModuleCat.{max v w} R)).map h).app ST.homology ≫ eⱼ.inv
      simp)
  let p : ST.homology ≅ moduleSystemHomologySystem S :=
    p₀ ≪≫ Functor.isoWhiskerRight
      ((ShortComplex.FunctorEquivalence.counitIso I
        (ModuleCat.{max v w} R)).app S)
      (ShortComplex.homologyFunctor (ModuleCat.{max v w} R))
  refine ⟨((ShortComplex.homologyFunctor (ModuleCat.{max v w} R)).mapIso q).symm ≪≫
    ST.mapHomologyIso colim ≪≫ colim.mapIso p⟩

theorem directed_colimit_exact {R : Type u} [CommRing R]
    {I : Type v} [Preorder I]
    {L M N : ModuleSystem R I} (φ : L ⟶ M) (ψ : M ⟶ N)
    (hcomplex : ∀ i : I, φ.app i ≫ ψ.app i = 0)
    (hI : IsDirectedSet I) :
    Nonempty
      ((moduleShortComplexColimit (moduleSystemShortComplex φ ψ hcomplex)).homology ≅
        colimit (moduleSystemHomologySystem
          (moduleSystemShortComplex φ ψ hcomplex))) := by
  exact directed_colimit_homology (moduleSystemShortComplex φ ψ hcomplex) hI

theorem directed_colimit_exact_of_exact {R : Type u} [CommRing R]
    {I : Type v} [Preorder I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v w} R)) (hI : IsDirectedSet I)
    (hS : ∀ i : I, (S.obj i).Exact) :
    (moduleShortComplexColimit S).Exact := by
  letI : IsDirectedOrder I := hI.2
  letI : Nonempty I := hI.1
  letI : IsFiltered I := inferInstance
  letI : AB5OfSize.{v, v} (AddCommGrpCat.{max v w}) :=
    AB5OfSize_of_univLE (AddCommGrpCat.{max v w})
  letI : HasExactColimitsOfShape I (ModuleCat.{max v w} R) :=
    HasExactColimitsOfShape.domain_of_functor I
      (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat)
  have hF : (colim : (I ⥤ ModuleCat.{max v w} R) ⥤
      ModuleCat.{max v w} R).PreservesHomology := by infer_instance
  let T := ShortComplex.FunctorEquivalence.inverse I (ModuleCat.{max v w} R)
  let ST := T.obj S
  have hST : ST.Exact := by
    apply (ST.exact_iff_isZero_homology).2
    refine { unique_to := ?_, unique_from := ?_ }
    · intro X
      refine ⟨⟨⟨0⟩, ?_⟩⟩
      intro q
      apply NatTrans.ext
      funext i
      change q.app i = ((0 : ST.homology ⟶ X).app i)
      have hi : IsZero (ST.homology.obj i) := by
        let e := (ShortComplex.homologyFunctorIso
          ((evaluation I (ModuleCat.{max v w} R)).obj i)).app ST
        apply IsZero.of_iso ((ST.map ((evaluation I (ModuleCat.{max v w} R)).obj i)).exact_iff_isZero_homology.1
          (hS i)) e.symm
      exact hi.eq_of_src (q.app i) ((0 : ST.homology ⟶ X).app i)
    · intro X
      refine ⟨⟨⟨0⟩, ?_⟩⟩
      intro q
      apply NatTrans.ext
      funext i
      change q.app i = ((0 : X ⟶ ST.homology).app i)
      have hi : IsZero (ST.homology.obj i) := by
        let e := (ShortComplex.homologyFunctorIso
          ((evaluation I (ModuleCat.{max v w} R)).obj i)).app ST
        apply IsZero.of_iso ((ST.map ((evaluation I (ModuleCat.{max v w} R)).obj i)).exact_iff_isZero_homology.1
          (hS i)) e.symm
      exact hi.eq_of_tgt (q.app i) ((0 : X ⟶ ST.homology).app i)
  have hfirst : S.whiskerLeft ShortComplex.π₁Toπ₂ =
      moduleShortComplexFirstMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hsecond : S.whiskerLeft ShortComplex.π₂Toπ₃ =
      moduleShortComplexSecondMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hff : colim.map ST.f = colim.map (moduleShortComplexFirstMap S) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hfirst
  have hgg : colim.map ST.g = colim.map (moduleShortComplexSecondMap S) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hsecond
  have hcol := colim.exact_mapShortComplex (S := ST) hST
    (c₁ := colimit.cocone ST.X₁)
    (hc₁ := colimit.isColimit ST.X₁)
    (c₂ := colimit.cocone ST.X₂)
    (hc₂ := colimit.isColimit ST.X₂)
    (c₃ := colimit.cocone ST.X₃)
    (hc₃ := colimit.isColimit ST.X₃)
    (f := colim.map ST.f) (g := colim.map ST.g) (hf := by
      intro i
      exact colimit.ι_map ST.f i) (hg := by
      intro i
      exact colimit.ι_map ST.g i)
  change (ShortComplex.mk (colim.map ST.f) (colim.map ST.g) _).Exact at hcol
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_) hcol
  · simpa [moduleShortComplexColimit] using hff.symm
  · simpa [moduleShortComplexColimit] using hgg.symm

/-! ## Coproducts and the almost-directed statement -/

def discreteShortComplexSystem {R : Type u} [CommRing R]
    {J : Type v} (S : J → ShortComplex (ModuleCat.{max v w} R)) :
    Discrete J ⥤ ShortComplex (ModuleCat.{max v w} R) :=
  Discrete.functor S

/-- The categorical direct-sum sequence attached to a family of short
complexes. -/
abbrev directSumShortComplex {R : Type u} [CommRing R]
    {J : Type v} (S : J → ShortComplex (ModuleCat.{max v w} R)) :=
  moduleShortComplexColimit (discreteShortComplexSystem S)

theorem direct_sum_of_exact_short_complexes {R : Type u} [CommRing R]
    {J : Type v} (S : J → ShortComplex (ModuleCat.{max v w} R))
    (hS : ∀ j : J, (S j).Exact) :
    (directSumShortComplex S).Exact := by
  letI : AB5OfSize.{v, v} (AddCommGrpCat.{max v w}) :=
    AB5OfSize_of_univLE (AddCommGrpCat.{max v w})
  letI : AB4OfSize.{max v w} (AddCommGrpCat.{max v w}) :=
    AB4.of_AB5 (AddCommGrpCat.{max v w})
  letI : AB4OfSize.{v} (AddCommGrpCat.{max v w}) :=
    AB4OfSize_shrink (AddCommGrpCat.{max v w})
  letI : HasExactColimitsOfShape (Discrete J) (ModuleCat.{max v w} R) :=
    HasExactColimitsOfShape.domain_of_functor (Discrete J)
      (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat)
  have hF : (colim : (Discrete J ⥤ ModuleCat.{max v w} R) ⥤
      ModuleCat.{max v w} R).PreservesHomology := by infer_instance
  let SD := discreteShortComplexSystem S
  let T := ShortComplex.FunctorEquivalence.inverse (Discrete J)
    (ModuleCat.{max v w} R)
  let ST := T.obj SD
  have hST : ST.Exact := by
    apply (ST.exact_iff_isZero_homology).2
    refine { unique_to := ?_, unique_from := ?_ }
    · intro X
      refine ⟨⟨⟨0⟩, ?_⟩⟩
      intro q
      apply NatTrans.ext
      funext i
      change q.app i = ((0 : ST.homology ⟶ X).app i)
      have hi : IsZero (ST.homology.obj i) := by
        let e := (ShortComplex.homologyFunctorIso
          ((evaluation (Discrete J) (ModuleCat.{max v w} R)).obj i)).app ST
        apply IsZero.of_iso
          ((ST.map ((evaluation (Discrete J) (ModuleCat.{max v w} R)).obj i)).exact_iff_isZero_homology.1
            (hS i.as)) e.symm
      exact hi.eq_of_src (q.app i) ((0 : ST.homology ⟶ X).app i)
    · intro X
      refine ⟨⟨⟨0⟩, ?_⟩⟩
      intro q
      apply NatTrans.ext
      funext i
      change q.app i = ((0 : X ⟶ ST.homology).app i)
      have hi : IsZero (ST.homology.obj i) := by
        let e := (ShortComplex.homologyFunctorIso
          ((evaluation (Discrete J) (ModuleCat.{max v w} R)).obj i)).app ST
        apply IsZero.of_iso
          ((ST.map ((evaluation (Discrete J) (ModuleCat.{max v w} R)).obj i)).exact_iff_isZero_homology.1
            (hS i.as)) e.symm
      exact hi.eq_of_tgt (q.app i) ((0 : X ⟶ ST.homology).app i)
  have hfirst : SD.whiskerLeft ShortComplex.π₁Toπ₂ =
      moduleShortComplexFirstMap SD := by
    apply NatTrans.ext
    funext i
    rfl
  have hsecond : SD.whiskerLeft ShortComplex.π₂Toπ₃ =
      moduleShortComplexSecondMap SD := by
    apply NatTrans.ext
    funext i
    rfl
  have hff : colim.map ST.f = colim.map (moduleShortComplexFirstMap SD) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hfirst
  have hgg : colim.map ST.g = colim.map (moduleShortComplexSecondMap SD) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hsecond
  have hcol := colim.exact_mapShortComplex (S := ST) hST
    (c₁ := colimit.cocone ST.X₁)
    (hc₁ := colimit.isColimit ST.X₁)
    (c₂ := colimit.cocone ST.X₂)
    (hc₂ := colimit.isColimit ST.X₂)
    (c₃ := colimit.cocone ST.X₃)
    (hc₃ := colimit.isColimit ST.X₃)
    (f := colim.map ST.f) (g := colim.map ST.g) (hf := by
      intro i
      exact colimit.ι_map ST.f i) (hg := by
      intro i
      exact colimit.ι_map ST.g i)
  change (ShortComplex.mk (colim.map ST.f) (colim.map ST.g) _).Exact at hcol
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_) hcol
  · simpa [directSumShortComplex, moduleShortComplexColimit] using hff.symm
  · simpa [directSumShortComplex, moduleShortComplexColimit] using hgg.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def decomposedColimitCocone {R : Type u} [CommRing R]
    {J : Type v} [Category.{v'} J]
    (H : ∀ j : ConnectedComponents J,
      j.Component ⥤ ModuleCat.{max v v' w} R) :
    Cocone (CategoryTheory.Sigma.desc H) := by
  let G : ConnectedComponents J → ModuleCat.{max v v' w} R :=
    fun j => colimit (H j)
  let O := colimit (Discrete.functor G)
  let ι : CategoryTheory.Sigma.desc H ⟶
      (Functor.const (Decomposed J)).obj O :=
    Sigma.natTrans (fun j => {
      app := fun x => (Sigma.inclDesc H j).hom.app x ≫
        colimit.ι (H j) x ≫
        colimit.ι (Discrete.functor G) (Discrete.mk j)
      naturality := by
        intro X Y f
        dsimp [G]
        have h := congrArg (fun q =>
            q ≫ colimit.ι (H j) Y ≫
              colimit.ι (Discrete.functor G) (Discrete.mk j))
          ((Sigma.inclDesc H j).hom.naturality f)
        have hf : (Sigma.incl j).map f = Sigma.SigmaHom.mk f := rfl
        simpa [Functor.const_obj_map, Functor.comp_map,
          CategoryTheory.Sigma.desc_map_mk, Sigma.inclDesc_hom_app,
          hf, Category.id_comp, Category.comp_id, Category.assoc, colimit.w] using h
      })
  exact { pt := O, ι := ι }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def decomposedColimitIsColimit {R : Type u} [CommRing R]
    {J : Type v} [Category.{v'} J]
    (H : ∀ j : ConnectedComponents J,
      j.Component ⥤ ModuleCat.{max v v' w} R) :
    IsColimit (decomposedColimitCocone H) := by
  let G : ConnectedComponents J → ModuleCat.{max v v' w} R :=
    fun j => colimit (H j)
  let O := colimit (Discrete.functor G)
  let desc (s : Cocone (CategoryTheory.Sigma.desc H)) :
      (decomposedColimitCocone H).pt ⟶ s.pt := by
    let cG : Cocone (Discrete.functor G) :=
      Cocone.mk s.pt (Discrete.natTrans (fun j => by
        let c : Cocone (H j.as) :=
          (Cocone.precompose (Sigma.inclDesc H j.as).inv).obj
            (s.whisker (inclusion j.as))
        exact colimit.desc (H j.as) c))
    exact colimit.desc (Discrete.functor G) cG
  refine { desc := fun s => desc s, fac := ?_, uniq := ?_ }
  · intro s
    rintro ⟨j, X⟩
    dsimp [decomposedColimitCocone, desc, G]
    change _ = s.ι.app ((inclusion j).obj X)
    simp only [Category.id_comp, Category.assoc, Discrete.natTrans_app,
      Cofan.mk_ι_app, colimit.ι_desc]
    rfl
  · intro s m hm
    dsimp [decomposedColimitCocone] at m hm ⊢
    apply colimit.hom_ext
    rintro ⟨j⟩
    apply colimit.hom_ext
    intro X
    have h := hm ⟨j, X⟩
    dsimp [desc, G]
    simpa [Sigma.natTrans_app, Sigma.inclDesc_hom_app,
      Cocone.precompose_obj_ι, Cocone.whisker_ι, NatTrans.comp_app,
      Discrete.natTrans_app, Category.assoc, colimit.ι_desc] using h

private noncomputable def decomposedColimitIso {R : Type u} [CommRing R]
    {J : Type v} [Category.{v'} J]
    (F : J ⥤ ModuleCat.{max v v' w} R) :
    colimit F ≅ colimit
      (Discrete.functor (fun j : ConnectedComponents J =>
          colimit (inclusion j ⋙
          (decomposedEquiv (J := J)).functor ⋙ F))) := by
  let e := (decomposedEquiv (J := J)).inverse
  let ef := (decomposedEquiv (J := J)).functor
  let H : ∀ j : ConnectedComponents J,
      j.Component ⥤ ModuleCat.{max v v' w} R :=
    fun j => inclusion j ⋙ ef ⋙ F
  let i₀ : e ⋙ ef ⋙ F ≅ e ⋙ CategoryTheory.Sigma.desc H :=
    Functor.isoWhiskerLeft e
      (Sigma.descUniq H (ef ⋙ F) (fun _ => Iso.refl _))
  let i : e ⋙ CategoryTheory.Sigma.desc H ≅ F :=
    i₀.symm ≪≫ Functor.isoWhiskerRight
      (decomposedEquiv (J := J)).counitIso F
  exact (HasColimit.isoOfNatIso i).symm ≪≫
    Functor.Final.colimitIso e (CategoryTheory.Sigma.desc H) ≪≫
      (colimit.isColimit (CategoryTheory.Sigma.desc H)).coconePointUniqueUpToIso
        (decomposedColimitIsColimit H)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem decomposedColimitIso_ι_hom_aux {R : Type u} [CommRing R]
    {J : Type v} [Category.{v'} J]
    (F : J ⥤ ModuleCat.{max v v' w} R)
    (H : ∀ j : ConnectedComponents J,
      j.Component ⥤ ModuleCat.{max v v' w} R)
    (i : (decomposedEquiv (J := J)).inverse ⋙ CategoryTheory.Sigma.desc H ≅ F)
    (X : J) :
    colimit.ι F X ≫
        ((HasColimit.isoOfNatIso i).symm ≪≫
          Functor.Final.colimitIso (decomposedEquiv (J := J)).inverse
            (CategoryTheory.Sigma.desc H) ≪≫
          (colimit.isColimit (CategoryTheory.Sigma.desc H)).coconePointUniqueUpToIso
            (decomposedColimitIsColimit H)).hom =
      i.inv.app X ≫
        (decomposedColimitCocone H).ι.app
          ((decomposedEquiv (J := J)).inverse.obj X) := by
  simp [Category.assoc, HasColimit.isoOfNatIso_ι_inv,
    Functor.Final.ι_colimitIso_hom,
    IsColimit.comp_coconePointUniqueUpToIso_hom]

private def arbitraryModuleShortComplexFirstMap {R : Type u} [CommRing R]
    {K : Type v} [Category.{v'} K]
    (S : K ⥤ ShortComplex (ModuleCat.{w'} R)) :
    (S ⋙ ShortComplex.π₁) ⟶ (S ⋙ ShortComplex.π₂) where
  app i := (S.obj i).f
  naturality _i _j f := (S.map f).comm₁₂

private def arbitraryModuleShortComplexSecondMap {R : Type u} [CommRing R]
    {K : Type v} [Category.{v'} K]
    (S : K ⥤ ShortComplex (ModuleCat.{w'} R)) :
    (S ⋙ ShortComplex.π₂) ⟶ (S ⋙ ShortComplex.π₃) where
  app i := (S.obj i).g
  naturality _i _j f := (S.map f).comm₂₃

private def arbitraryModuleShortComplexColimit {R : Type u} [CommRing R]
    {K : Type v} [Category.{v'} K]
    [HasColimitsOfShape K (AddCommGrpCat.{w'})]
    [HasColimitsOfShape K (ModuleCat.{w'} R)]
    (S : K ⥤ ShortComplex (ModuleCat.{w'} R)) :
    ShortComplex (ModuleCat.{w'} R) :=
  ShortComplex.mk (colim.map (arbitraryModuleShortComplexFirstMap S))
    (colim.map (arbitraryModuleShortComplexSecondMap S)) (by
      apply colimit.hom_ext
      intro i
      rw [← Category.assoc, colimit.ι_map, Category.assoc, colimit.ι_map]
      have hzero :
          (arbitraryModuleShortComplexFirstMap S).app i ≫
              (arbitraryModuleShortComplexSecondMap S).app i = 0 := by
        change (S.obj i).f ≫ (S.obj i).g = 0
        exact (S.obj i).zero
      rw [← Category.assoc, hzero, zero_comp, comp_zero])

private def decomposedShortComplexFamily {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    ConnectedComponents I → ShortComplex (ModuleCat.{max v v' w} R) :=
  fun j =>
    moduleShortComplexColimit
      (inclusion j ⋙ (decomposedEquiv (J := I)).functor ⋙ S)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def decomposedShortComplexIso {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    moduleShortComplexColimit S ≅
      arbitraryModuleShortComplexColimit
        (Discrete.functor (decomposedShortComplexFamily S)) := by
  let D := decomposedShortComplexFamily S
  let e₁ := decomposedColimitIso (S ⋙ ShortComplex.π₁)
  let e₂ := decomposedColimitIso (S ⋙ ShortComplex.π₂)
  let e₃ := decomposedColimitIso (S ⋙ ShortComplex.π₃)
  let H₁ : ∀ j : ConnectedComponents I,
      j.Component ⥤ ModuleCat.{max v v' w} R := fun j =>
    inclusion j ⋙ (decomposedEquiv (J := I)).functor ⋙ S ⋙ ShortComplex.π₁
  let H₂ : ∀ j : ConnectedComponents I,
      j.Component ⥤ ModuleCat.{max v v' w} R := fun j =>
    inclusion j ⋙ (decomposedEquiv (J := I)).functor ⋙ S ⋙ ShortComplex.π₂
  let H₃ : ∀ j : ConnectedComponents I,
      j.Component ⥤ ModuleCat.{max v v' w} R := fun j =>
    inclusion j ⋙ (decomposedEquiv (J := I)).functor ⋙ S ⋙ ShortComplex.π₃
  let b₁ := Discrete.compNatIsoDiscrete D ShortComplex.π₁
  let b₂ := Discrete.compNatIsoDiscrete D ShortComplex.π₂
  let b₃ := Discrete.compNatIsoDiscrete D ShortComplex.π₃
  let a₁ : Discrete.functor (fun j : ConnectedComponents I =>
      colimit (H₁ j)) ≅
      Discrete.functor (ShortComplex.π₁.obj ∘ D) :=
    Discrete.natIso (fun j => by
      dsimp [D, H₁, moduleShortComplexColimit]
      exact Iso.refl _)
  let a₂ : Discrete.functor (fun j : ConnectedComponents I =>
      colimit (H₂ j)) ≅
      Discrete.functor (ShortComplex.π₂.obj ∘ D) :=
    Discrete.natIso (fun j => by
      dsimp [D, H₂, moduleShortComplexColimit]
      exact Iso.refl _)
  let a₃ : Discrete.functor (fun j : ConnectedComponents I =>
      colimit (H₃ j)) ≅
      Discrete.functor (ShortComplex.π₃.obj ∘ D) :=
    Discrete.natIso (fun j => by
      dsimp [D, H₃, moduleShortComplexColimit]
      exact Iso.refl _)
  let d₁ := HasColimit.isoOfNatIso a₁
  let d₂ := HasColimit.isoOfNatIso a₂
  let d₃ := HasColimit.isoOfNatIso a₃
  let c₁ := HasColimit.isoOfNatIso b₁.symm
  let c₂ := HasColimit.isoOfNatIso b₂.symm
  let c₃ := HasColimit.isoOfNatIso b₃.symm
  let i₀₁ : (decomposedEquiv (J := I)).inverse ⋙
      (decomposedEquiv (J := I)).functor ⋙ S ⋙ ShortComplex.π₁ ≅
      (decomposedEquiv (J := I)).inverse ⋙ CategoryTheory.Sigma.desc H₁ :=
    Functor.isoWhiskerLeft (decomposedEquiv (J := I)).inverse
      (Sigma.descUniq H₁ ((decomposedEquiv (J := I)).functor ⋙ S ⋙ ShortComplex.π₁)
        (fun _ => Iso.refl _))
  let i₀₂ : (decomposedEquiv (J := I)).inverse ⋙
      (decomposedEquiv (J := I)).functor ⋙ S ⋙ ShortComplex.π₂ ≅
      (decomposedEquiv (J := I)).inverse ⋙ CategoryTheory.Sigma.desc H₂ :=
    Functor.isoWhiskerLeft (decomposedEquiv (J := I)).inverse
      (Sigma.descUniq H₂ ((decomposedEquiv (J := I)).functor ⋙ S ⋙ ShortComplex.π₂)
        (fun _ => Iso.refl _))
  let i₀₃ : (decomposedEquiv (J := I)).inverse ⋙
      (decomposedEquiv (J := I)).functor ⋙ S ⋙ ShortComplex.π₃ ≅
      (decomposedEquiv (J := I)).inverse ⋙ CategoryTheory.Sigma.desc H₃ :=
    Functor.isoWhiskerLeft (decomposedEquiv (J := I)).inverse
      (Sigma.descUniq H₃ ((decomposedEquiv (J := I)).functor ⋙ S ⋙ ShortComplex.π₃)
        (fun _ => Iso.refl _))
  let i₁ : (decomposedEquiv (J := I)).inverse ⋙ CategoryTheory.Sigma.desc H₁ ≅
      S ⋙ ShortComplex.π₁ :=
    i₀₁.symm ≪≫ Functor.isoWhiskerRight
      (decomposedEquiv (J := I)).counitIso (S ⋙ ShortComplex.π₁)
  let i₂ : (decomposedEquiv (J := I)).inverse ⋙ CategoryTheory.Sigma.desc H₂ ≅
      S ⋙ ShortComplex.π₂ :=
    i₀₂.symm ≪≫ Functor.isoWhiskerRight
      (decomposedEquiv (J := I)).counitIso (S ⋙ ShortComplex.π₂)
  let i₃ : (decomposedEquiv (J := I)).inverse ⋙ CategoryTheory.Sigma.desc H₃ ≅
      S ⋙ ShortComplex.π₃ :=
    i₀₃.symm ≪≫ Functor.isoWhiskerRight
      (decomposedEquiv (J := I)).counitIso (S ⋙ ShortComplex.π₃)
  refine ShortComplex.isoMk
    (by
      let s₁ : (moduleShortComplexColimit S).X₁ ≅
          colimit (S ⋙ ShortComplex.π₁) := by
        dsimp [moduleShortComplexColimit]
        rfl
      let t₁ : colimit ((Discrete.functor D) ⋙ ShortComplex.π₁) ≅
          (arbitraryModuleShortComplexColimit (Discrete.functor D)).X₁ := by
        dsimp [arbitraryModuleShortComplexColimit]
        rfl
      exact s₁ ≪≫ e₁ ≪≫ d₁ ≪≫ c₁ ≪≫ t₁)
    (by
      let s₂ : (moduleShortComplexColimit S).X₂ ≅
          colimit (S ⋙ ShortComplex.π₂) := by
        dsimp [moduleShortComplexColimit]
        rfl
      let t₂ : colimit ((Discrete.functor D) ⋙ ShortComplex.π₂) ≅
          (arbitraryModuleShortComplexColimit (Discrete.functor D)).X₂ := by
        dsimp [arbitraryModuleShortComplexColimit]
        rfl
      exact s₂ ≪≫ e₂ ≪≫ d₂ ≪≫ c₂ ≪≫ t₂)
    (by
      let s₃ : (moduleShortComplexColimit S).X₃ ≅
          colimit (S ⋙ ShortComplex.π₃) := by
        dsimp [moduleShortComplexColimit]
        rfl
      let t₃ : colimit ((Discrete.functor D) ⋙ ShortComplex.π₃) ≅
          (arbitraryModuleShortComplexColimit (Discrete.functor D)).X₃ := by
        dsimp [arbitraryModuleShortComplexColimit]
        rfl
      exact s₃ ≪≫ e₃ ≪≫ d₃ ≪≫ c₃ ≪≫ t₃) ?_ ?_
  · apply colimit.hom_ext
    intro i
    have hι₁ := decomposedColimitIso_ι_hom_aux
      (S ⋙ ShortComplex.π₁) H₁ i₁ i
    have hι₂ := decomposedColimitIso_ι_hom_aux
      (S ⋙ ShortComplex.π₂) H₂ i₂ i
    rw [Category.assoc, hι₁, Category.assoc, colimit.ι_map,
      Category.assoc, hι₂]
    simp [e₁, e₂, b₁, b₂, c₁, c₂, D, H₁, H₂, i₁, i₂,
      arbitraryModuleShortComplexColimit,
      arbitraryModuleShortComplexFirstMap, arbitraryModuleShortComplexSecondMap,
      moduleShortComplexColimit, decomposedColimitCocone]
  · apply colimit.hom_ext
    intro i
    have hι₂ := decomposedColimitIso_ι_hom_aux
      (S ⋙ ShortComplex.π₂) H₂ i₂ i
    have hι₃ := decomposedColimitIso_ι_hom_aux
      (S ⋙ ShortComplex.π₃) H₃ i₃ i
    rw [Category.assoc, hι₂, Category.assoc, colimit.ι_map,
      Category.assoc, hι₃]
    simp [e₂, e₃, b₂, b₃, c₂, c₃, D, H₂, H₃, i₂, i₃,
      arbitraryModuleShortComplexColimit,
      arbitraryModuleShortComplexFirstMap, arbitraryModuleShortComplexSecondMap,
      moduleShortComplexColimit, decomposedColimitCocone]

private def colimit_homology {R : Type u} [CommRing R]
    {K : Type v} [Category.{v'} K]
    [AB5OfSize.{v', v} (AddCommGrpCat.{max v v' w})]
    [HasExactColimitsOfShape K (ModuleCat.{max v v' w} R)]
    (S : K ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    Nonempty
      ((moduleShortComplexColimit S).homology ≅
        colimit (S ⋙ ShortComplex.homologyFunctor
          (ModuleCat.{max v v' w} R))) := by
  have hF : (colim : (K ⥤ ModuleCat.{max v v' w} R) ⥤
      ModuleCat.{max v v' w} R).PreservesHomology := by infer_instance
  let T := ShortComplex.FunctorEquivalence.inverse K
    (ModuleCat.{max v v' w} R)
  let ST := T.obj S
  have hfirst : S.whiskerLeft ShortComplex.π₁Toπ₂ =
      moduleShortComplexFirstMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hsecond : S.whiskerLeft ShortComplex.π₂Toπ₃ =
      moduleShortComplexSecondMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hff : colim.map ST.f = colim.map (moduleShortComplexFirstMap S) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hfirst
  have hgg : colim.map ST.g = colim.map (moduleShortComplexSecondMap S) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hsecond
  let q : ST.map colim ≅ moduleShortComplexColimit S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
        exact hff.symm)
      (by
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
        exact hgg.symm)
  let E := ShortComplex.FunctorEquivalence.functor K
    (ModuleCat.{max v v' w} R)
  let HST := E.obj ST ⋙ ShortComplex.homologyFunctor
    (ModuleCat.{max v v' w} R)
  let p₀ : ST.homology ≅ HST :=
    NatIso.ofComponents (fun i => by
      simpa [HST, E, T, ST, ShortComplex.FunctorEquivalence.functor,
        ShortComplex.FunctorEquivalence.inverse] using
        (ST.mapHomologyIso ((evaluation K (ModuleCat.{max v v' w} R)).obj i)).symm) (by
      intro i j h
      let eᵢ := ST.mapHomologyIso ((evaluation K (ModuleCat.{max v v' w} R)).obj i)
      let eⱼ := ST.mapHomologyIso ((evaluation K (ModuleCat.{max v v' w} R)).obj j)
      change ST.homology.map h ≫ eⱼ.inv =
        eᵢ.inv ≫ ShortComplex.homologyMap (ST.mapNatTrans
          ((evaluation K (ModuleCat.{max v v' w} R)).map h))
      rw [ShortComplex.homologyMap_mapNatTrans]
      change ST.homology.map h ≫ eⱼ.inv =
        eᵢ.inv ≫ eᵢ.hom ≫
          ((evaluation K (ModuleCat.{max v v' w} R)).map h).app ST.homology ≫ eⱼ.inv
      simp)
  let p : ST.homology ≅ S ⋙ ShortComplex.homologyFunctor
      (ModuleCat.{max v v' w} R) :=
    p₀ ≪≫ Functor.isoWhiskerRight
      ((ShortComplex.FunctorEquivalence.counitIso K
        (ModuleCat.{max v v' w} R)).app S)
      (ShortComplex.homologyFunctor (ModuleCat.{max v v' w} R))
  exact ⟨((ShortComplex.homologyFunctor (ModuleCat.{max v v' w} R)).mapIso q).symm ≪≫
    ST.mapHomologyIso colim ≪≫ colim.mapIso p⟩

private def filtered_colimit_homology {R : Type u} [CommRing R]
    {K : Type v} [Category.{v'} K] [IsFiltered K]
    (S : K ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    Nonempty
      ((moduleShortComplexColimit S).homology ≅
        colimit (S ⋙ ShortComplex.homologyFunctor
          (ModuleCat.{max v v' w} R))) := by
  letI : AB5OfSize.{v', v} (AddCommGrpCat.{max v v' w}) :=
    AB5OfSize_of_univLE (AddCommGrpCat.{max v v' w})
  letI : HasExactColimitsOfShape K (ModuleCat.{max v v' w} R) :=
    HasExactColimitsOfShape.domain_of_functor K
      (forget₂ (ModuleCat.{max v v' w} R) AddCommGrpCat)
  exact colimit_homology S

private def filtered_colimit_exact {R : Type u} [CommRing R]
    {K : Type v} [Category.{v'} K] [IsFiltered K]
    (S : K ⥤ ShortComplex (ModuleCat.{max v v' w} R))
    (hS : ∀ i : K, (S.obj i).Exact) :
    (moduleShortComplexColimit S).Exact := by
  letI : AB5OfSize.{v', v} (AddCommGrpCat.{max v v' w}) :=
    AB5OfSize_of_univLE (AddCommGrpCat.{max v v' w})
  letI : HasExactColimitsOfShape K (ModuleCat.{max v v' w} R) :=
    HasExactColimitsOfShape.domain_of_functor K
      (forget₂ (ModuleCat.{max v v' w} R) AddCommGrpCat)
  have hF : (colim : (K ⥤ ModuleCat.{max v v' w} R) ⥤
      ModuleCat.{max v v' w} R).PreservesHomology := by infer_instance
  let T := ShortComplex.FunctorEquivalence.inverse K
    (ModuleCat.{max v v' w} R)
  let ST := T.obj S
  have hST : ST.Exact := by
    apply (ST.exact_iff_isZero_homology).2
    refine { unique_to := ?_, unique_from := ?_ }
    · intro X
      refine ⟨⟨⟨0⟩, ?_⟩⟩
      intro q
      apply NatTrans.ext
      funext i
      change q.app i = ((0 : ST.homology ⟶ X).app i)
      have hi : IsZero (ST.homology.obj i) := by
        let e := (ShortComplex.homologyFunctorIso
          ((evaluation K (ModuleCat.{max v v' w} R)).obj i)).app ST
        apply IsZero.of_iso
          ((ST.map ((evaluation K (ModuleCat.{max v v' w} R)).obj i)).exact_iff_isZero_homology.1
            (hS i)) e.symm
      exact hi.eq_of_src (q.app i) ((0 : ST.homology ⟶ X).app i)
    · intro X
      refine ⟨⟨⟨0⟩, ?_⟩⟩
      intro q
      apply NatTrans.ext
      funext i
      change q.app i = ((0 : X ⟶ ST.homology).app i)
      have hi : IsZero (ST.homology.obj i) := by
        let e := (ShortComplex.homologyFunctorIso
          ((evaluation K (ModuleCat.{max v v' w} R)).obj i)).app ST
        apply IsZero.of_iso
          ((ST.map ((evaluation K (ModuleCat.{max v v' w} R)).obj i)).exact_iff_isZero_homology.1
            (hS i)) e.symm
      exact hi.eq_of_tgt (q.app i) ((0 : X ⟶ ST.homology).app i)
  have hfirst : S.whiskerLeft ShortComplex.π₁Toπ₂ =
      moduleShortComplexFirstMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hsecond : S.whiskerLeft ShortComplex.π₂Toπ₃ =
      moduleShortComplexSecondMap S := by
    apply NatTrans.ext
    funext i
    rfl
  have hff : colim.map ST.f = colim.map (moduleShortComplexFirstMap S) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hfirst
  have hgg : colim.map ST.g = colim.map (moduleShortComplexSecondMap S) := by
    simpa [T, ST, ShortComplex.FunctorEquivalence.inverse] using
      congrArg (fun q => colim.map q) hsecond
  have hcol := colim.exact_mapShortComplex (S := ST) hST
    (c₁ := colimit.cocone ST.X₁)
    (hc₁ := colimit.isColimit ST.X₁)
    (c₂ := colimit.cocone ST.X₂)
    (hc₂ := colimit.isColimit ST.X₂)
    (c₃ := colimit.cocone ST.X₃)
    (hc₃ := colimit.isColimit ST.X₃)
    (f := colim.map ST.f) (g := colim.map ST.g) (hf := by
      intro i
      exact colimit.ι_map ST.f i) (hg := by
      intro i
      exact colimit.ι_map ST.g i)
  change (ShortComplex.mk (colim.map ST.f) (colim.map ST.g) _).Exact at hcol
  apply ShortComplex.exact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_) hcol
  · simpa [moduleShortComplexColimit] using hff.symm
  · simpa [moduleShortComplexColimit] using hgg.symm

theorem almost_directed_colimit_homology {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (hspan : Formalization.Books.Categories.Unit19.HasCoconesForSpans I)
    (heq : Formalization.Books.Categories.Unit19.HasParallelEqualizers I)
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    Nonempty
      ((moduleShortComplexColimit S).homology ≅
        colimit (S ⋙ ShortComplex.homologyFunctor
          (ModuleCat.{max v v' w} R))) := by
  sorry

theorem almost_directed_colimit_exact {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (hspan : Formalization.Books.Categories.Unit19.HasCoconesForSpans I)
    (heq : Formalization.Books.Categories.Unit19.HasParallelEqualizers I)
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R))
    (hS : ∀ i : I, (S.obj i).Exact) :
    (moduleShortComplexColimit S).Exact := by
  sorry

end

end Formalization.Books.Algebra.Unit08
