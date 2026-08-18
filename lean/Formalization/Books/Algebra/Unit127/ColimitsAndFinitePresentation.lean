import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.RingHom.Finite
import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets

/-!
# Commutative Algebra, Chapter 127: Colimits and maps of finite presentation

This file records the source-facing interfaces for the chapter's filtered
colimit and absolute Noetherian approximation statements.  Filtered
colimits of commutative rings and the finiteness predicates are Mathlib's
canonical constructions; the structures below only package the extra
comparison data displayed in the source.
-/

namespace Formalization.Books.Algebra.Unit127

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Filtered colimits of finitely presented algebras -/

/-- An `R`-algebra map regarded as an object of `Under (CommRingCat.of R)`. -/
def underRingHom {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : Under (CommRingCat.of R) :=
  Under.mk (CommRingCat.ofHom f)

/-- The object property of being a finitely presented `R`-algebra. -/
def finitelyPresentedAlgebraProperty (R : Type u) [CommRing R] :
    ObjectProperty (Under (CommRingCat.of R)) :=
  fun A => RingHom.FinitePresentation A.hom.hom

/-- The category of all maps from finitely presented `R`-algebras to `A`.

This is the full subcategory/costructured-arrow presentation of the category
described in the source; it avoids introducing a second category of ring
maps with ad-hoc composition laws.
-/
abbrev FinitelyPresentedAlgebraMapCategory {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) :=
  CostructuredArrow
    (finitelyPresentedAlgebraProperty R).ι (underRingHom f)

/-- The ring-valued diagram underlying the category of finitely presented
`R`-algebra maps into `A`. -/
def finitelyPresentedAlgebraMapDiagram {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : FinitelyPresentedAlgebraMapCategory f ⥤ CommRingCat :=
  CostructuredArrow.proj (finitelyPresentedAlgebraProperty R).ι (underRingHom f) ⋙
    (finitelyPresentedAlgebraProperty R).ι ⋙ Under.forget (CommRingCat.of R)

/-- The canonical cocone to `A` for all finitely presented `R`-algebras mapping
to `A`. -/
def finitelyPresentedAlgebraMapCocone {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : Cocone (finitelyPresentedAlgebraMapDiagram f) where
  pt := CommRingCat.of A
  ι :=
    { app := fun X => (Under.forget (CommRingCat.of R)).map X.hom
      naturality := by
        intro X Y g
        exact (Under.forget (CommRingCat.of R)).congr_map (CostructuredArrow.w g) }

/-- The category of finitely presented `R`-algebra maps into `A` is filtered,
and its tautological cocone has colimit `A`. -/
theorem ringColimitFpCategory {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) :
    IsFiltered (FinitelyPresentedAlgebraMapCategory f) ∧
      Nonempty (IsColimit (finitelyPresentedAlgebraMapCocone f)) := by
  let P := finitelyPresentedAlgebraProperty R
  have hfiltered : IsFiltered (FinitelyPresentedAlgebraMapCategory f) := by
    refine {
      cocone_objs := ?_
      cocone_maps := ?_
      nonempty := ?_ }
    · intro X Y
      let : Algebra (CommRingCat.of R) (X.left.obj.right) := RingHom.toAlgebra X.left.obj.hom.hom
      let : Algebra (CommRingCat.of R) (Y.left.obj.right) := RingHom.toAlgebra Y.left.obj.hom.hom
      let : Algebra (CommRingCat.of R) ((P.ι.obj X.left).right) :=
        RingHom.toAlgebra (P.ι.obj X.left).hom.hom
      let : Algebra (CommRingCat.of R) ((P.ι.obj Y.left).right) :=
        RingHom.toAlgebra (P.ι.obj Y.left).hom.hom
      let T : Under (CommRingCat.of R) :=
        CommRingCat.mkUnder (CommRingCat.of R) ((X.left.obj).right ⊗[R] (Y.left.obj).right)
      have hT : P T := by
        let : Algebra.FinitePresentation R (X.left.obj.right) := X.left.property
        let : Algebra.FinitePresentation R (Y.left.obj.right) := Y.left.property
        let : Algebra.FinitePresentation (X.left.obj.right)
            ((X.left.obj.right) ⊗[R] (Y.left.obj.right)) := Algebra.FinitePresentation.baseChange _
        dsimp [P, finitelyPresentedAlgebraProperty, T]
        exact (RingHom.finitePresentation_algebraMap (A := R)
          (B := (X.left.obj.right) ⊗[R] (Y.left.obj.right))).2
          (Algebra.FinitePresentation.trans R (X.left.obj.right)
            ((X.left.obj.right) ⊗[R] (Y.left.obj.right)))
      let u : X.left.obj ⟶ T := Under.homMk (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := R)
          (A := X.left.obj.right) (B := Y.left.obj.right)))
      let v : Y.left.obj ⟶ T := Under.homMk (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R)
          (A := X.left.obj.right) (B := Y.left.obj.right)).toRingHom) (by
            ext r
            change 1 ⊗ₜ[R] (Y.left.obj.hom.hom r) =
              algebraMap R ((X.left.obj.right) ⊗[R] (Y.left.obj.right)) r
            rw [Algebra.TensorProduct.algebraMap_apply']
            rfl)
      let : Algebra (CommRingCat.of R) A := RingHom.toAlgebra f
      let : IsScalarTower (CommRingCat.of R) (CommRingCat.of R) A := ⟨by
        intro r s a
        exact smul_assoc r s a
      ⟩
      let tx : X.left.obj.right →ₐ[CommRingCat.of R] A := {
        __ := X.hom.right.hom
        commutes' := by
          intro a
          have hw := X.hom.w
          dsimp [underRingHom] at hw
          have hw' := congrArg (fun q => q.hom a) hw
          change X.hom.right.hom (X.left.obj.hom.hom a) = f a at hw'
          change X.hom.right.hom (X.left.obj.hom.hom a) = f a
          exact hw' }
      let ty : Y.left.obj.right →ₐ[CommRingCat.of R] A := {
        __ := Y.hom.right.hom
        commutes' := by
          intro a
          have hw := Y.hom.w
          dsimp [underRingHom] at hw
          have hw' := congrArg (fun q => q.hom a) hw
          change Y.hom.right.hom (Y.left.obj.hom.hom a) = f a at hw'
          change Y.hom.right.hom (Y.left.obj.hom.hom a) = f a
          exact hw' }
      let w : T ⟶ underRingHom f := Under.homMk (CommRingCat.ofHom
        (Algebra.TensorProduct.lift (C := A) tx ty
          (fun _ _ => Commute.all _ _)).toRingHom) (by
            ext r
            change (Algebra.TensorProduct.lift tx ty
              (fun _ _ => Commute.all _ _)) (algebraMap R
                ((X.left.obj.right) ⊗[R] (Y.left.obj.right)) r) = f r
            rw [(Algebra.TensorProduct.lift tx ty
              (fun _ _ => Commute.all _ _)).commutes]
            rfl)
      let Z : FinitelyPresentedAlgebraMapCategory f :=
        CostructuredArrow.mk (Y := ObjectProperty.FullSubcategory.mk T hT) w
      refine ⟨Z, ?_, ?_, trivial⟩
      · exact CostructuredArrow.homMk (P.homMk u) (by
          apply Under.UnderMorphism.ext
          dsimp [u, w]
          ext x
          change ((Algebra.TensorProduct.lift tx ty
            (fun _ _ => Commute.all _ _)).comp
            Algebra.TensorProduct.includeLeft).toRingHom x = _
          rw [Algebra.TensorProduct.lift_comp_includeLeft]
          rfl)
      · exact CostructuredArrow.homMk (P.homMk v) (by
          apply Under.UnderMorphism.ext
          dsimp [v, w]
          ext x
          change ((Algebra.TensorProduct.lift tx ty
            (fun _ _ => Commute.all _ _)).comp
            Algebra.TensorProduct.includeRight).toRingHom x = _
          rw [Algebra.TensorProduct.lift_comp_includeRight']
          rfl)
    · intro X Y g h
      let : Algebra (CommRingCat.of R) X.left.obj.right :=
        RingHom.toAlgebra X.left.obj.hom.hom
      let : Algebra (CommRingCat.of R) Y.left.obj.right :=
        RingHom.toAlgebra Y.left.obj.hom.hom
      let : Algebra (CommRingCat.of R) A := RingHom.toAlgebra f
      obtain ⟨n, p, hp⟩ :=
        Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
          (RingHom.FiniteType.of_finitePresentation X.left.property)
      let d : Fin n → Y.left.obj.right := fun i =>
        g.left.hom.right.hom (p (MvPolynomial.X i)) -
          h.left.hom.right.hom (p (MvPolynomial.X i))
      let I : Ideal Y.left.obj.right := Ideal.span (Set.range d)
      have hI : I.FG := by
        exact Submodule.fg_span (Set.finite_range d)
      let : Algebra.FinitePresentation (CommRingCat.of R) Y.left.obj.right := by
        apply (RingHom.finitePresentation_algebraMap
          (A := CommRingCat.of R) (B := Y.left.obj.right)).mp
        convert Y.left.property using 1; rfl
      let Q : Under (CommRingCat.of R) :=
        CommRingCat.mkUnder (CommRingCat.of R) (Y.left.obj.right ⧸ I)
      let : Algebra (CommRingCat.of R) Q.right := RingHom.toAlgebra Q.hom.hom
      let : Algebra.FinitePresentation (CommRingCat.of R) Q.right :=
        Algebra.FinitePresentation.quotient hI
      have hQ : P Q := by
        dsimp [P, Q, finitelyPresentedAlgebraProperty]
        exact (RingHom.finitePresentation_algebraMap
          (A := CommRingCat.of R) (B := Q.right)).2 inferInstance
      let aY : Y.left.obj.right →+* A := Y.hom.right.hom
      have hg : Y.hom.right.hom.comp g.left.hom.right.hom = X.hom.right.hom := by
        convert congrArg (fun z => z.right.hom) (CostructuredArrow.w g) using 1 <;> rfl
      have hh : Y.hom.right.hom.comp h.left.hom.right.hom = X.hom.right.hom := by
        convert congrArg (fun z => z.right.hom) (CostructuredArrow.w h) using 1 <;> rfl
      have haI : ∀ z : Y.left.obj.right, z ∈ I → aY z = 0 := by
        intro z hz
        have hle : I ≤ RingHom.ker aY := by
          dsimp [I]
          refine Ideal.span_le.2 ?_
          rintro _ ⟨i, rfl⟩
          change aY (d i) = 0
          dsimp [d]
          rw [map_sub]
          have hgi := congrArg (fun z => z (p (MvPolynomial.X i))) hg
          have hhi := congrArg (fun z => z (p (MvPolynomial.X i))) hh
          dsimp [underRingHom] at hgi hhi
          have hgi' : aY (g.left.hom.right.hom (p (MvPolynomial.X i))) =
              X.hom.right.hom (p (MvPolynomial.X i)) := by
            convert hgi using 1; rfl
          have hhi' : aY (h.left.hom.right.hom (p (MvPolynomial.X i))) =
              X.hom.right.hom (p (MvPolynomial.X i)) := by
            convert hhi using 1; rfl
          rw [hgi', hhi']
          exact sub_self _
        exact hle hz
      let b : Q.right →+* A := Ideal.Quotient.lift I aY haI
      let q : Y.left.obj ⟶ Q := Under.homMk (CommRingCat.ofHom
        (Ideal.Quotient.mk I))
      let v : Q ⟶ underRingHom f := Under.homMk (CommRingCat.ofHom b) (by
        ext r
        change b (algebraMap (CommRingCat.of R) Q.right r) = f r
        change b (Ideal.Quotient.mk I (Y.left.obj.hom.hom r)) = f r
        rw [Ideal.Quotient.lift_mk]
        have hw := Y.hom.w
        dsimp [underRingHom] at hw
        have hw' := congrArg (fun z => z.hom r) hw
        change aY (Y.left.obj.hom.hom r) = f r at hw'
        exact hw')
      let Z : FinitelyPresentedAlgebraMapCategory f :=
        CostructuredArrow.mk (Y := ObjectProperty.FullSubcategory.mk Q hQ) v
      let k : Y ⟶ Z := CostructuredArrow.homMk (P.homMk q) (by
        apply Under.UnderMorphism.ext
        dsimp [q, v, b, Z]
        ext x
        change b (Ideal.Quotient.mk I x) = aY x
        dsimp [b]
        rw [Ideal.Quotient.lift_mk])
      refine ⟨Z, k, ?_⟩
      apply CostructuredArrow.hom_ext
      apply ObjectProperty.hom_ext
      apply Under.UnderMorphism.ext
      apply CommRingCat.hom_ext
      ext x
      let qRing : Y.left.obj.right →+* (Y.left.obj.right ⧸ I) := Ideal.Quotient.mk I
      have heq :
          (qRing.comp g.left.hom.right.hom).comp p.toRingHom =
            (qRing.comp h.left.hom.right.hom).comp p.toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp only [RingHom.comp_apply]
          change qRing (g.left.hom.right.hom (p (MvPolynomial.C r))) =
            qRing (h.left.hom.right.hom (p (MvPolynomial.C r)))
          have hpC : p (MvPolynomial.C r) =
              algebraMap (CommRingCat.of R) X.left.obj.right r := by
            exact p.commutes r
          rw [hpC]
          change qRing (g.left.hom.right.hom (X.left.obj.hom.hom r)) =
            qRing (h.left.hom.right.hom (X.left.obj.hom.hom r))
          have hgbase := congrArg (fun z => z.hom r) (Under.w g.left.hom)
          have hhbase := congrArg (fun z => z.hom r) (Under.w h.left.hom)
          dsimp at hgbase hhbase
          rw [hgbase, hhbase]
        · intro i
          simp only [RingHom.comp_apply]
          change Ideal.Quotient.mk I (g.left.hom.right.hom (p (MvPolynomial.X i))) =
            Ideal.Quotient.mk I (h.left.hom.right.hom (p (MvPolynomial.X i)))
          rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
          apply Ideal.subset_span
          exact ⟨i, rfl⟩
      have hqeq : qRing.comp g.left.hom.right.hom = qRing.comp h.left.hom.right.hom := by
        apply RingHom.ext
        intro x
        obtain ⟨z, rfl⟩ := hp x
        exact congrArg (fun t => t z) heq
      dsimp [k, q, Z, Q]
      exact congrArg (fun t => t x) hqeq
    · let B : Under (CommRingCat.of R) := Under.mk (CommRingCat.ofHom (RingHom.id R))
      have hB : P B := by exact RingHom.FinitePresentation.id R
      exact ⟨CostructuredArrow.mk (Y := ObjectProperty.FullSubcategory.mk B hB)
        (Under.homMk (CommRingCat.ofHom f))⟩
  refine ⟨hfiltered, ?_⟩
  let : IsFiltered (FinitelyPresentedAlgebraMapCategory f) := hfiltered
  have hsurj : ∀ a : A, ∃ i xi,
      a = (finitelyPresentedAlgebraMapCocone f).ι.app i xi := by
    intro a
    let : Algebra (CommRingCat.of R) A := RingHom.toAlgebra f
    let B : Under (CommRingCat.of R) :=
      CommRingCat.mkUnder (CommRingCat.of R) (MvPolynomial (Fin 1) R)
    have hB : P B := by
      let : Algebra.FinitePresentation R (MvPolynomial (Fin 1) R) := inferInstance
      dsimp [P, B, finitelyPresentedAlgebraProperty]
      exact (RingHom.finitePresentation_algebraMap
        (A := CommRingCat.of R) (B := MvPolynomial (Fin 1) R)).2 inferInstance
    let evalA : MvPolynomial (Fin 1) R →ₐ[R] A :=
      MvPolynomial.aeval (fun _ => a)
    let m : B ⟶ underRingHom f := Under.homMk (CommRingCat.ofHom evalA.toRingHom) (by
      ext r
      change evalA (algebraMap R (MvPolynomial (Fin 1) R) r) = f r
      rw [evalA.commutes]
      rfl)
    let X : FinitelyPresentedAlgebraMapCategory f :=
      CostructuredArrow.mk (Y := ObjectProperty.FullSubcategory.mk B hB) m
    refine ⟨X, MvPolynomial.X 0, ?_⟩
    change a = evalA (MvPolynomial.X 0)
    rw [show evalA (MvPolynomial.X 0) = a by
      dsimp [evalA]
      rw [MvPolynomial.aeval_X]]
  have htype : IsColimit
      ((forget CommRingCat).mapCocone (finitelyPresentedAlgebraMapCocone f)) := by
    refine Types.FilteredColimit.isColimitOf
      (F := finitelyPresentedAlgebraMapDiagram f ⋙ forget CommRingCat)
      ((forget CommRingCat).mapCocone (finitelyPresentedAlgebraMapCocone f)) ?_ ?_
    · intro a
      change A at a
      obtain ⟨i, xi, hxi⟩ := hsurj a
      refine ⟨i, xi, ?_⟩
      exact hxi
    · intro i j xi xj h
      obtain ⟨z, u, v, _⟩ := hfiltered.cocone_objs i j
      have hu := congrArg (fun q => q.hom xi)
        ((finitelyPresentedAlgebraMapCocone f).w u)
      have hv := congrArg (fun q => q.hom xj)
        ((finitelyPresentedAlgebraMapCocone f).w v)
      dsimp [finitelyPresentedAlgebraMapCocone, finitelyPresentedAlgebraMapDiagram] at hu hv
      have hcommon : z.hom.right.hom (u.left.hom.right.hom xi) =
          z.hom.right.hom (v.left.hom.right.hom xj) := by
        exact hu.trans (h.trans hv.symm)
      let : Algebra (CommRingCat.of R) z.left.obj.right :=
        RingHom.toAlgebra z.left.obj.hom.hom
      let B : Under (CommRingCat.of R) :=
        CommRingCat.mkUnder (CommRingCat.of R) (MvPolynomial (Fin 1) R)
      have hB : P B := by
        let : Algebra.FinitePresentation R (MvPolynomial (Fin 1) R) := inferInstance
        dsimp [P, B, finitelyPresentedAlgebraProperty]
        exact (RingHom.finitePresentation_algebraMap
          (A := CommRingCat.of R) (B := MvPolynomial (Fin 1) R)).2 inferInstance
      let pXi : MvPolynomial (Fin 1) R →ₐ[R] z.left.obj.right :=
        MvPolynomial.aeval (fun _ => u.left.hom.right.hom xi)
      let pXj : MvPolynomial (Fin 1) R →ₐ[R] z.left.obj.right :=
        MvPolynomial.aeval (fun _ => v.left.hom.right.hom xj)
      let uXi : B ⟶ z.left.obj := Under.homMk (CommRingCat.ofHom pXi.toRingHom) (by
        ext r
        change pXi (algebraMap R (MvPolynomial (Fin 1) R) r) =
          z.left.obj.hom.hom r
        rw [pXi.commutes]
        rfl)
      let uXj : B ⟶ z.left.obj := Under.homMk (CommRingCat.ofHom pXj.toRingHom) (by
        ext r
        change pXj (algebraMap R (MvPolynomial (Fin 1) R) r) =
          z.left.obj.hom.hom r
        rw [pXj.commutes]
        rfl)
      let : Algebra (CommRingCat.of R) A := RingHom.toAlgebra f
      let zMap : z.left.obj.right →+* A := by
        dsimp [underRingHom]
        exact z.hom.right.hom
      let zAlg : z.left.obj.right →ₐ[R] A := {
        __ := zMap
        commutes' := by
          intro r
          have hw := z.hom.w
          dsimp [underRingHom] at hw
          have hw' := congrArg (fun q => q.hom r) hw
          change z.hom.right.hom (z.left.obj.hom.hom r) = f r at hw'
          change z.hom.right.hom (z.left.obj.hom.hom r) = f r
          exact hw' }
      let pA : MvPolynomial (Fin 1) R →ₐ[R] A :=
        MvPolynomial.aeval (fun _ => zMap (u.left.hom.right.hom xi))
      have hcompXi : zAlg.comp pXi = pA := by
        apply MvPolynomial.algHom_ext
        intro k
        have hk : k = 0 := Fin.eq_zero k
        subst k
        change zMap (pXi (MvPolynomial.X 0)) = pA (MvPolynomial.X 0)
        rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      have hcompXj : zAlg.comp pXj = pA := by
        apply MvPolynomial.algHom_ext
        intro k
        have hk : k = 0 := Fin.eq_zero k
        subst k
        change zMap (pXj (MvPolynomial.X 0)) = pA (MvPolynomial.X 0)
        rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
        convert hcommon.symm using 1 <;> rfl
      let wA : B ⟶ underRingHom f := Under.homMk (CommRingCat.ofHom pA.toRingHom) (by
        ext r
        change pA (algebraMap R (MvPolynomial (Fin 1) R) r) = f r
        rw [pA.commutes]
        rfl)
      let W : FinitelyPresentedAlgebraMapCategory f :=
        CostructuredArrow.mk (Y := ObjectProperty.FullSubcategory.mk B hB) wA
      have hmapXi : uXi ≫ z.hom = wA := by
        apply Under.UnderMorphism.ext
        apply CommRingCat.hom_ext
        change (zAlg.comp pXi).toRingHom = pA.toRingHom
        exact congrArg AlgHom.toRingHom hcompXi
      have hmapXj : uXj ≫ z.hom = wA := by
        apply Under.UnderMorphism.ext
        apply CommRingCat.hom_ext
        change (zAlg.comp pXj).toRingHom = pA.toRingHom
        exact congrArg AlgHom.toRingHom hcompXj
      let gw : W ⟶ z := CostructuredArrow.homMk (P.homMk uXi) (by
        exact hmapXi)
      let hw : W ⟶ z := CostructuredArrow.homMk (P.homMk uXj) (by
        exact hmapXj)
      obtain ⟨l, t, htq⟩ := hfiltered.cocone_maps gw hw
      refine ⟨l, u ≫ t, v ≫ t, ?_⟩
      have hleft := congrArg
        (fun q => q.left.hom.right.hom (MvPolynomial.X 0)) htq
      dsimp [gw, hw, uXi, uXj] at hleft
      change t.left.hom.right.hom (u.left.hom.right.hom xi) =
        t.left.hom.right.hom (v.left.hom.right.hom xj)
      change t.left.hom.right.hom (pXi (MvPolynomial.X 0)) =
        t.left.hom.right.hom (pXj (MvPolynomial.X 0)) at hleft
      rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X] at hleft
      exact hleft
  have hdesc (s : Cocone (finitelyPresentedAlgebraMapDiagram f))
      (i : FinitelyPresentedAlgebraMapCategory f) (x : i.left.obj.right) :
      htype.desc ((forget CommRingCat).mapCocone s)
          ((finitelyPresentedAlgebraMapCocone f).ι.app i x) =
        s.ι.app i x := by
    have hh := congrArg (fun q => q x)
      (htype.fac ((forget CommRingCat).mapCocone s) i)
    exact hh
  have hrel : ∀ (i j : FinitelyPresentedAlgebraMapCategory f)
      (xi : i.left.obj.right) (xj : j.left.obj.right),
      (finitelyPresentedAlgebraMapCocone f).ι.app i xi =
          (finitelyPresentedAlgebraMapCocone f).ι.app j xj →
        ∃ (k : FinitelyPresentedAlgebraMapCategory f) (g : i ⟶ k) (h : j ⟶ k),
          (finitelyPresentedAlgebraMapDiagram f).map g xi =
            (finitelyPresentedAlgebraMapDiagram f).map h xj := by
    intro i j xi xj h
    apply (Types.FilteredColimit.isColimit_eq_iff
      (finitelyPresentedAlgebraMapDiagram f ⋙ forget CommRingCat) htype).mp
    exact h
  have hsmap (s : Cocone (finitelyPresentedAlgebraMapDiagram f))
      {i k : FinitelyPresentedAlgebraMapCategory f} (g : i ⟶ k)
      (x : i.left.obj.right) :
      s.ι.app i x = s.ι.app k
        ((finitelyPresentedAlgebraMapDiagram f).map g x) := by
    have hh := congrArg (fun q => q.hom x) (s.w g)
    exact hh.symm
  have hcmap {i k : FinitelyPresentedAlgebraMapCategory f} (g : i ⟶ k)
      (x : i.left.obj.right) :
      (finitelyPresentedAlgebraMapCocone f).ι.app i x =
        (finitelyPresentedAlgebraMapCocone f).ι.app k
          ((finitelyPresentedAlgebraMapDiagram f).map g x) := by
    have hh := congrArg (fun q => q.hom x)
      ((finitelyPresentedAlgebraMapCocone f).w g)
    exact hh.symm
  let descRingHom (s : Cocone (finitelyPresentedAlgebraMapDiagram f)) : A →+* s.pt := {
    toFun := htype.desc ((forget CommRingCat).mapCocone s)
    map_one' := by
      obtain ⟨i, xi, hxi⟩ := hsurj (1 : A)
      obtain ⟨k, g, h, heq⟩ := hrel i i xi (1 : i.left.obj.right)
        (hxi.symm.trans ((finitelyPresentedAlgebraMapCocone f).ι.app i).hom.map_one.symm)
      change htype.desc ((forget CommRingCat).mapCocone s) (1 : A) = (1 : s.pt)
      rw [hxi, hdesc s i xi, hsmap s g xi, heq]
      rw [← hsmap s h (1 : i.left.obj.right)]
      exact (s.ι.app i).hom.map_one
    map_mul' := by
      let : CommRing ((forget CommRingCat).mapCocone s).pt :=
        inferInstanceAs (CommRing s.pt)
      intro a b
      obtain ⟨i, xi, hxi⟩ := hsurj a
      obtain ⟨j, xj, hxj⟩ := hsurj b
      obtain ⟨k, g, h, _⟩ := hfiltered.cocone_objs i j
      let aiterm : A := (finitelyPresentedAlgebraMapCocone f).ι.app i xi
      let bjterm : A := (finitelyPresentedAlgebraMapCocone f).ι.app j xj
      have hxiA : a = aiterm := hxi
      have hxjA : b = bjterm := hxj
      let zterm : A := (finitelyPresentedAlgebraMapCocone f).ι.app k
        ((finitelyPresentedAlgebraMapDiagram f).map g xi *
          (finitelyPresentedAlgebraMapDiagram f).map h xj)
      have hprod : a * b = zterm := by
        dsimp [zterm, aiterm, bjterm]
        rw [hxi, hxj, hcmap g xi, hcmap h xj]
        exact ((finitelyPresentedAlgebraMapCocone f).ι.app k).hom.map_mul _ _ |>.symm
      let d : A → s.pt := fun x => htype.desc ((forget CommRingCat).mapCocone s) x
      change d (a * b) = d a * d b
      have hdk := hdesc s k
        ((finitelyPresentedAlgebraMapDiagram f).map g xi *
          (finitelyPresentedAlgebraMapDiagram f).map h xj)
      have hdk' : d zterm = (s.ι.app k).hom
          ((finitelyPresentedAlgebraMapDiagram f).map g xi *
            (finitelyPresentedAlgebraMapDiagram f).map h xj) := by
        dsimp [d, zterm]
        exact hdk
      have hdi := hdesc s i xi
      have hdj := hdesc s j xj
      have hdi' : d aiterm = (s.ι.app i).hom xi := by
        dsimp [d, aiterm]
        exact hdi
      have hdj' : d bjterm = (s.ι.app j).hom xj := by
        dsimp [d, bjterm]
        exact hdj
      rw [hprod, hdk', (s.ι.app k).hom.map_mul, hxiA, hdi', hxjA, hdj',
        hsmap s g xi, hsmap s h xj]
    map_zero' := by
      obtain ⟨i, xi, hxi⟩ := hsurj (0 : A)
      obtain ⟨k, g, h, heq⟩ := hrel i i xi (0 : i.left.obj.right)
        (hxi.symm.trans ((finitelyPresentedAlgebraMapCocone f).ι.app i).hom.map_zero.symm)
      change htype.desc ((forget CommRingCat).mapCocone s) (0 : A) = (0 : s.pt)
      rw [hxi, hdesc s i xi, hsmap s g xi, heq]
      rw [← hsmap s h (0 : i.left.obj.right)]
      exact (s.ι.app i).hom.map_zero
    map_add' := by
      let : CommRing ((forget CommRingCat).mapCocone s).pt :=
        inferInstanceAs (CommRing s.pt)
      intro a b
      obtain ⟨i, xi, hxi⟩ := hsurj a
      obtain ⟨j, xj, hxj⟩ := hsurj b
      obtain ⟨k, g, h, _⟩ := hfiltered.cocone_objs i j
      let aiterm : A := (finitelyPresentedAlgebraMapCocone f).ι.app i xi
      let bjterm : A := (finitelyPresentedAlgebraMapCocone f).ι.app j xj
      have hxiA : a = aiterm := hxi
      have hxjA : b = bjterm := hxj
      let zterm : A := (finitelyPresentedAlgebraMapCocone f).ι.app k
        ((finitelyPresentedAlgebraMapDiagram f).map g xi +
          (finitelyPresentedAlgebraMapDiagram f).map h xj)
      have hplus : a + b = zterm := by
        dsimp [zterm, aiterm, bjterm]
        rw [hxi, hxj, hcmap g xi, hcmap h xj]
        exact ((finitelyPresentedAlgebraMapCocone f).ι.app k).hom.map_add _ _ |>.symm
      let d : A → s.pt := fun x => htype.desc ((forget CommRingCat).mapCocone s) x
      change d (a + b) = d a + d b
      have hdk := hdesc s k
        ((finitelyPresentedAlgebraMapDiagram f).map g xi +
          (finitelyPresentedAlgebraMapDiagram f).map h xj)
      have hdk' : d zterm = (s.ι.app k).hom
          ((finitelyPresentedAlgebraMapDiagram f).map g xi +
            (finitelyPresentedAlgebraMapDiagram f).map h xj) := by
        dsimp [d, zterm]
        exact hdk
      have hdi := hdesc s i xi
      have hdj := hdesc s j xj
      have hdi' : d aiterm = (s.ι.app i).hom xi := by
        dsimp [d, aiterm]
        exact hdi
      have hdj' : d bjterm = (s.ι.app j).hom xj := by
        dsimp [d, bjterm]
        exact hdj
      rw [hplus, hdk', (s.ι.app k).hom.map_add, hxiA, hdi', hxjA, hdj',
        hsmap s g xi, hsmap s h xj]
    }
  refine ⟨{
    desc := fun s => CommRingCat.ofHom (descRingHom s)
    fac := by
      intro s i
      apply CommRingCat.hom_ext
      ext x
      exact hdesc s i x
    uniq := by
      intro s m hm
      apply CommRingCat.hom_ext
      ext a
      obtain ⟨i, xi, hxi⟩ := hsurj a
      rw [hxi]
      have hm' := congrArg (fun q => q.hom xi) (hm i)
      have hd := hdesc s i xi
      exact hm'.trans hd.symm }⟩

/- A directed system of rings is a functor from the canonical preorder
category.  `System` and `IsDirectedSet` are the established Chapter 21
interfaces, reused here rather than duplicated. -/
abbrev RingSystem (I : Type u) [Preorder I] := System I CommRingCat

/-- A directed system of `R`-algebras. -/
abbrev AlgebraSystem (R : Type u) (I : Type u) [Preorder I] [CommRing R] :=
  System I (Under (CommRingCat.of R))

/-- A chosen directed colimit presentation of an `R`-algebra. -/
structure DirectedAlgebraColimit
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) where
  index : Type u
  [indexPreorder : Preorder index]
  directed : IsDirectedSet index
  diagram : AlgebraSystem R index
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  targetIso : cocone.pt ≅ underRingHom f

/-- A selected directed filtered-colimit presentation of an `R`-algebra. -/
structure DirectedFinitelyPresentedAlgebraColimit
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    extends DirectedAlgebraColimit f where
  finitelyPresented : ∀ i, RingHom.FinitePresentation (diagram.obj i).hom.hom

/-- A directed presentation whose transition maps are all surjective. -/
structure DirectedSurjectiveFinitelyPresentedAlgebraColimit
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    extends DirectedFinitelyPresentedAlgebraColimit f where
  transitionSurjective : ∀ {i j : index} (h : i ≤ j),
    Function.Surjective (diagram.map (homOfLE h)).right.hom

private def finitePresentationEval {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (S : Finset A) : MvPolynomial (↑S) R →+* A :=
  MvPolynomial.eval₂Hom f (fun x => (x : A))

private structure finitePresentationData {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) where
  vars : Finset A
  rels : Finset (MvPolynomial (↑vars) R)
  rel_zero : ∀ p ∈ rels, finitePresentationEval f vars p = 0

private def finitePresentationIdeal {R A : Type u} [CommRing R] [CommRing A]
    {f : R →+* A} (i : finitePresentationData f) : Ideal (MvPolynomial (↑i.vars) R) :=
  Ideal.span (i.rels : Set (MvPolynomial (↑i.vars) R))

private abbrev finitePresentationStage {R A : Type u} [CommRing R] [CommRing A]
    {f : R →+* A} (i : finitePresentationData f) : Type u :=
  MvPolynomial (↑i.vars) R ⧸ finitePresentationIdeal i

private def finitePresentationStageMap {R A : Type u} [CommRing R] [CommRing A]
    {f : R →+* A} (i : finitePresentationData f) :
    R →+* finitePresentationStage i :=
  letI : CommRing (finitePresentationStage i) := Ideal.Quotient.commRing _
  (Ideal.Quotient.mk (finitePresentationIdeal i)).comp (algebraMap R (MvPolynomial (↑i.vars) R))

private def finitePresentationInclusion {A : Type u} {S T : Finset A} (h : S ⊆ T) :
    (↑S : Type u) → (↑T : Type u) :=
  fun x => ⟨x.1, h x.2⟩

private def finitePresentationDataLE {R A : Type u} [CommRing R] [CommRing A]
    {f : R →+* A} (i j : finitePresentationData f) : Prop :=
  ∃ h : i.vars ⊆ j.vars,
    ∀ p ∈ i.rels,
      MvPolynomial.rename (finitePresentationInclusion h) p ∈ j.rels

/-- Every ring map is a directed colimit of finitely presented algebras, and a
finite-type target admits a presentation with surjective transitions. -/
theorem ringColimitFp {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) :
    Nonempty (DirectedFinitelyPresentedAlgebraColimit f) ∧
      (f.FiniteType →
        Nonempty (DirectedSurjectiveFinitelyPresentedAlgebraColimit f)) := by
  sorry

/-! ## The compactness criterion -/

/-- A map out of `S` factors through a stage of a directed algebra colimit. -/
def FactorsThroughDirectedAlgebraStage
    {R S I : Type u} [CommRing R] [CommRing S] [Preorder I]
    (f : R →+* S) (D : AlgebraSystem R I)
    (c : Cocone D) (g : underRingHom f ⟶ c.pt) : Prop :=
  ∃ i, ∃ h : underRingHom f ⟶ D.obj i,
    h ≫ c.ι.app i = g

/-- Surjectivity of the comparison from the colimit of `Hom_R(S, -)` to the
hom-set into a directed colimit. -/
def DirectedHomComparisonSurjective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ∀ (I : Type u) [Preorder I] (D : AlgebraSystem R I)
    (_hI : IsDirectedSet I) (c : Cocone D) (_hc : IsColimit c),
    ∀ g : underRingHom f ⟶ c.pt,
      FactorsThroughDirectedAlgebraStage f D c g

/-- The eventual-equality condition for two representatives in the colimit
of hom-sets. -/
def DirectedHomComparisonInjective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ∀ (I : Type u) [Preorder I] (D : AlgebraSystem R I)
    (_hI : IsDirectedSet I) (c : Cocone D) (_hc : IsColimit c)
    {i j : I} (g : underRingHom f ⟶ D.obj i) (h : underRingHom f ⟶ D.obj j),
    g ≫ c.ι.app i = h ≫ c.ι.app j →
      ∃ k : I, ∃ hik : i ≤ k, ∃ hjk : j ≤ k,
        g ≫ D.map (homOfLE hik) = h ≫ D.map (homOfLE hjk)

/-- Bijectivity of the canonical comparison for a directed colimit of
`R`-algebras. -/
def DirectedHomComparisonBijective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  DirectedHomComparisonSurjective f ∧ DirectedHomComparisonInjective f

/-- A ring map is of finite presentation exactly when its hom-functor carries
every directed algebra colimit to the corresponding colimit of hom-sets. -/
theorem characterizeFinitePresentation {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    List.TFAE
      [ f.FinitePresentation,
        DirectedHomComparisonBijective f,
        DirectedHomComparisonSurjective f ] := by
  have hfp_to_bij : f.FinitePresentation → DirectedHomComparisonBijective f := by
    intro hfp
    unfold DirectedHomComparisonBijective DirectedHomComparisonSurjective
      DirectedHomComparisonInjective
    constructor
    · intro I _ D hI c hc g
      let _ : Nonempty I := hI.1
      let _ : IsDirectedOrder I := hI.2
      let _ : IsFiltered I := inferInstance
      let _ : IsFinitelyPresentable (underRingHom f) :=
        CommRingCat.isFinitelyPresentable_under (CommRingCat.of R) (underRingHom f) (by
          convert hfp using 1 <;> rfl)
      obtain ⟨i, q, hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc g
      exact ⟨i, q, hq⟩
    · intro I _ D hI c hc i j g h hgh
      let _ : Nonempty I := hI.1
      let _ : IsDirectedOrder I := hI.2
      let _ : IsFiltered I := inferInstance
      let _ : IsFinitelyPresentable (underRingHom f) :=
        CommRingCat.isFinitelyPresentable_under (CommRingCat.of R) (underRingHom f) (by
          convert hfp using 1 <;> rfl)
      obtain ⟨k, u, v, huv⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hc g h hgh
      refine ⟨k, u.le, v.le, ?_⟩
      change g ≫ D.map u = h ≫ D.map v
      exact huv
  have hsurj_to_fp : DirectedHomComparisonSurjective f → f.FinitePresentation := by
    intro hsur
    obtain ⟨D⟩ := (ringColimitFp f).1
    let _ : Preorder D.index := D.indexPreorder
    obtain ⟨i, q, hq⟩ :=
      hsur D.index D.diagram D.directed D.cocone D.isColimit D.targetIso.inv
    let p : R →+* (D.diagram.obj i).right := (D.diagram.obj i).hom.hom
    let a : S →+* (D.diagram.obj i).right := q.right.hom
    let b : (D.diagram.obj i).right →+* S :=
      (D.cocone.ι.app i ≫ D.targetIso.hom).right.hom
    have ha : a.comp f = p := by
      simpa [p, a, underRingHom] using congrArg (fun z => z.hom) (Under.w q)
    have hq' : q ≫ D.cocone.ι.app i ≫ D.targetIso.hom = 𝟙 _ := by
      rw [← Category.assoc, hq, Iso.inv_hom_id]
    have hba : b.comp a = RingHom.id S := by
      convert congrArg (fun z => z.right.hom) hq' using 1 <;> rfl
    have haft : a.FiniteType :=
      RingHom.FiniteType.of_comp_finiteType (f := f) (by
        rw [ha]
        exact RingHom.FiniteType.of_finitePresentation (D.finitelyPresented i))
    have hbfp : b.FinitePresentation :=
      RingHom.FinitePresentation.of_comp_finiteType a
        (by rw [hba]; exact RingHom.FinitePresentation.id S) haft
    have hbp : (b.comp p).FinitePresentation :=
      RingHom.FinitePresentation.comp hbfp (D.finitelyPresented i)
    have hbf : b.comp p = f := by
      calc
        b.comp p = b.comp (a.comp f) := by rw [ha]
        _ = (b.comp a).comp f := by rfl
        _ = f := by rw [hba, RingHom.id_comp]
    rw [← hbf]
    exact hbp
  rw [List.tfae_cons_cons]
  refine ⟨⟨hfp_to_bij, fun h => hsurj_to_fp h.1⟩, ?_⟩
  rw [List.tfae_cons_cons]
  exact ⟨⟨fun h => h.1, fun h => hfp_to_bij (hsurj_to_fp h)⟩, List.tfae_singleton _⟩

/-! ## Colimits restricted to a prescribed class of algebras -/

/-- A filtered colimit of `R`-algebras whose stages lie in a prescribed set. -/
structure FilteredAlgebraColimitIn
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (E : Set (Under (CommRingCat.of R))) where
  index : Type u
  [indexCategory : Category index]
  [indexFiltered : IsFiltered index]
  diagram : index ⥤ Under (CommRingCat.of R)
  stagesInE : ∀ i, E (diagram.obj i)
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  targetIso : cocone.pt ≅ underRingHom f

/-- The factorization condition through a prescribed class of finitely
presented algebras.  The map `g` is the arbitrary `R`-algebra map into the
target that appears in the source's criterion. -/
def FactorsThroughAlgebraSet
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (E : Set (Under (CommRingCat.of R))) : Prop :=
  ∀ (B : Under (CommRingCat.of R)),
    B.hom.hom.FinitePresentation →
      ∀ (g : B ⟶ underRingHom f),
        ∃ (C : Under (CommRingCat.of R)), E C ∧
          ∃ (u : B ⟶ C) (v : C ⟶ underRingHom f), u ≫ v = g

/-- The class criterion for being a filtered colimit of prescribed finitely
presented algebras. -/
theorem whenColimit {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (E : Set (Under (CommRingCat.of R)))
    (hE : ∀ B, E B → B.hom.hom.FinitePresentation) :
    Nonempty (FilteredAlgebraColimitIn f E) ↔ FactorsThroughAlgebraSet f E := by
  sorry

/-! ## Directed systems of ring maps -/

/- The canonical map from a tensor product to a ring receiving compatible
maps from both factors.  The `letI` binders make the algebra structures
specified by the four ring maps part of the definition rather than an
additional hypothesis at every use site. -/

/-- The map from a stage ring to the represented target ring in a chosen
directed algebra colimit. -/
def DirectedAlgebraColimit.stageToTarget
    {A R : Type u} [CommRing A] [CommRing R] {f : A →+* R}
    (D : DirectedAlgebraColimit f) (i : D.index) :
    letI : Preorder D.index := D.indexPreorder
    (D.diagram.obj i).right →+* R := by
  letI : Preorder D.index := D.indexPreorder
  exact ((D.cocone.ι.app i ≫ D.targetIso.hom).right).hom

/-- The underlying ring at a stage of a directed algebra colimit. -/
abbrev directedStageRing
    {A R : Type u} [CommRing A] [CommRing R] {f : A →+* R}
    (D : DirectedAlgebraColimit f) (i : D.index) : Type u :=
  letI : Preorder D.index := D.indexPreorder
  (D.diagram.obj i).right

/-- The tensor product of an `A`-module with the represented target. -/
def directedTensorTarget
    {A R : Type u} [CommRing A] [CommRing R]
    (f : A →+* R) (M : Type u) [AddCommGroup M] [Module A M] : Type u :=
  letI : Algebra A R := f.toAlgebra
  R ⊗[A] M

instance directedTensorTarget.addCommGroup
    {A R M : Type u} [CommRing A] [CommRing R]
    [AddCommGroup M] [Module A M] (f : A →+* R) :
    AddCommGroup (directedTensorTarget f M) := by
  letI : Algebra A R := f.toAlgebra
  change AddCommGroup (R ⊗[A] M)
  infer_instance

instance directedTensorTarget.moduleBase
    {A R M : Type u} [CommRing A] [CommRing R]
    [AddCommGroup M] [Module A M] (f : A →+* R) :
    Module A (directedTensorTarget f M) := by
  letI : Algebra A R := f.toAlgebra
  change Module A (R ⊗[A] M)
  infer_instance

instance directedTensorTarget.moduleTarget
    {A R M : Type u} [CommRing A] [CommRing R]
    [AddCommGroup M] [Module A M] (f : A →+* R) :
    Module R (directedTensorTarget f M) := by
  letI : Algebra A R := f.toAlgebra
  change Module R (R ⊗[A] M)
  infer_instance

/-- The tensor product of an `A`-module with a stage of a directed algebra
colimit. -/
def directedTensorStage
    {A R : Type u} [CommRing A] [CommRing R]
    {f : A →+* R} (D : DirectedAlgebraColimit f) (M : Type u)
    [AddCommGroup M] [Module A M] (i : D.index) : Type u :=
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra A (D.diagram.obj i).right := (D.diagram.obj i).hom.hom.toAlgebra
  (D.diagram.obj i).right ⊗[A] M

instance directedTensorStage.addCommGroup
    {A R : Type u} [CommRing A] [CommRing R]
    (M : Type u) [AddCommGroup M] [Module A M] {f : A →+* R}
    (D : DirectedAlgebraColimit f) (i : D.index) :
    AddCommGroup (directedTensorStage D M i) := by
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra A (D.diagram.obj i).right := (D.diagram.obj i).hom.hom.toAlgebra
  change AddCommGroup ((D.diagram.obj i).right ⊗[A] M)
  infer_instance

instance directedTensorStage.moduleBase
    {A R : Type u} [CommRing A] [CommRing R]
    (M : Type u) [AddCommGroup M] [Module A M] {f : A →+* R}
    (D : DirectedAlgebraColimit f) (i : D.index) :
    Module A (directedTensorStage D M i) := by
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra A (D.diagram.obj i).right := (D.diagram.obj i).hom.hom.toAlgebra
  change Module A ((D.diagram.obj i).right ⊗[A] M)
  infer_instance

instance directedTensorStage.moduleStage
    {A R : Type u} [CommRing A] [CommRing R]
    (M : Type u) [AddCommGroup M] [Module A M] {f : A →+* R}
    (D : DirectedAlgebraColimit f) (i : D.index) :
    Module (directedStageRing D i) (directedTensorStage D M i) := by
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra A (D.diagram.obj i).right := (D.diagram.obj i).hom.hom.toAlgebra
  change Module (D.diagram.obj i).right ((D.diagram.obj i).right ⊗[A] M)
  infer_instance

/-- Base change of an `A`-linear map to the represented target. -/
def directedTensorMapTarget
    {A R M N : Type u} [CommRing A] [CommRing R]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : A →+* R) (u : M →ₗ[A] N) :
    directedTensorTarget f M →ₗ[A] directedTensorTarget f N := by
  letI : Algebra A R := f.toAlgebra
  exact TensorProduct.AlgebraTensorModule.map (LinearMap.id) u

/-- Base change of an `A`-linear map to a stage of a directed algebra
colimit. -/
def directedTensorMapStage
    {A R M N : Type u} [CommRing A] [CommRing R]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {f : A →+* R} (D : DirectedAlgebraColimit f) (i : D.index)
    (u : M →ₗ[A] N) :
    directedTensorStage D M i →ₗ[A] directedTensorStage D N i := by
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra A (D.diagram.obj i).right := (D.diagram.obj i).hom.hom.toAlgebra
  exact TensorProduct.AlgebraTensorModule.map (LinearMap.id) u

/-- The canonical map from a stage tensor product to the tensor product over
the represented target. -/
def directedTensorStageToTarget
    {A R : Type u} [CommRing A] [CommRing R] {f : A →+* R}
    (D : DirectedAlgebraColimit f) (M : Type u)
    [AddCommGroup M] [Module A M] (i : D.index) :
    directedTensorStage D M i →ₗ[A] directedTensorTarget f M := by
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra A (D.diagram.obj i).right := (D.diagram.obj i).hom.hom.toAlgebra
  letI : Algebra A R := f.toAlgebra
  let g : (D.diagram.obj i).right →ₐ[A] R :=
    { toRingHom := D.stageToTarget i
      commutes' := by
        intro a
        change (D.stageToTarget i) ((D.diagram.obj i).hom.hom a) = f a
        have hw : (D.cocone.ι.app i ≫ D.targetIso.hom).right.hom.comp
            (D.diagram.obj i).hom.hom =
              (underRingHom f).hom.hom := by
          exact congrArg (fun q : CommRingCat.of A ⟶ CommRingCat.of R => q.hom)
            (Under.w (D.cocone.ι.app i ≫ D.targetIso.hom))
        change (D.cocone.ι.app i ≫ D.targetIso.hom).right.hom.comp
            (D.diagram.obj i).hom.hom = f at hw
        exact congrArg (fun q : A →+* R => q a) hw }
  exact TensorProduct.map g.toLinearMap (LinearMap.id)

/-- The stage-linear-map type used in the module descent interface. -/
abbrev directedStageLinearMap
    {A R : Type u} [CommRing A] [CommRing R]
    {f : A →+* R} (D : DirectedAlgebraColimit f) (M N : Type u)
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (i : D.index) : Type u :=
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra A (directedStageRing D i) :=
    (D.diagram.obj i).hom.hom.toAlgebra
  directedTensorStage D M i →ₗ[directedStageRing D i] directedTensorStage D N i

/-- A stage map extends a map at the represented target when the canonical
stage-to-target tensor maps make the square commute. -/
def directedStageLinearMapExtends
    {A R M N : Type u} [CommRing A] [CommRing R]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {f : A →+* R} (D : DirectedAlgebraColimit f) (i : D.index)
    (v : directedTensorTarget f N →ₗ[R] directedTensorTarget f M)
    (vᵢ : directedStageLinearMap D N M i) : Prop :=
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra A (D.diagram.obj i).right := (D.diagram.obj i).hom.hom.toAlgebra
  letI : Algebra A R := f.toAlgebra
  ∀ x, directedTensorStageToTarget D M i (vᵢ x) =
    v (directedTensorStageToTarget D N i x)

/-- The four eventual equality, surjectivity, lifting, and isomorphism
properties for maps of modules through a directed algebra colimit. -/
def moduleMapPropertyInColimit
    {A R M N : Type u} [CommRing A] [CommRing R]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {f : A →+* R} (D : DirectedAlgebraColimit f) : Prop :=
  letI : Preorder D.index := D.indexPreorder
  (∀ (_hM : Module.Finite A M) (u u' : M →ₗ[A] N),
      directedTensorMapTarget f u = directedTensorMapTarget f u' →
        ∃ i, directedTensorMapStage D i u = directedTensorMapStage D i u') ∧
    (∀ (_hN : Module.Finite A N) (u : M →ₗ[A] N),
      Function.Surjective (directedTensorMapTarget f u) →
        ∃ i, Function.Surjective (directedTensorMapStage D i u)) ∧
    (∀ (_hN : Module.FinitePresentation A N)
      (v : directedTensorTarget f N →ₗ[R] directedTensorTarget f M),
      ∃ i, ∃ vᵢ : directedStageLinearMap D N M i,
        directedStageLinearMapExtends D i v vᵢ) ∧
    (∀ (_hM : Module.Finite A M) (_hN : Module.FinitePresentation A N)
      (u : M →ₗ[A] N),
      Function.Bijective (directedTensorMapTarget f u) →
        ∃ i, Function.Bijective (directedTensorMapStage D i u))

/-- Module maps, surjections, lifts, and isomorphisms between finite or
finitely presented modules descend to a sufficiently large stage. -/
theorem moduleMapPropertyInColimit_exists
    {A R M N : Type u} [CommRing A] [CommRing R]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {f : A →+* R} (D : DirectedAlgebraColimit f) :
    moduleMapPropertyInColimit (M := M) (N := N) D := by
  sorry

/-- The tensor-product algebra representing base change to the represented
target ring. -/
abbrev directedAlgebraTensorTarget
    {A R : Type u} [CommRing A] [CommRing R]
    (f : A →+* R) (B : Type u) [CommRing B] [Algebra A B] : Type u :=
  letI : Algebra A R := f.toAlgebra
  R ⊗[A] B

/-- The tensor-product algebra at a stage of a directed algebra colimit. -/
abbrev directedAlgebraTensorStage
    {A R : Type u} [CommRing A] [CommRing R] {f : A →+* R}
    (D : DirectedAlgebraColimit f) (B : Type u) [CommRing B] [Algebra A B]
    (i : D.index) : Type u :=
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra A (D.diagram.obj i).right := (D.diagram.obj i).hom.hom.toAlgebra
  (D.diagram.obj i).right ⊗[A] B

/-- Base change of an `A`-algebra map to the represented target. -/
def directedAlgebraTensorMapTarget
    {A R B C : Type u} [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (f : A →+* R) (u : B →ₐ[A] C) :
    directedAlgebraTensorTarget f B →ₐ[R] directedAlgebraTensorTarget f C := by
  letI : Algebra A R := f.toAlgebra
  exact Algebra.TensorProduct.map (Algebra.ofId R R) u

/-- The underlying ring of a stage in a directed algebra colimit. -/
abbrev directedAlgebraStageRing
    {A R : Type u} [CommRing A] [CommRing R] {f : A →+* R}
    (D : DirectedAlgebraColimit f) (i : D.index) : Type u :=
  letI : Preorder D.index := D.indexPreorder
  (D.diagram.obj i).right

/-- Base change of an `A`-algebra map to a stage. -/
def directedAlgebraTensorMapStage
    {A R B C : Type u} [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {f : A →+* R}
    (D : DirectedAlgebraColimit f) (i : D.index) (u : B →ₐ[A] C) :
    directedAlgebraTensorStage D B i →ₐ[directedAlgebraStageRing D i]
      directedAlgebraTensorStage D C i := by
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra A (D.diagram.obj i).right := (D.diagram.obj i).hom.hom.toAlgebra
  exact Algebra.TensorProduct.map
    (Algebra.ofId (D.diagram.obj i).right (D.diagram.obj i).right) u

/-- The canonical ring map between tensor products induced by a compatible map
on the first factor and the identity on an algebra in the second factor. -/
def baseChangeTensorRingHomOfCompatible
    {A B C X : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing X]
    [Algebra A X]
    (f : A →+* B) (g : A →+* C) (h : B →+* C)
    (compat : h.comp f = g) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A C := g.toAlgebra
    B ⊗[A] X →+* C ⊗[A] X := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A C := g.toAlgebra
  exact Algebra.TensorProduct.mapRingHom
    (R := A) (S := B) (T := X) (R' := A) (S' := C) (T' := X)
    (fR := RingHom.id A) (fS := h) (fT := RingHom.id X)
    (by
      ext a
      change h (f a) = g a
      simpa [RingHom.comp_apply] using congrArg (fun q : A →+* C => q a) compat)
    (by simp)

/-- The canonical ring map from a stage tensor algebra to the represented
target tensor algebra. -/
def directedAlgebraTensorStageToTarget
    {A R B : Type u} [CommRing A] [CommRing R] [CommRing B]
    [Algebra A B] {f : A →+* R} (D : DirectedAlgebraColimit f)
    (i : D.index) :
    directedAlgebraTensorStage D B i →+*
      directedAlgebraTensorTarget f B := by
  letI : Preorder D.index := D.indexPreorder
  letI : Algebra A (D.diagram.obj i).right := (D.diagram.obj i).hom.hom.toAlgebra
  letI : Algebra A R := f.toAlgebra
  have hw : (D.stageToTarget i).comp (D.diagram.obj i).hom.hom = f := by
    have hw0 : (D.stageToTarget i).comp (D.diagram.obj i).hom.hom =
        (underRingHom f).hom.hom := by
      exact congrArg (fun q : CommRingCat.of A ⟶ CommRingCat.of R => q.hom)
        (Under.w (D.cocone.ι.app i ≫ D.targetIso.hom))
    change (D.stageToTarget i).comp (D.diagram.obj i).hom.hom = f at hw0
    exact hw0
  exact baseChangeTensorRingHomOfCompatible (X := B)
    (D.diagram.obj i).hom.hom f (D.stageToTarget i) hw

/-- The four eventual equality, surjectivity, lifting, and isomorphism
properties for maps of algebras through a directed colimit. -/
def algebraMapPropertyInColimit
    {A R B C : Type u} [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {f : A →+* R}
    (D : DirectedAlgebraColimit f) : Prop :=
  letI : Preorder D.index := D.indexPreorder
  (∀ (_hB : RingHom.FiniteType (algebraMap A B)) (u u' : B →ₐ[A] C),
      directedAlgebraTensorMapTarget f u = directedAlgebraTensorMapTarget f u' →
        ∃ i, directedAlgebraTensorMapStage D i u =
          directedAlgebraTensorMapStage D i u') ∧
    (∀ (_hC : RingHom.FiniteType (algebraMap A C)) (u : B →ₐ[A] C),
      Function.Surjective (directedAlgebraTensorMapTarget f u) →
        ∃ i, Function.Surjective (directedAlgebraTensorMapStage D i u)) ∧
    (∀ (_hC : RingHom.FinitePresentation (algebraMap A C))
      (v : directedAlgebraTensorTarget f C →ₐ[R]
        directedAlgebraTensorTarget f B),
      ∃ i, ∃ vᵢ : directedAlgebraTensorStage D C i →ₐ[directedAlgebraStageRing D i]
        directedAlgebraTensorStage D B i,
        ∀ x, directedAlgebraTensorStageToTarget (B := B) D i (vᵢ x) =
          v (directedAlgebraTensorStageToTarget (B := C) D i x)) ∧
    (∀ (_hB : RingHom.FiniteType (algebraMap A B))
      (_hC : RingHom.FinitePresentation (algebraMap A C))
      (u : B →ₐ[A] C),
      Function.Bijective (directedAlgebraTensorMapTarget f u) →
        ∃ i, Function.Bijective (directedAlgebraTensorMapStage D i u))

/-- Algebra maps, surjections, lifts, and isomorphisms between finite or
finitely presented algebras descend to a sufficiently large stage. -/
theorem algebraMapPropertyInColimit_exists
    {A R B C : Type u} [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {f : A →+* R}
    (D : DirectedAlgebraColimit f) :
      algebraMapPropertyInColimit (A := A) (R := R) (B := B) (C := C) D := by
  sorry

/-! ## Finitely presented modules over a directed ring colimit -/

/-- A directed colimit presentation of a commutative ring. -/
structure DirectedRingColimit
    {R : Type u} [CommRing R] where
  index : Type u
  [indexPreorder : Preorder index]
  directed : IsDirectedSet index
  diagram : RingSystem index
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  targetIso : cocone.pt ≅ CommRingCat.of R

/-- The map from a stage of a directed ring colimit to its represented target. -/
def DirectedRingColimit.stageToTarget
    {R : Type u} [CommRing R] (D : DirectedRingColimit (R := R)) (i : D.index) :
    letI : Preorder D.index := D.indexPreorder
    (D.diagram.obj i) →+* R := by
  letI : Preorder D.index := D.indexPreorder
  exact ((D.cocone.ι.app i ≫ D.targetIso.hom)).hom

/-- The transition map between two stages of a directed ring colimit. -/
def DirectedRingColimit.transitionMap
    {R : Type u} [CommRing R] (D : DirectedRingColimit (R := R))
    {i j : D.index} (hij : D.indexPreorder.le i j) :
    letI : Preorder D.index := D.indexPreorder
    (D.diagram.obj i) →+* (D.diagram.obj j) := by
  letI : Preorder D.index := D.indexPreorder
  exact (D.diagram.map (homOfLE hij)).hom

/-- Stage-to-target compatibility for the transition maps of a directed ring
colimit. -/
def DirectedRingColimit.stageCompatibilityWitness
    {R : Type u} [CommRing R] (D : DirectedRingColimit (R := R))
    {i j : D.index} (hij : D.indexPreorder.le i j) :
    PLift ((D.stageToTarget j).comp (D.transitionMap hij) = D.stageToTarget i) := by
  letI : Preorder D.index := D.indexPreorder
  apply PLift.up
  apply congrArg (fun q : CommRingCat.of (D.diagram.obj i) ⟶ CommRingCat.of R => q.hom)
  change D.diagram.map (homOfLE hij) ≫ D.cocone.ι.app j ≫ D.targetIso.hom =
    D.cocone.ι.app i ≫ D.targetIso.hom
  calc
    D.diagram.map (homOfLE hij) ≫ D.cocone.ι.app j ≫ D.targetIso.hom =
        (D.diagram.map (homOfLE hij) ≫ D.cocone.ι.app j) ≫ D.targetIso.hom :=
      (Category.assoc _ _ _).symm
    _ = D.cocone.ι.app i ≫ D.targetIso.hom := by
      rw [D.cocone.ι.naturality (homOfLE hij)]
      simp

theorem DirectedRingColimit.stageCompatibility
    {R : Type u} [CommRing R] (D : DirectedRingColimit (R := R))
    {i j : D.index} (hij : D.indexPreorder.le i j) :
    (D.stageToTarget j).comp (D.transitionMap hij) = D.stageToTarget i :=
  (D.stageCompatibilityWitness hij).down

/-- The canonical linear map induced by compatible maps on the first tensor
factor. -/
def baseChangeLinearMapOfCompatible
    {A B C M : Type u} [CommRing A] [CommRing B] [CommRing C]
    [AddCommGroup M] [Module A M]
    (f : A →+* B) (g : A →+* C) (h : B →+* C)
    (compat : h.comp f = g) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A C := g.toAlgebra
    B ⊗[A] M →ₗ[A] C ⊗[A] M := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A C := g.toAlgebra
  let hh : B →ₐ[A] C :=
    { toRingHom := h
      commutes' := by
        intro a
        change h (f a) = g a
        simpa [RingHom.comp_apply] using congrArg (fun q : A →+* C => q a) compat }
  exact TensorProduct.map hh.toLinearMap (LinearMap.id)

/-- The pointwise expression that a map at a later stage is the base change of
an `R`-linear map at the represented target. -/
def baseChangeLinearMapExtends
    {A B C M N : Type u} [CommRing A] [CommRing B] [CommRing C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : A →+* B) (g : A →+* C) (h : B →+* C)
    (compat : h.comp f = g)
    (v : directedTensorTarget g N →ₗ[C] directedTensorTarget g M)
    (vB : directedTensorTarget f N →ₗ[B] directedTensorTarget f M) : Prop := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A C := g.toAlgebra
  exact ∀ x, baseChangeLinearMapOfCompatible f g h compat (vB x) =
    v (baseChangeLinearMapOfCompatible f g h compat x)

/-- A finitely presented module over a specified commutative ring, with its
carrier and module structures bundled so that it can be moved through the
stage-indexed statements below. -/
structure FpModuleOver (A : Type u) [CommRing A] where
  carrier : Type u
  addCommGroup : AddCommGroup carrier
  module : Module A carrier
  finitePresentation : Module.FinitePresentation A carrier

/-- The type of module maps between two bundled modules before base change. -/
abbrev FpModuleOver.linearMap
    {A : Type u} [CommRing A] (M N : FpModuleOver A) : Type u :=
  letI : AddCommGroup M.carrier := M.addCommGroup
  letI : Module A M.carrier := M.module
  letI : AddCommGroup N.carrier := N.addCommGroup
  letI : Module A N.carrier := N.module
  M.carrier →ₗ[A] N.carrier

/-- The extension-of-scalars carrier of a bundled finitely presented module. -/
abbrev FpModuleOver.baseChange
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (M : FpModuleOver A) : Type u :=
  letI : AddCommGroup M.carrier := M.addCommGroup
  letI : Module A M.carrier := M.module
  directedTensorTarget f M.carrier

/-- The type of linear maps between two base-changed bundled modules. -/
abbrev FpModuleOver.baseChangeMap
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (M N : FpModuleOver A) : Type u :=
  letI : AddCommGroup M.carrier := M.addCommGroup
  letI : Module A M.carrier := M.module
  letI : AddCommGroup N.carrier := N.addCommGroup
  letI : Module A N.carrier := N.module
  FpModuleOver.baseChange f M →ₗ[B] FpModuleOver.baseChange f N

/-- Base change of a module map to the codomain of a ring map. -/
def FpModuleOver.mapBaseChange
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (M N : FpModuleOver A) (u : FpModuleOver.linearMap M N) :
    FpModuleOver.baseChangeMap f M N := by
  letI : Algebra A B := f.toAlgebra
  letI : AddCommGroup M.carrier := M.addCommGroup
  letI : Module A M.carrier := M.module
  letI : AddCommGroup N.carrier := N.addCommGroup
  letI : Module A N.carrier := N.module
  exact TensorProduct.AlgebraTensorModule.map (LinearMap.id) u

/-- The extension condition for a map represented at a later stage, with the
module structures supplied by the bundled source modules. -/
def FpModuleOver.mapBaseChangeExtends
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) (h : B →+* C)
    (compat : h.comp f = g) (M N : FpModuleOver A)
    (v : FpModuleOver.baseChangeMap g M N)
    (vB : FpModuleOver.baseChangeMap f M N) : Prop := by
  letI : AddCommGroup M.carrier := M.addCommGroup
  letI : Module A M.carrier := M.module
  letI : AddCommGroup N.carrier := N.addCommGroup
  letI : Module A N.carrier := N.module
  exact baseChangeLinearMapExtends f g h compat v vB

/-- The three compactness assertions describing the colimit category of
finitely presented modules. -/
theorem colimitCategoryFpModules
    {R : Type u} [CommRing R] (D : DirectedRingColimit (R := R)) :
    (∀ (M : Type u) [AddCommGroup M] [Module R M],
      Module.FinitePresentation R M →
        ∃ i, letI : Preorder D.index := D.indexPreorder
          ∃ Mᵢ : FpModuleOver (D.diagram.obj i),
            Nonempty (FpModuleOver.baseChange (D.stageToTarget i) Mᵢ ≃ₗ[R] M)) ∧
    (∀ (i₀ : D.index), letI : Preorder D.index := D.indexPreorder
      ∀ (M0 N0 : FpModuleOver (D.diagram.obj i₀))
        (φ : FpModuleOver.baseChangeMap (D.stageToTarget i₀) M0 N0),
        ∃ j, ∃ h : D.indexPreorder.le i₀ j,
          ∃ phiStage : FpModuleOver.baseChangeMap (D.transitionMap h) M0 N0,
            FpModuleOver.mapBaseChangeExtends
              (D.transitionMap h) (D.stageToTarget i₀) (D.stageToTarget j)
              (D.stageCompatibility h) M0 N0 φ phiStage) ∧
    (∀ (i₀ : D.index), letI : Preorder D.index := D.indexPreorder
      ∀ (M0 N0 : FpModuleOver (D.diagram.obj i₀))
        (φ ψ : FpModuleOver.linearMap M0 N0),
        FpModuleOver.mapBaseChange (D.stageToTarget i₀) M0 N0 φ =
            FpModuleOver.mapBaseChange (D.stageToTarget i₀) M0 N0 ψ →
          ∃ j, ∃ h : D.indexPreorder.le i₀ j,
            FpModuleOver.mapBaseChange (D.transitionMap h) M0 N0 φ =
              FpModuleOver.mapBaseChange (D.transitionMap h) M0 N0 ψ) := by
  sorry


def baseChangeRingHomOfCompatible
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (compat : h.comp f = k.comp g) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    letI : Algebra R S' := (h.comp f).toAlgebra
    letI : Algebra R' S' := k.toAlgebra
    S ⊗[R] R' →+* S' := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R S' := (h.comp f).toAlgebra
  letI : Algebra R' S' := k.toAlgebra
  let hs : S →ₐ[R] S' :=
    { toRingHom := h
      commutes' := fun r => rfl }
  let hk : R' →ₐ[R] S' :=
    { toRingHom := k
      commutes' := fun r => by
        change k (g r) = h (f r)
        simpa [RingHom.comp_apply] using
          congrArg (fun q : R →+* S' => q r) compat.symm }
  exact (Algebra.TensorProduct.lift hs hk (fun _ _ => Commute.all _ _)).toRingHom

/-- A finitely presented algebra over a specified commutative ring. -/
structure FpAlgebraOver (A : Type u) [CommRing A] where
  carrier : Type u
  commRing : CommRing carrier
  algebra : Algebra A carrier
  finitePresentation : RingHom.FinitePresentation (algebraMap A carrier)

/-- The type of algebra maps between two bundled algebras. -/
abbrev FpAlgebraOver.algHom
    {A : Type u} [CommRing A] (M N : FpAlgebraOver A) : Type u :=
  letI : CommRing M.carrier := M.commRing
  letI : Algebra A M.carrier := M.algebra
  letI : CommRing N.carrier := N.commRing
  letI : Algebra A N.carrier := N.algebra
  M.carrier →ₐ[A] N.carrier

/-- The extension-of-scalars carrier of a bundled finitely presented algebra. -/
abbrev FpAlgebraOver.baseChange
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (M : FpAlgebraOver A) : Type u :=
  letI : CommRing M.carrier := M.commRing
  letI : Algebra A M.carrier := M.algebra
  letI : Algebra A B := f.toAlgebra
  B ⊗[A] M.carrier

/-- The type of algebra maps after extension of scalars. -/
abbrev FpAlgebraOver.baseChangeMap
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (M N : FpAlgebraOver A) : Type u :=
  letI : CommRing M.carrier := M.commRing
  letI : Algebra A M.carrier := M.algebra
  letI : CommRing N.carrier := N.commRing
  letI : Algebra A N.carrier := N.algebra
  letI : Algebra A B := f.toAlgebra
  FpAlgebraOver.baseChange f M →ₐ[B] FpAlgebraOver.baseChange f N

/-- The type of an algebra equivalence from a base change to a bundled target
algebra. -/
abbrev FpAlgebraOver.baseChangeEquiv
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (M : FpAlgebraOver A) (N : FpAlgebraOver B) : Type u :=
  letI : CommRing M.carrier := M.commRing
  letI : Algebra A M.carrier := M.algebra
  letI : CommRing N.carrier := N.commRing
  letI : Algebra B N.carrier := N.algebra
  FpAlgebraOver.baseChange f M ≃ₐ[B] N.carrier

/-- Base change of an algebra map to the codomain of a ring map. -/
def FpAlgebraOver.mapBaseChange
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (M N : FpAlgebraOver A) (u : FpAlgebraOver.algHom M N) :
    FpAlgebraOver.baseChangeMap f M N := by
  letI : CommRing M.carrier := M.commRing
  letI : Algebra A M.carrier := M.algebra
  letI : CommRing N.carrier := N.commRing
  letI : Algebra A N.carrier := N.algebra
  letI : Algebra A B := f.toAlgebra
  exact Algebra.TensorProduct.map (Algebra.ofId B B) u

/-- The extension condition for an algebra map represented at a later stage. -/
def FpAlgebraOver.mapBaseChangeExtends
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) (h : B →+* C)
    (compat : h.comp f = g) (M N : FpAlgebraOver A)
    (v : FpAlgebraOver.baseChangeMap g M N)
    (vB : FpAlgebraOver.baseChangeMap f M N) : Prop := by
  letI : CommRing M.carrier := M.commRing
  letI : Algebra A M.carrier := M.algebra
  letI : CommRing N.carrier := N.commRing
  letI : Algebra A N.carrier := N.algebra
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A C := g.toAlgebra
  exact ∀ x,
    baseChangeTensorRingHomOfCompatible f g h compat (vB x) =
      v (baseChangeTensorRingHomOfCompatible f g h compat x)

/-- The three compactness assertions describing the colimit category of
finitely presented algebras. -/
theorem colimitCategoryFpAlgebras
    {R : Type u} [CommRing R] (D : DirectedRingColimit (R := R)) :
    (∀ A0 : FpAlgebraOver R,
        ∃ i, letI : Preorder D.index := D.indexPreorder
        ∃ Aᵢ : FpAlgebraOver (D.diagram.obj i),
          Nonempty (FpAlgebraOver.baseChangeEquiv (D.stageToTarget i) Aᵢ A0)) ∧
    (∀ (i₀ : D.index), letI : Preorder D.index := D.indexPreorder
      ∀ (A0 B0 : FpAlgebraOver (D.diagram.obj i₀))
        (φ : FpAlgebraOver.baseChangeMap (D.stageToTarget i₀) A0 B0),
        ∃ j, ∃ h : D.indexPreorder.le i₀ j,
          ∃ phiStage : FpAlgebraOver.baseChangeMap (D.transitionMap h) A0 B0,
            FpAlgebraOver.mapBaseChangeExtends
              (D.transitionMap h) (D.stageToTarget i₀) (D.stageToTarget j)
              (D.stageCompatibility h) A0 B0 φ phiStage) ∧
    (∀ (i₀ : D.index), letI : Preorder D.index := D.indexPreorder
      ∀ (A0 B0 : FpAlgebraOver (D.diagram.obj i₀))
        (φ ψ : FpAlgebraOver.algHom A0 B0),
        FpAlgebraOver.mapBaseChange (D.stageToTarget i₀) A0 B0 φ =
            FpAlgebraOver.mapBaseChange (D.stageToTarget i₀) A0 B0 ψ →
          ∃ j, ∃ h : D.indexPreorder.le i₀ j,
            FpAlgebraOver.mapBaseChange (D.transitionMap h) A0 B0 φ =
              FpAlgebraOver.mapBaseChange (D.transitionMap h) A0 B0 ψ) := by
  sorry

/- A directed colimit of ring maps, with both source and target colimits
exhibited.  The natural transformation `map` records the maps at each
stage, while `colimitMap` and `map_fac` record the induced map on colimits. -/
structure DirectedRingMapColimit
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) where
  index : Type u
  [indexPreorder : Preorder index]
  directed : IsDirectedSet index
  sourceDiagram : RingSystem index
  targetDiagram : RingSystem index
  map : sourceDiagram ⟶ targetDiagram
  sourceCocone : Cocone sourceDiagram
  sourceIsColimit : IsColimit sourceCocone
  targetCocone : Cocone targetDiagram
  targetIsColimit : IsColimit targetCocone
  colimitMap : sourceCocone.pt ⟶ targetCocone.pt
  map_fac : ∀ i, sourceCocone.ι.app i ≫ colimitMap =
    map.app i ≫ targetCocone.ι.app i
  sourceIso : sourceCocone.pt ≅ CommRingCat.of R
  targetIso : targetCocone.pt ≅ CommRingCat.of S
  colimitMap_comm : sourceIso.hom ≫ CommRingCat.ofHom f =
    colimitMap ≫ targetIso.hom

/-- The ring map at a stage of a directed ring-map colimit. -/
def DirectedRingMapColimit.stageMap
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) (i : D.index) :
    letI : Preorder D.index := D.indexPreorder
    (D.sourceDiagram.obj i) →+* (D.targetDiagram.obj i) :=
  letI : Preorder D.index := D.indexPreorder
  (D.map.app i).hom

/-- The canonical base-change map attached to a transition in a directed
system of ring maps. -/
def DirectedRingMapColimit.transitionBaseChange
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) {i j : D.index}
    (hij : D.indexPreorder.le i j) :
    letI : Preorder D.index := D.indexPreorder
    letI : Algebra (D.sourceDiagram.obj i) (D.targetDiagram.obj i) :=
      (D.stageMap i).toAlgebra
    letI : Algebra (D.sourceDiagram.obj i) (D.sourceDiagram.obj j) :=
      (D.sourceDiagram.map (homOfLE hij)).hom.toAlgebra
    (D.targetDiagram.obj i) ⊗[D.sourceDiagram.obj i]
        (D.sourceDiagram.obj j) →+* (D.targetDiagram.obj j) := by
  letI : Preorder D.index := D.indexPreorder
  let r := (D.sourceDiagram.map (homOfLE hij)).hom
  let s := (D.targetDiagram.map (homOfLE hij)).hom
  let fi := D.stageMap i
  let fj := D.stageMap j
  apply baseChangeRingHomOfCompatible fi r s fj
  exact congrArg (fun q => q.hom) (D.map.naturality (homOfLE hij)).symm

/-! ## Properties of the transition maps -/

/-- Essential finite presentation, expressed as a finitely presented algebra
followed by localization.  The local approximation theorem below supplies
prime localizations for its transitions separately. -/
def _root_.RingHom.EssFinitePresentation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ∃ (T : Type u) (hT : CommRing T),
    letI : CommRing T := hT
    ∃ (g : R →+* T) (U : Submonoid T) (q : T →+* S),
      g.FinitePresentation ∧ q.comp g = f ∧
        letI : Algebra T S := q.toAlgebra
        IsLocalization U S

/-- The target-ring transition map in a directed ring-map colimit. -/
def DirectedRingMapColimit.targetTransition
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) {i j : D.index}
    (hij : D.indexPreorder.le i j) :
    letI : Preorder D.index := D.indexPreorder
    (D.targetDiagram.obj i) →+* (D.targetDiagram.obj j) := by
  letI : Preorder D.index := D.indexPreorder
  exact (D.targetDiagram.map (homOfLE hij)).hom

/-- The source-stage map to the represented source ring. -/
def DirectedRingMapColimit.sourceStageToTarget
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) (i : D.index) :
    letI : Preorder D.index := D.indexPreorder
    (D.sourceDiagram.obj i) →+* R := by
  letI : Preorder D.index := D.indexPreorder
  exact ((D.sourceCocone.ι.app i ≫ D.sourceIso.hom)).hom

/-- The target-stage map to the represented target ring. -/
def DirectedRingMapColimit.targetStageToTarget
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) (i : D.index) :
    letI : Preorder D.index := D.indexPreorder
    (D.targetDiagram.obj i) →+* S := by
  letI : Preorder D.index := D.indexPreorder
  exact ((D.targetCocone.ι.app i ≫ D.targetIso.hom)).hom

/-- The source stages are essentially of finite type over the integers. -/
def DirectedRingMapColimit.sourceStagesEssFiniteTypeOverInt
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact ∀ i, (Int.castRingHom (D.sourceDiagram.obj i)).EssFiniteType

/-- The target stages are essentially of finite type over their source stages. -/
def DirectedRingMapColimit.targetStagesEssFiniteTypeOverSource
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact ∀ i, (D.stageMap i).EssFiniteType

/-- Every source and target stage in a local approximation is local, and each
stage map is a local homomorphism. -/
def DirectedRingMapColimit.stagesAreLocal
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact (∀ i, IsLocalRing (D.sourceDiagram.obj i)) ∧
    (∀ i, IsLocalRing (D.targetDiagram.obj i)) ∧
    (∀ i, IsLocalHom (D.stageMap i))

/-- A transition map presents its target as a localization of a quotient of
its source. -/
def IsLocalizationOfQuotient
    {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) : Prop :=
  ∃ (I : Ideal R) (U : Submonoid (R ⧸ I)) (q : (R ⧸ I) →+* S),
    q.comp (Ideal.Quotient.mk I) = g ∧
      letI : Algebra (R ⧸ I) S := q.toAlgebra
      IsLocalization U S

/-- A transition map presents its target as localization at a prime of a
quotient of its source. -/
def IsLocalizationAtPrimeOfQuotient
    {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) : Prop :=
  ∃ (I : Ideal R) (p : Ideal (R ⧸ I)) (hp : p.IsPrime)
    (q : (R ⧸ I) →+* S),
    q.comp (Ideal.Quotient.mk I) = g ∧
      letI : Algebra (R ⧸ I) S := q.toAlgebra
      letI : p.IsPrime := hp
      IsLocalization.AtPrime S p

/-- A ring map whose target is localization at a prime of its source.  The
source's finite-presentation approximation uses this exact transition shape. -/
def IsLocalizationAtPrime
    {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) : Prop :=
  ∃ (p : Ideal R) (hp : p.IsPrime),
    letI : Algebra R S := g.toAlgebra
    letI : p.IsPrime := hp
    IsLocalization.AtPrime S p

/-- A ring map whose target is the localization of its source at a submonoid. -/
def IsLocalizationMap
    {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) : Prop :=
  ∃ U : Submonoid R,
    letI : Algebra R S := g.toAlgebra
    IsLocalization U S

/-- All transition base-change maps present the later target as a localization
of a quotient. -/
def DirectedRingMapColimit.transitionsAreLocalizationsOfQuotients
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact ∀ {i j : D.index} (hij : D.indexPreorder.le i j),
    IsLocalizationOfQuotient (D.transitionBaseChange hij)

/-- All transition base-change maps are localizations at primes of their
source tensor products. -/
def DirectedRingMapColimit.transitionsAreLocalizationsAtPrime
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact ∀ {i j : D.index} (hij : D.indexPreorder.le i j),
    IsLocalizationAtPrime (D.transitionBaseChange hij)

/-- Every transition base-change map is surjective. -/
def DirectedRingMapColimit.transitionsAreSurjective
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact ∀ {i j : D.index} (hij : D.indexPreorder.le i j),
    Function.Surjective (D.transitionBaseChange hij)

/-- Every transition base-change map is bijective. -/
def DirectedRingMapColimit.transitionsAreBijective
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact ∀ {i j : D.index} (hij : D.indexPreorder.le i j),
    Function.Bijective (D.transitionBaseChange hij)

/-- Every strict transition base-change map fails to be a localization of its source.
Reflexive transitions are canonical equivalences and therefore localizations. -/
def DirectedRingMapColimit.transitionsAreNotLocalizations
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact ∀ {i j : D.index} (hij : D.indexPreorder.lt i j),
    ¬ IsLocalizationMap (D.transitionBaseChange hij.le)

/-- The source stages are of finite type over the integers. -/
def DirectedRingMapColimit.sourceStagesFiniteTypeOverInt
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact ∀ i, (Int.castRingHom (D.sourceDiagram.obj i)).FiniteType

/-- The target stages are of finite type over their source stages. -/
def DirectedRingMapColimit.targetStagesFiniteTypeOverSource
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact ∀ i, (D.stageMap i).FiniteType

/-- The target stages are finite over their source stages. -/
def DirectedRingMapColimit.targetStagesFinite
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact ∀ i, (D.stageMap i).Finite

/-- A local approximation with essentially finite-type source and target
stages. -/
structure DirectedLocalEssFiniteTypeApproximation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) where
  colimit : DirectedRingMapColimit f
  localStages : colimit.stagesAreLocal
  sourceEssFiniteType : colimit.sourceStagesEssFiniteTypeOverInt
  targetEssFiniteType : colimit.targetStagesEssFiniteTypeOverSource

/-- A local essentially finite-type approximation with quotient-localization
transition maps. -/
structure DirectedLocalEssFiniteTypeWithQuotient
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) where
  base : DirectedLocalEssFiniteTypeApproximation f
  transitionLocalization : base.colimit.transitionsAreLocalizationsOfQuotients

/-- A local essentially finite-presentation approximation with prime-localization
transition maps. -/
structure DirectedLocalEssFinitePresentationApproximation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) where
  base : DirectedLocalEssFiniteTypeApproximation f
  transitionLocalization : base.colimit.transitionsAreLocalizationsAtPrime

/-- A nonlocal finite-type approximation. -/
structure DirectedFiniteTypeApproximation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) where
  colimit : DirectedRingMapColimit f
  sourceFiniteType : colimit.sourceStagesFiniteTypeOverInt
  targetFiniteType : colimit.targetStagesFiniteTypeOverSource

/-- A finite-type approximation with quotient transition maps. -/
structure DirectedFiniteTypeWithQuotient
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) where
  base : DirectedFiniteTypeApproximation f
  transitionQuotient : base.colimit.transitionsAreSurjective

/-- An integral approximation. -/
structure DirectedIntegralApproximation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) where
  colimit : DirectedRingMapColimit f
  sourceFiniteType : colimit.sourceStagesFiniteTypeOverInt
  targetFinite : colimit.targetStagesFinite

/-- A finite-presentation approximation with isomorphic transition maps. -/
structure DirectedFinitePresentationApproximation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) where
  base : DirectedFiniteTypeApproximation f
  transitionIsomorphism : base.colimit.transitionsAreBijective

/-! ## Local and nonlocal approximation theorems -/

private def finiteSubsetSubringDiagram {T : Type u} [CommRing T] :
    Finset T ⥤ CommRingCat where
  obj E := CommRingCat.of (Subring.closure (E : Set T))
  map := fun {E F} hEF => CommRingCat.ofHom {
    toFun := fun x => ⟨x.1, Subring.closure_mono (leOfHom hEF) x.2⟩
    map_one' := rfl
    map_mul' := by intro x y; rfl
    map_zero' := rfl
    map_add' := by intro x y; rfl }
  map_id := by
    intro E
    apply CommRingCat.hom_ext
    ext x
    rfl
  map_comp := by
    intro E F G hEF hFG
    apply CommRingCat.hom_ext
    ext x
    rfl

private def finiteSubsetSubringCocone {T : Type u} [CommRing T] :
    Cocone (finiteSubsetSubringDiagram (T := T)) where
  pt := CommRingCat.of T
  ι := {
    app := fun E => CommRingCat.ofHom {
      toFun := fun x => x.1
      map_one' := rfl
      map_mul' := by intro x y; rfl
      map_zero' := rfl
      map_add' := by intro x y; rfl }
    naturality := by
      intro E F hEF
      apply CommRingCat.hom_ext
      ext x
      rfl }

private theorem finiteSubsetSubringCocone_isColimit {T : Type u} [CommRing T] :
    IsColimit (finiteSubsetSubringCocone (T := T)) := by
  classical
  refine { desc := fun s => (CommRingCat.ofHom {
      toFun := fun x => (s.ι.app {x}).hom
        ⟨x, Subring.subset_closure (s := (↑({x} : Finset T) : Set T)) (by simp)⟩
      map_one' := by
        change (s.ι.app {1}).hom
          (⟨1, Subring.subset_closure (s := (↑({1} : Finset T) : Set T))
            (by simp)⟩ : Subring.closure (↑({1} : Finset T) : Set T)) = 1
        have h1 : (⟨1, Subring.subset_closure (s := (↑({1} : Finset T) : Set T))
            (by simp)⟩ : Subring.closure (↑({1} : Finset T) : Set T)) = 1 :=
          Subtype.ext rfl
        calc
          (s.ι.app {1}).hom
              (⟨1, Subring.subset_closure (s := (↑({1} : Finset T) : Set T))
                (by simp)⟩ : Subring.closure (↑({1} : Finset T) : Set T)) =
              (s.ι.app {1}).hom (1 : Subring.closure (↑({1} : Finset T) : Set T)) :=
            congrArg (s.ι.app {1}).hom h1
          _ = 1 := (s.ι.app {1}).hom.map_one
      map_mul' := by
        intro x y
        let E : Finset T := {x, y, x * y}
        have hx : x ∈ E := by simp [E]
        have hy : y ∈ E := by simp [E]
        have hxy : x * y ∈ (E : Set T) := by simp [E]
        have hxS : x ∈ (↑({x} : Finset T) : Set T) := by simp
        have hyS : y ∈ (↑({y} : Finset T) : Set T) := by simp
        have hxyS : x * y ∈ (↑({x * y} : Finset T) : Set T) := by simp
        have hx₀ : x ∈ (E : Set T) := by simp [E]
        have hy₀ : y ∈ (E : Set T) := by simp [E]
        let h₁ : ({x} : Finset T) ≤ E := by
          intro z hz
          simp only [Finset.mem_singleton.mp hz]
          exact hx
        let h₂ : ({y} : Finset T) ≤ E := by
          intro z hz
          simp only [Finset.mem_singleton.mp hz]
          exact hy
        have hx' : (s.ι.app E).hom
              ⟨x, Subring.subset_closure (s := (E : Set T)) hx₀⟩ =
            (s.ι.app {x}).hom ⟨x, Subring.subset_closure
              (s := (↑({x} : Finset T) : Set T)) hxS⟩ := by
          have h := congrArg (fun k => k.hom
            (⟨x, Subring.subset_closure (s := (↑({x} : Finset T) : Set T)) hxS⟩))
            (s.ι.naturality (homOfLE h₁))
          change (s.ι.app E).hom
              ⟨x, Subring.subset_closure (s := (E : Set T)) hx₀⟩ =
            (s.ι.app {x}).hom
              ⟨x, Subring.subset_closure
                (s := (↑({x} : Finset T) : Set T)) hxS⟩ at h
          exact h
        have hy' : (s.ι.app E).hom
              ⟨y, Subring.subset_closure (s := (E : Set T)) hy₀⟩ =
            (s.ι.app {y}).hom ⟨y, Subring.subset_closure
              (s := (↑({y} : Finset T) : Set T)) hyS⟩ := by
          have h := congrArg (fun k => k.hom
            (⟨y, Subring.subset_closure (s := (↑({y} : Finset T) : Set T)) hyS⟩))
            (s.ι.naturality (homOfLE h₂))
          change (s.ι.app E).hom
              ⟨y, Subring.subset_closure (s := (E : Set T)) hy₀⟩ =
            (s.ι.app {y}).hom
              ⟨y, Subring.subset_closure
                (s := (↑({y} : Finset T) : Set T)) hyS⟩ at h
          exact h
        have hxy' : (s.ι.app E).hom
              ⟨x * y, Subring.subset_closure (s := (E : Set T)) hxy⟩ =
            (s.ι.app {x * y}).hom
              ⟨x * y, Subring.subset_closure
                (s := (↑({x * y} : Finset T) : Set T)) hxyS⟩ := by
          have h := congrArg (fun k => k.hom
            (⟨x * y, Subring.subset_closure
              (s := (↑({x * y} : Finset T) : Set T)) hxyS⟩))
            (s.ι.naturality (homOfLE (show ({x * y} : Finset T) ≤ E by
            intro z hz
            simp only [Finset.mem_singleton.mp hz]
            exact hxy)))
          change (s.ι.app E).hom
              ⟨x * y, Subring.subset_closure (s := (E : Set T)) hxy⟩ =
            (s.ι.app {x * y}).hom
              ⟨x * y, Subring.subset_closure
                (s := (↑({x * y} : Finset T) : Set T)) hxyS⟩ at h
          exact h
        change (s.ι.app {x * y}).hom
            ⟨x * y, Subring.subset_closure
              (s := (↑({x * y} : Finset T) : Set T)) hxyS⟩ = _
        have hmul : (⟨x * y, Subring.subset_closure (s := (E : Set T)) hxy⟩ :
            (finiteSubsetSubringDiagram (T := T)).obj E) =
            (⟨x, Subring.subset_closure (s := (E : Set T)) hx₀⟩ :
              (finiteSubsetSubringDiagram (T := T)).obj E) *
              ⟨y, Subring.subset_closure (s := (E : Set T)) hy₀⟩ := by
          rfl
        calc
          (s.ι.app {x * y}).hom
              ⟨x * y, Subring.subset_closure
                (s := (↑({x * y} : Finset T) : Set T)) hxyS⟩ =
              (s.ι.app E).hom
                ⟨x * y, Subring.subset_closure (s := (E : Set T)) hxy⟩ := hxy'.symm
          _ = (s.ι.app E).hom
                ((⟨x, Subring.subset_closure (s := (E : Set T)) hx₀⟩ :
                  (finiteSubsetSubringDiagram (T := T)).obj E) *
                  ⟨y, Subring.subset_closure (s := (E : Set T)) hy₀⟩) := by rw [hmul]
          _ = (s.ι.app E).hom
                ⟨x, Subring.subset_closure (s := (E : Set T)) hx₀⟩ *
                (s.ι.app E).hom
                  ⟨y, Subring.subset_closure (s := (E : Set T)) hy₀⟩ :=
              (s.ι.app E).hom.map_mul _ _
          _ = _ := by rw [hx', hy']
      map_zero' := by
        change (s.ι.app {0}).hom
          (⟨0, Subring.subset_closure (s := (↑({0} : Finset T) : Set T))
            (by simp)⟩ : Subring.closure (↑({0} : Finset T) : Set T)) = 0
        have h0 : (⟨0, Subring.subset_closure (s := (↑({0} : Finset T) : Set T))
            (by simp)⟩ : Subring.closure (↑({0} : Finset T) : Set T)) = 0 :=
          Subtype.ext rfl
        calc
          (s.ι.app {0}).hom
              (⟨0, Subring.subset_closure (s := (↑({0} : Finset T) : Set T))
                (by simp)⟩ : Subring.closure (↑({0} : Finset T) : Set T)) =
              (s.ι.app {0}).hom (0 : Subring.closure (↑({0} : Finset T) : Set T)) :=
            congrArg (s.ι.app {0}).hom h0
          _ = 0 := (s.ι.app {0}).hom.map_zero
      map_add' := by
        intro x y
        let E : Finset T := {x, y, x + y}
        have hx : x ∈ E := by simp [E]
        have hy : y ∈ E := by simp [E]
        have h₁ : ({x} : Finset T) ≤ E := by
          intro z hz
          simp only [Finset.mem_singleton.mp hz]
          exact hx
        have h₂ : ({y} : Finset T) ≤ E := by
          intro z hz
          simp only [Finset.mem_singleton.mp hz]
          exact hy
        have hx₀ : x ∈ (E : Set T) := by simp [E]
        have hy₀ : y ∈ (E : Set T) := by simp [E]
        have hxy₀ : x + y ∈ (E : Set T) := by simp [E]
        have hxS : x ∈ (↑({x} : Finset T) : Set T) := by simp
        have hyS : y ∈ (↑({y} : Finset T) : Set T) := by simp
        have hxyS : x + y ∈ (↑({x + y} : Finset T) : Set T) := by simp
        have hxy : ({x + y} : Finset T) ≤ E := by
          intro z hz
          simp only [Finset.mem_singleton.mp hz]
          exact hxy₀
        have hx' : (s.ι.app E).hom
              ⟨x, Subring.subset_closure (s := (E : Set T)) hx₀⟩ =
            (s.ι.app {x}).hom ⟨x, Subring.subset_closure
              (s := (↑({x} : Finset T) : Set T)) hxS⟩ := by
          have h := congrArg (fun k => k.hom
            (⟨x, Subring.subset_closure (s := (↑({x} : Finset T) : Set T)) hxS⟩))
            (s.ι.naturality (homOfLE h₁))
          change (s.ι.app E).hom
              ⟨x, Subring.subset_closure (s := (E : Set T)) hx₀⟩ =
            (s.ι.app {x}).hom
              ⟨x, Subring.subset_closure
                (s := (↑({x} : Finset T) : Set T)) hxS⟩ at h
          exact h
        have hy' : (s.ι.app E).hom
              ⟨y, Subring.subset_closure (s := (E : Set T)) hy₀⟩ =
            (s.ι.app {y}).hom ⟨y, Subring.subset_closure
              (s := (↑({y} : Finset T) : Set T)) hyS⟩ := by
          have h := congrArg (fun k => k.hom
            (⟨y, Subring.subset_closure (s := (↑({y} : Finset T) : Set T)) hyS⟩))
            (s.ι.naturality (homOfLE h₂))
          change (s.ι.app E).hom
              ⟨y, Subring.subset_closure (s := (E : Set T)) hy₀⟩ =
            (s.ι.app {y}).hom
              ⟨y, Subring.subset_closure
                (s := (↑({y} : Finset T) : Set T)) hyS⟩ at h
          exact h
        have hxy' : (s.ι.app E).hom
              ⟨x + y, Subring.subset_closure (s := (E : Set T)) hxy₀⟩ =
            (s.ι.app {x + y}).hom
              ⟨x + y, Subring.subset_closure
                (s := (↑({x + y} : Finset T) : Set T)) hxyS⟩ := by
          have h := congrArg (fun k => k.hom
            (⟨x + y, Subring.subset_closure
              (s := (↑({x + y} : Finset T) : Set T)) hxyS⟩))
            (s.ι.naturality (homOfLE hxy))
          change (s.ι.app E).hom
              ⟨x + y, Subring.subset_closure (s := (E : Set T)) hxy₀⟩ =
            (s.ι.app {x + y}).hom
              ⟨x + y, Subring.subset_closure
                (s := (↑({x + y} : Finset T) : Set T)) hxyS⟩ at h
          exact h
        change (s.ι.app {x + y}).hom
            ⟨x + y, Subring.subset_closure
              (s := (↑({x + y} : Finset T) : Set T)) hxyS⟩ = _
        have hadd : (⟨x + y, Subring.subset_closure (s := (E : Set T)) hxy₀⟩ :
            (finiteSubsetSubringDiagram (T := T)).obj E) =
            (⟨x, Subring.subset_closure (s := (E : Set T)) hx₀⟩ :
              (finiteSubsetSubringDiagram (T := T)).obj E) +
              ⟨y, Subring.subset_closure (s := (E : Set T)) hy₀⟩ := by
          rfl
        calc
          (s.ι.app {x + y}).hom
              ⟨x + y, Subring.subset_closure
                (s := (↑({x + y} : Finset T) : Set T)) hxyS⟩ =
              (s.ι.app E).hom
                ⟨x + y, Subring.subset_closure (s := (E : Set T)) hxy₀⟩ := hxy'.symm
          _ = (s.ι.app E).hom
                ((⟨x, Subring.subset_closure (s := (E : Set T)) hx₀⟩ :
                  (finiteSubsetSubringDiagram (T := T)).obj E) +
                  ⟨y, Subring.subset_closure (s := (E : Set T)) hy₀⟩) := by rw [hadd]
          _ = (s.ι.app E).hom
                ⟨x, Subring.subset_closure (s := (E : Set T)) hx₀⟩ +
                (s.ι.app E).hom
                  ⟨y, Subring.subset_closure (s := (E : Set T)) hy₀⟩ :=
              (s.ι.app E).hom.map_add _ _
          _ = _ := by rw [hx', hy']
        }),
    fac := by
      intro s E
      apply CommRingCat.hom_ext
      ext x
      have h := s.ι.naturality (homOfLE (show ({x} : Finset T) ≤ E by simp))
      exact congrArg (fun k => k.hom ⟨x, Subring.subset_closure (by simp)⟩) h
    uniq := by
      intro s m hm
      apply CommRingCat.hom_ext
      ext x
      simpa using congrArg (fun k => k.hom
        ⟨x, Subring.subset_closure (by simp)⟩) (hm {x}) }

/-- Every local homomorphism of local rings is a filtered colimit of local
maps whose stages are essentially of finite type over the integers. -/
theorem limitNoConditionLocal
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] {f : R →+* S} [IsLocalHom f] :
    Nonempty (DirectedLocalEssFiniteTypeApproximation f) := by
  sorry

/-- The local essentially-finite-type approximation with quotient-localization
transition maps. -/
theorem limitEssentiallyFiniteType
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] {f : R →+* S} [IsLocalHom f]
    (hS : f.EssFiniteType) :
    Nonempty (DirectedLocalEssFiniteTypeWithQuotient f) := by
  sorry

/-- The local essentially-finite-presentation approximation with prime
localization transition maps. -/
theorem limitEssentiallyFinitePresentation
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] {f : R →+* S} [IsLocalHom f]
    (hS : f.EssFinitePresentation) :
    Nonempty (DirectedLocalEssFinitePresentationApproximation f) := by
  sorry

/-- The nonlocal absolute finite-type approximation. -/
theorem limitNoCondition
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Nonempty (DirectedFiniteTypeApproximation f) := by
  sorry

/-- The nonlocal approximation for an integral ring map. -/
theorem limitIntegral
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hIntegral : letI : Algebra R S := f.toAlgebra; Algebra.IsIntegral R S) :
    Nonempty (DirectedIntegralApproximation f) := by
  sorry

/-- The nonlocal finite-type approximation with quotient transition maps. -/
theorem limitFiniteType
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (hS : f.FiniteType) :
    Nonempty (DirectedFiniteTypeWithQuotient f) := by
  sorry

/-- The nonlocal finite-presentation approximation with isomorphic transition
maps. -/
theorem limitFinitePresentation
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (hS : f.FinitePresentation) :
    Nonempty (DirectedFinitePresentationApproximation f) := by
  sorry

/-! ## The warning example and module approximation -/

/-- The countable variables in the displayed characteristic-two example. -/
abbrev suitableSystemsPolynomialRing (k : Type u) [CommRing k] :=
  MvPolynomial (Option ℕ) k

/-- The element `z` in the polynomial ring of the warning example. -/
def suitableSystemsZ (k : Type u) [CommRing k] : suitableSystemsPolynomialRing k :=
  MvPolynomial.X none

/-- The element `y_(n+1)` in the polynomial ring of the warning example. -/
def suitableSystemsY (k : Type u) [CommRing k] (n : ℕ) :
    suitableSystemsPolynomialRing k :=
  MvPolynomial.X (some n)

/-- The relations `y_i^2 - z y_(i+1)` in the warning example. -/
def suitableSystemsRelationSet (k : Type u) [CommRing k] :
    Set (suitableSystemsPolynomialRing k) :=
  Set.range (fun n : ℕ =>
    suitableSystemsY k n ^ 2 - suitableSystemsZ k * suitableSystemsY k (n + 1))

/-- The relation ideal in the countable polynomial ring. -/
def suitableSystemsRelationIdeal (k : Type u) [CommRing k] :
    Ideal (suitableSystemsPolynomialRing k) :=
  Ideal.span (suitableSystemsRelationSet k)

/-- The quotient before localizing in the warning example. -/
abbrev suitableSystemsPresentedRing (k : Type u) [CommRing k] :=
  suitableSystemsPolynomialRing k ⧸ suitableSystemsRelationIdeal k

/-- The images of the displayed variables in the presented ring. -/
def suitableSystemsPresentedZ (k : Type u) [CommRing k] :
    suitableSystemsPresentedRing k :=
  Ideal.Quotient.mk (suitableSystemsRelationIdeal k) (suitableSystemsZ k)

def suitableSystemsPresentedY (k : Type u) [CommRing k] (n : ℕ) :
    suitableSystemsPresentedRing k :=
  Ideal.Quotient.mk (suitableSystemsRelationIdeal k) (suitableSystemsY k n)

/-- The maximal ideal at which the displayed quotient is localized. -/
def suitableSystemsMaximalIdeal (k : Type u) [CommRing k] :
    Ideal (suitableSystemsPresentedRing k) :=
  Ideal.span ({suitableSystemsPresentedZ k} ∪
    Set.range (suitableSystemsPresentedY k))

/-- The displayed maximal ideal is prime over a field. -/
theorem suitableSystemsMaximalIdeal_isPrime (k : Type u) [Field k] :
    (suitableSystemsMaximalIdeal k).IsPrime := by
  sorry

/-- The localized ring `R` in the warning example. -/
noncomputable abbrev suitableSystemsLocalizedRing (k : Type u) [Field k] : Type u :=
  letI : (suitableSystemsMaximalIdeal k).IsPrime :=
    suitableSystemsMaximalIdeal_isPrime k
  Localization.AtPrime (suitableSystemsMaximalIdeal k)

instance suitableSystemsLocalizedRing.commRing (k : Type u) [Field k] :
    CommRing (suitableSystemsLocalizedRing k) := by
  letI : (suitableSystemsMaximalIdeal k).IsPrime :=
    suitableSystemsMaximalIdeal_isPrime k
  change CommRing (Localization.AtPrime (suitableSystemsMaximalIdeal k))
  infer_instance

def suitableSystemsLocalizedZ (k : Type u) [Field k] :
    suitableSystemsLocalizedRing k :=
  algebraMap (suitableSystemsPresentedRing k) (suitableSystemsLocalizedRing k)
    (suitableSystemsPresentedZ k)

/-- The quotient `S = R/zR` in the warning example. -/
abbrev suitableSystemsQuotientRing (k : Type u) [Field k] :=
  suitableSystemsLocalizedRing k ⧸ Ideal.span {suitableSystemsLocalizedZ k}

def suitableSystemsQuotientMap (k : Type u) [Field k] :
    suitableSystemsLocalizedRing k →+* suitableSystemsQuotientRing k :=
  Ideal.Quotient.mk _

/-- The polynomial ring used for the finite stage `R_n` in the warning. -/
abbrev suitableSystemsFinitePolynomialRing (k : Type u) [CommRing k] (n : ℕ) :=
  MvPolynomial (Fin (n + 2)) k

def suitableSystemsFiniteZ (k : Type u) [CommRing k] (n : ℕ) :
    suitableSystemsFinitePolynomialRing k n :=
  MvPolynomial.X 0

def suitableSystemsFiniteY (k : Type u) [CommRing k] (n : ℕ) (i : Fin (n + 1)) :
    suitableSystemsFinitePolynomialRing k n :=
  MvPolynomial.X (Fin.succ i)

/-- The finitely many displayed relations in the finite polynomial stage. -/
def suitableSystemsFiniteRelationSet (k : Type u) [CommRing k] (n : ℕ) :
    Set (suitableSystemsFinitePolynomialRing k n) :=
  Set.range (fun i : Fin n =>
    suitableSystemsFiniteY k n i.castSucc ^ 2 - suitableSystemsFiniteZ k n *
      suitableSystemsFiniteY k n i.succ)

def suitableSystemsFiniteRelationIdeal (k : Type u) [CommRing k] (n : ℕ) :
    Ideal (suitableSystemsFinitePolynomialRing k n) :=
  Ideal.span (suitableSystemsFiniteRelationSet k n)

abbrev suitableSystemsFinitePresentedRing (k : Type u) [CommRing k] (n : ℕ) :=
  suitableSystemsFinitePolynomialRing k n ⧸ suitableSystemsFiniteRelationIdeal k n

def suitableSystemsFinitePresentedZ (k : Type u) [CommRing k] (n : ℕ) :
    suitableSystemsFinitePresentedRing k n :=
  Ideal.Quotient.mk (suitableSystemsFiniteRelationIdeal k n) (suitableSystemsFiniteZ k n)

def suitableSystemsFinitePresentedY (k : Type u) [CommRing k] (n : ℕ)
    (i : Fin (n + 1)) : suitableSystemsFinitePresentedRing k n :=
  Ideal.Quotient.mk (suitableSystemsFiniteRelationIdeal k n)
    (suitableSystemsFiniteY k n i)

def suitableSystemsFiniteMaximalIdeal (k : Type u) [CommRing k] (n : ℕ) :
    Ideal (suitableSystemsFinitePresentedRing k n) :=
  Ideal.span ({suitableSystemsFinitePresentedZ k n} ∪
    Set.range (suitableSystemsFinitePresentedY k n))

theorem suitableSystemsFiniteMaximalIdeal_isPrime (k : Type u) [Field k] (n : ℕ) :
    (suitableSystemsFiniteMaximalIdeal k n).IsPrime := by
  sorry

noncomputable abbrev suitableSystemsFiniteLocalizedRing (k : Type u) [Field k] (n : ℕ) :
    Type u :=
  letI : (suitableSystemsFiniteMaximalIdeal k n).IsPrime :=
    suitableSystemsFiniteMaximalIdeal_isPrime k n
  Localization.AtPrime (suitableSystemsFiniteMaximalIdeal k n)

instance suitableSystemsFiniteLocalizedRing.commRing (k : Type u) [Field k] (n : ℕ) :
    CommRing (suitableSystemsFiniteLocalizedRing k n) := by
  letI : (suitableSystemsFiniteMaximalIdeal k n).IsPrime :=
    suitableSystemsFiniteMaximalIdeal_isPrime k n
  change CommRing (Localization.AtPrime (suitableSystemsFiniteMaximalIdeal k n))
  infer_instance

def suitableSystemsFiniteLocalizedZ (k : Type u) [Field k] (n : ℕ) :
    suitableSystemsFiniteLocalizedRing k n :=
  algebraMap (suitableSystemsFinitePresentedRing k n)
    (suitableSystemsFiniteLocalizedRing k n) (suitableSystemsFinitePresentedZ k n)

def suitableSystemsFiniteLocalizedY (k : Type u) [Field k] (n : ℕ)
    (i : Fin (n + 1)) : suitableSystemsFiniteLocalizedRing k n :=
  algebraMap (suitableSystemsFinitePresentedRing k n)
    (suitableSystemsFiniteLocalizedRing k n) (suitableSystemsFinitePresentedY k n i)

/-- The extra relation defining the bad finite quotient `S_n`. -/
def suitableSystemsFiniteBadIdeal (k : Type u) [Field k] (n : ℕ) :
    Ideal (suitableSystemsFiniteLocalizedRing k n) :=
  Ideal.span ({suitableSystemsFiniteLocalizedZ k n} ∪
    {suitableSystemsFiniteLocalizedY k n (Fin.last n) ^ 2})

abbrev suitableSystemsFiniteBadRing (k : Type u) [Field k] (n : ℕ) :=
  suitableSystemsFiniteLocalizedRing k n ⧸ suitableSystemsFiniteBadIdeal k n

/-- The corrected finite quotient `S'_n = R_n/zR_n`. -/
abbrev suitableSystemsFiniteCorrectedRing (k : Type u) [Field k] (n : ℕ) :=
  suitableSystemsFiniteLocalizedRing k n ⧸
    Ideal.span {suitableSystemsFiniteLocalizedZ k n}

/-- Data recording the characteristic-two counterexample showing that an
arbitrary essentially-finite-type local system need not have prime-localization
transition maps.  The displayed polynomial, localization, quotient, and finite
stage rings are named above; the system fields record the bad and corrected
choices of stages. -/
structure SuitableSystemsLimitsWarning where
  k : Type u
  [kField : Field k]
  charTwo : CharP k 2
  badSystem : DirectedRingMapColimit (suitableSystemsQuotientMap k)
  badSystemLocal : badSystem.stagesAreLocal
  badSystemEssentiallyFiniteType :
    badSystem.sourceStagesEssFiniteTypeOverInt ∧
      badSystem.targetStagesEssFiniteTypeOverSource
  badTransitionsNotLocalizations : badSystem.transitionsAreNotLocalizations
  badTransitionsNotIsomorphisms : ¬ badSystem.transitionsAreBijective
  correctedSystem : DirectedRingMapColimit (suitableSystemsQuotientMap k)
  correctedTransitionsAreIsomorphisms : correctedSystem.transitionsAreBijective

/-- The source warning example is available as a mathematical counterexample. -/
theorem suitableSystemsLimitsWarning : Nonempty SuitableSystemsLimitsWarning := by
  sorry

/-- A finite module over a specified commutative ring, bundled as a module
category object. -/
structure FiniteModuleOver (A : Type u) [CommRing A] where
  module : ModuleCat.{u} A
  finite : Module.Finite A module

/-- The source-base-change carrier of a target-stage module. -/
abbrev FiniteModuleOver.baseChangeViaSource
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) (M : FiniteModuleOver S) : Type u :=
  letI : Algebra R S := f.toAlgebra
  letI : Module R (M.module : Type u) := Module.compHom (M.module : Type u) f
  directedTensorTarget g (M.module : Type u)

/-- The module-colimit data attached to a directed ring-map colimit.  The
stage is finite over each target stage, its target base changes form a module
colimit with target `M`, and the transition base changes are isomorphisms. -/
structure DirectedModuleColimitPresentation
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) (M : Type u)
    [AddCommGroup M] [Module S M] where
  stage : ∀ i, letI : Preorder D.index := D.indexPreorder
    FiniteModuleOver (D.targetDiagram.obj i)
  moduleDiagram : letI : Preorder D.index := D.indexPreorder
    D.index ⥤ ModuleCat.{u} S
  cocone : letI : Preorder D.index := D.indexPreorder
    Cocone moduleDiagram
  isColimit : letI : Preorder D.index := D.indexPreorder
    IsColimit cocone
  targetIso : letI : Preorder D.index := D.indexPreorder
    cocone.pt ≅ ModuleCat.of S M
  stageIso : ∀ i, letI : Preorder D.index := D.indexPreorder
    moduleDiagram.obj i ≅
      (ModuleCat.extendScalars (D.targetStageToTarget i)).obj (stage i).module
  stageTargetIso : ∀ i, letI : Preorder D.index := D.indexPreorder
    Nonempty ((ModuleCat.extendScalars (D.targetStageToTarget i)).obj (stage i).module ≅
      ModuleCat.of S M)
  transitionIso : ∀ {i j : D.index} (hij : D.indexPreorder.le i j),
    letI : Preorder D.index := D.indexPreorder
    Nonempty ((ModuleCat.extendScalars (D.targetTransition hij)).obj
      (stage i).module ≅ (stage j).module)

/-- A local module approximation with the prime-localization ring system. -/
structure DirectedLocalModuleEssentiallyFinitePresentation
    {R S M : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [AddCommGroup M] [Module S M] where
  ringApproximation : DirectedLocalEssFinitePresentationApproximation f
  moduleApproximation :
    DirectedModuleColimitPresentation ringApproximation.base.colimit M

/-- A nonlocal module approximation with isomorphic ring and module
transitions. -/
structure DirectedModuleFinitePresentationApproximation
    {R S M : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [AddCommGroup M] [Module S M] where
  ringApproximation : DirectedFinitePresentationApproximation f
  moduleApproximation :
    DirectedModuleColimitPresentation ringApproximation.base.colimit M
  sourceTargetIso : ∀ i, letI : Preorder ringApproximation.base.colimit.index :=
      ringApproximation.base.colimit.indexPreorder
    letI : Module R M := Module.compHom M f
    Nonempty (FiniteModuleOver.baseChangeViaSource
      (ringApproximation.base.colimit.stageMap i)
      (ringApproximation.base.colimit.sourceStageToTarget i)
      (moduleApproximation.stage i) ≃ₗ[R] M)

/-- A finitely presented module over a local essentially-finitely-presented
map descends together with the prime-localization approximation. -/
theorem limitModuleEssentiallyFinitePresentation
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] {f : R →+* S} [IsLocalHom f]
    (hS : f.EssFinitePresentation) [AddCommGroup M] [Module S M]
    (hM : Module.FinitePresentation S M) :
    Nonempty (DirectedLocalModuleEssentiallyFinitePresentation (M := M) f) := by
  sorry

/-- A finitely presented module over a finitely presented map descends with
finite ring stages, isomorphic ring transitions, and isomorphic module
transitions. -/
theorem limitModuleFinitePresentation
    {R S M : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hS : f.FinitePresentation)
    [AddCommGroup M] [Module S M]
    (hM : Module.FinitePresentation S M) :
    Nonempty (DirectedModuleFinitePresentationApproximation (M := M) f) := by
  sorry


/-! ## Module maps in a directed colimit -/

/- The canonical map from a tensor product to a ring receiving compatible
maps from both factors.  The `letI` binders make the algebra structures
specified by the four ring maps part of the definition rather than an
additional hypothesis at every use site. -/

end

end Formalization.Books.Algebra.Unit127
