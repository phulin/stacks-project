import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
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
  sorry

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
  sorry

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
followed by localization at a prime. -/
def _root_.RingHom.EssFinitePresentation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ∃ (T : Type u) (hT : CommRing T),
    letI : CommRing T := hT
    ∃ (g : R →+* T) (p : Ideal T) (hp : p.IsPrime) (q : T →+* S),
      g.FinitePresentation ∧ q.comp g = f ∧
        letI : Algebra T S := q.toAlgebra
        letI : p.IsPrime := hp
        IsLocalization.AtPrime S p

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

/-- All transition base-change maps are localizations at primes of quotients. -/
def DirectedRingMapColimit.transitionsAreLocalizationsAtPrime
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact ∀ {i j : D.index} (hij : D.indexPreorder.le i j),
    IsLocalizationAtPrimeOfQuotient (D.transitionBaseChange hij)

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

/-- Every transition base-change map fails to be a localization of its source. -/
def DirectedRingMapColimit.transitionsAreNotLocalizations
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (D : DirectedRingMapColimit f) : Prop := by
  letI : Preorder D.index := D.indexPreorder
  exact ∀ {i j : D.index} (hij : D.indexPreorder.le i j),
    ¬ IsLocalizationMap (D.transitionBaseChange hij)

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
