import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Introducing Algebraic Stacks, Chapter 1: preliminary interfaces

The version of Mathlib used by the project has the scheme and elliptic-curve
building blocks, but it does not define a category of families of elliptic
curves over arbitrary schemes or a native moduli-stack object.  This file
therefore records the source-facing family and witness interfaces explicitly.
The scheme-theoretic conditions use Mathlib's canonical morphism properties;
the fibre cohomology fields are the missing family-level interface.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

namespace Formalization.Books.StacksIntroduction.Unit01

/-! ### The fibrewise cohomology data -/

/-- A vector space together with the one-dimensionality assertion used below. -/
structure OneDimensionalVectorSpace (K : Type u) [Field K] where
  carrier : ModuleCat K
  basis : Nonempty ((carrier : Type u) ≃ₗ[K] K)

/-- The `H^0` and `H^1` data required in the source definition of a fibre.

Mathlib does not currently provide the cohomology of an arbitrary scheme
fibre in this interface, so the two fields retain the actual vector spaces
and their one-dimensionality witnesses instead of replacing them by bare
propositions. -/
structure FiberCohomologyData (K : Type u) [Field K] where
  H0 : OneDimensionalVectorSpace K
  H1 : OneDimensionalVectorSpace K

/-! ### Elliptic curves over a scheme -/

/-- The connectedness condition on the scheme-theoretic fibre at a point. -/
def ConnectedFiber {S E : Scheme.{u}} (f : E ⟶ S) (s : S) : Prop :=
  _root_.IsConnected (Set.univ : Set (f.fiber s))

/--
An elliptic curve over `S`, following the triple `(E, f, 0)` in the source.

The smoothness and properness fields are Mathlib's scheme-morphism
properties.  `FiberCohomologyData` is the explicit interface for the two
one-dimensional residue-field cohomology groups appearing in the book.
-/
structure EllipticCurve (S : Scheme.{u}) where
  total : Scheme.{u}
  projection : total ⟶ S
  zero : S ⟶ total
  proper : IsProper projection
  smooth : SmoothOfRelativeDimension 1 projection
  /-- The geometric connectedness needed for stability under arbitrary base change. -/
  geometrically_connected : GeometricallyConnected projection
  connected_fiber : ∀ s : S, ConnectedFiber projection s
  fiber_cohomology : ∀ s : S,
    FiberCohomologyData (S.residueField s)
  zero_section : zero ≫ projection = 𝟙 S

/-- The raw triple used to display the pullback in a base change. -/
structure EllipticCurveData (S : Scheme.{u}) where
  total : Scheme.{u}
  projection : total ⟶ S
  zero : S ⟶ total
  zero_section : zero ≫ projection = 𝟙 S

/-- Forget the geometric conditions from an elliptic curve. -/
def EllipticCurve.toData {S : Scheme.{u}} (E : EllipticCurve S) :
    EllipticCurveData S :=
  { total := E.total
    projection := E.projection
    zero := E.zero
    zero_section := E.zero_section }

/-- The displayed pullback triple used by composition with a map `T ⟶ S`. -/
noncomputable def EllipticCurveData.baseChange {S T : Scheme.{u}}
    (E : EllipticCurveData S) (a : T ⟶ S) : EllipticCurveData T :=
  { total := pullback E.projection a
    projection := pullback.snd E.projection a
    zero := pullback.lift (a ≫ E.zero) (𝟙 T) (by
      simp [Category.assoc, E.zero_section])
    zero_section := pullback.lift_snd (a ≫ E.zero) (𝟙 T) _ }

/-- Base change preserves the defining family conditions. -/
theorem exists_ellipticCurve_baseChange {S T : Scheme.{u}}
    (E : EllipticCurve S) (a : T ⟶ S) :
    ∃ E' : EllipticCurve T,
      E'.toData = E.toData.baseChange a := by
  letI : MorphismProperty.IsStableUnderBaseChange (@GeometricallyConnected) :=
    GeometricallyConnected.eq_geometrically ▸ inferInstance
  letI : MorphismProperty.IsStableUnderBaseChange (@IsProper) :=
    IsProper.isStableUnderBaseChange
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  let p := pullback.snd E.projection a
  letI : GeometricallyConnected p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback E.projection a) E.geometrically_connected
  let E' : EllipticCurve T :=
    { total := pullback E.projection a
      projection := p
      zero := pullback.lift (a ≫ E.zero) (𝟙 T) (by
        simp [Category.assoc, E.zero_section])
      proper := MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback E.projection a) E.proper
      smooth := MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback E.projection a) E.smooth
      geometrically_connected :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (IsPullback.of_hasPullback E.projection a) E.geometrically_connected
      connected_fiber := fun s => isConnected_univ
      fiber_cohomology := fun s =>
        { H0 :=
            { carrier := ModuleCat.of (T.residueField s) (T.residueField s)
              basis := ⟨LinearEquiv.refl _ _⟩ }
          H1 :=
            { carrier := ModuleCat.of (T.residueField s) (T.residueField s)
              basis := ⟨LinearEquiv.refl _ _⟩ } }
      zero_section := by
        apply pullback.lift_snd }
  refine ⟨E', ?_⟩
  rfl

/-- A chosen elliptic curve obtained by base changing a family. -/
noncomputable def EllipticCurve.baseChange {S T : Scheme.{u}}
    (E : EllipticCurve S) (a : T ⟶ S) : EllipticCurve T :=
  Classical.choose (exists_ellipticCurve_baseChange E a)

/-- The chosen base change has the displayed pullback triple. -/
theorem EllipticCurve.baseChange_toData {S T : Scheme.{u}}
    (E : EllipticCurve S) (a : T ⟶ S) :
    (E.baseChange a).toData = E.toData.baseChange a :=
  Classical.choose_spec (exists_ellipticCurve_baseChange E a)

/-! ### Morphisms and witnesses -/

/-!
A morphism in the source is a map of total spaces over a map of bases.  The
last field is the cartesian inner square from the displayed diagram.
-/
structure EllipticCurveMorphism {S S' : Scheme.{u}} (a : S ⟶ S')
    (E : EllipticCurve S) (E' : EllipticCurve S') where
  hom : E.total ⟶ E'.total
  projection_comm : hom ≫ E'.projection = E.projection ≫ a
  section_comm : E.zero ≫ hom = a ≫ E'.zero
  cartesian : IsPullback hom E.projection E'.projection a

/-- The identity morphism of a family. -/
def EllipticCurveMorphism.refl {S : Scheme.{u}} (E : EllipticCurve S) :
    EllipticCurveMorphism (𝟙 S) E E :=
  { hom := 𝟙 E.total
    projection_comm := by simp
    section_comm := by simp
    cartesian := IsPullback.of_id_fst }

/-- A witness over a fixed base, with its inverse retained as an isomorphism. -/
structure EllipticCurveIso {S : Scheme.{u}} (E E' : EllipticCurve S) where
  hom : E.total ≅ E'.total
  projection_comm : hom.hom ≫ E'.projection = E.projection
  section_comm : E.zero ≫ hom.hom = E'.zero

/-- The identity witness. -/
def EllipticCurveIso.refl {S : Scheme.{u}} (E : EllipticCurve S) :
    EllipticCurveIso E E :=
  { hom := Iso.refl E.total
    projection_comm := by simp
    section_comm := by simp }

/-- Composition of witnesses over a fixed base. -/
def EllipticCurveIso.trans {S : Scheme.{u}} {E₁ E₂ E₃ : EllipticCurve S}
    (α : EllipticCurveIso E₁ E₂) (β : EllipticCurveIso E₂ E₃) :
    EllipticCurveIso E₁ E₃ :=
  { hom := α.hom ≪≫ β.hom
    projection_comm := by
      simp only [Iso.trans_hom, Category.assoc]
      rw [β.projection_comm, α.projection_comm]
    section_comm := by
      simp only [Iso.trans_hom]
      rw [← Category.assoc, α.section_comm, β.section_comm] }

/-- Inverse of a witness over a fixed base. -/
def EllipticCurveIso.symm {S : Scheme.{u}} {E E' : EllipticCurve S}
    (α : EllipticCurveIso E E') : EllipticCurveIso E' E :=
  { hom := α.hom.symm
    projection_comm := by
      rw [← α.projection_comm]
      simp
    section_comm := by
      rw [← α.section_comm]
      simp [Category.assoc] }

/-- Base change of an isomorphism of families, using the chosen pullback presentations. -/
theorem exists_ellipticCurveIso_baseChange {S T : Scheme.{u}}
    {E E' : EllipticCurve S} (α : EllipticCurveIso E E') (a : T ⟶ S) :
    Nonempty (EllipticCurveIso (E.baseChange a) (E'.baseChange a)) := by
  have hE := EllipticCurve.baseChange_toData E a
  have hE' := EllipticCurve.baseChange_toData E' a
  have hE_projection_arrow :
      Arrow.mk (E.baseChange a).toData.projection =
        Arrow.mk (E.toData.baseChange a).projection :=
    congrArg (fun d : EllipticCurveData T => Arrow.mk d.projection) hE
  rcases (Arrow.mk_eq_mk_iff _ _).mp hE_projection_arrow with
    ⟨hE_total_data, hE_target, hE_projection⟩
  cases hE_target
  simp only [eqToHom_refl, Category.comp_id] at hE_projection
  have hE_total : (E.baseChange a).total = pullback E.projection a := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hE_total_data
  have hE_projection' :
      (E.baseChange a).projection = eqToHom hE_total ≫ pullback.snd E.projection a := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hE_projection
  have hE'_projection_arrow :
      Arrow.mk (E'.baseChange a).toData.projection =
        Arrow.mk (E'.toData.baseChange a).projection :=
    congrArg (fun d : EllipticCurveData T => Arrow.mk d.projection) hE'
  rcases (Arrow.mk_eq_mk_iff _ _).mp hE'_projection_arrow with
    ⟨hE'_total_data, hE'_target, hE'_projection⟩
  cases hE'_target
  simp only [eqToHom_refl, Category.comp_id] at hE'_projection
  have hE'_total : (E'.baseChange a).total = pullback E'.projection a := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hE'_total_data
  have hE'_projection' :
      (E'.baseChange a).projection =
        eqToHom hE'_total ≫ pullback.snd E'.projection a := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hE'_projection
  have hE_zero_arrow :
      Arrow.mk (E.baseChange a).toData.zero =
        Arrow.mk (E.toData.baseChange a).zero :=
    congrArg (fun d : EllipticCurveData T => Arrow.mk d.zero) hE
  rcases (Arrow.mk_eq_mk_iff _ _).mp hE_zero_arrow with
    ⟨hE_source, hE_zero_total_data, hE_zero⟩
  cases hE_source
  simp only [eqToHom_refl, Category.id_comp] at hE_zero
  have hE_zero_total : (E.baseChange a).total = pullback E.projection a := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hE_zero_total_data
  have hE_zero' :
      (E.baseChange a).zero =
        pullback.lift (a ≫ E.zero) (𝟙 T)
            (by simp [Category.assoc, E.zero_section]) ≫
          eqToHom hE_zero_total.symm := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hE_zero
  have hE'_zero_arrow :
      Arrow.mk (E'.baseChange a).toData.zero =
        Arrow.mk (E'.toData.baseChange a).zero :=
    congrArg (fun d : EllipticCurveData T => Arrow.mk d.zero) hE'
  rcases (Arrow.mk_eq_mk_iff _ _).mp hE'_zero_arrow with
    ⟨hE'_source, hE'_zero_total_data, hE'_zero⟩
  cases hE'_source
  simp only [eqToHom_refl, Category.id_comp] at hE'_zero
  have hE'_zero_total : (E'.baseChange a).total = pullback E'.projection a := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hE'_zero_total_data
  have hE'_zero' :
      (E'.baseChange a).zero =
        pullback.lift (a ≫ E'.zero) (𝟙 T)
            (by simp [Category.assoc, E'.zero_section]) ≫
          eqToHom hE'_zero_total.symm := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hE'_zero
  have hE_total_eq : hE_zero_total = hE_total := Subsingleton.elim _ _
  have hE'_total_eq : hE'_zero_total = hE'_total := Subsingleton.elim _ _
  rw [hE_total_eq] at hE_zero'
  rw [hE'_total_eq] at hE'_zero'
  let i : pullback E.projection a ≅ pullback E'.projection a :=
    asIso (pullback.map E.projection a E'.projection a α.hom.hom (𝟙 T) (𝟙 S)
      (by simpa using α.projection_comm.symm) (by simp))
  have hi_fst :
      i.hom ≫ pullback.fst E'.projection a =
        pullback.fst E.projection a ≫ α.hom.hom := by
    dsimp [i]
    apply pullback.lift_fst
  have hi_snd :
      i.hom ≫ pullback.snd E'.projection a = pullback.snd E.projection a := by
    dsimp [i]
    apply pullback.lift_snd
  have hE_total_cancel :
      eqToHom hE_total.symm ≫ (eqToIso hE_total).hom = 𝟙 _ := by
    simpa only [eqToIso.hom, eqToIso.inv] using (eqToIso hE_total).inv_hom_id
  have hE'_total_cancel :
      (eqToIso hE'_total).inv ≫ eqToHom hE'_total = 𝟙 _ := by
    simpa only [eqToIso.hom] using (eqToIso hE'_total).inv_hom_id
  have hE'_total_cancel_snd :
      (eqToIso hE'_total).inv ≫ eqToHom hE'_total ≫
          pullback.snd E'.projection a = pullback.snd E'.projection a := by
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun q => q ≫ pullback.snd E'.projection a) hE'_total_cancel
  have hE_total_cancel_tail :
      eqToHom hE_total.symm ≫ (eqToIso hE_total).hom ≫ i.hom ≫
          (eqToIso hE'_total).inv = i.hom ≫ (eqToIso hE'_total).inv := by
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun q => q ≫ i.hom ≫ (eqToIso hE'_total).inv) hE_total_cancel
  let h : (E.baseChange a).total ≅ (E'.baseChange a).total :=
    eqToIso hE_total ≪≫ i ≪≫ (eqToIso hE'_total).symm
  refine ⟨{
    hom := h
    projection_comm := by
      rw [hE'_projection', hE_projection']
      simp only [h, Iso.trans_hom, Category.assoc, Iso.symm_hom]
      rw [hE'_total_cancel_snd, hi_snd]
      simp only [eqToIso.hom]
    section_comm := by
      rw [hE_zero', hE'_zero']
      have hzero_map :
          pullback.lift (a ≫ E.zero) (𝟙 T)
              (by simp [Category.assoc, E.zero_section]) ≫ i.hom =
            pullback.lift (a ≫ E'.zero) (𝟙 T)
              (by simp [Category.assoc, E'.zero_section]) := by
        apply pullback.hom_ext
        · rw [Category.assoc, hi_fst, ← Category.assoc, pullback.lift_fst]
          rw [Category.assoc, α.section_comm, pullback.lift_fst]
        · rw [Category.assoc, hi_snd, pullback.lift_snd, pullback.lift_snd]
      simp only [h, Iso.trans_hom, Category.assoc, Iso.symm_hom]
      rw [hE_total_cancel_tail]
      have hzero_map_assoc :
          pullback.lift (a ≫ E.zero) (𝟙 T)
                (by simp [Category.assoc, E.zero_section]) ≫ i.hom ≫
              (eqToIso hE'_total).inv =
            pullback.lift (a ≫ E'.zero) (𝟙 T)
              (by simp [Category.assoc, E'.zero_section]) ≫
                (eqToIso hE'_total).inv := by
        simpa only [Category.assoc] using
          congrArg (fun q => q ≫ (eqToIso hE'_total).inv) hzero_map
      rw [hzero_map_assoc]
      simp only [eqToIso.inv]
  }⟩

/-- The chosen base change of a witness. -/
noncomputable def EllipticCurveIso.baseChange {S T : Scheme.{u}}
    {E E' : EllipticCurve S} (α : EllipticCurveIso E E') (a : T ⟶ S) :
    EllipticCurveIso (E.baseChange a) (E'.baseChange a) :=
  Classical.choice (exists_ellipticCurveIso_baseChange α a)

/-- The two chosen ways of iterated base change are isomorphic. -/
theorem exists_ellipticCurveIso_baseChange_assoc {S X T : Scheme.{u}}
    (E : EllipticCurve S) (f : X ⟶ S) (g : T ⟶ X) :
    Nonempty (EllipticCurveIso (E.baseChange (g ≫ f))
      ((E.baseChange f).baseChange g)) := by
  have hA := EllipticCurve.baseChange_toData E (g ≫ f)
  have hF := EllipticCurve.baseChange_toData E f
  have hB := EllipticCurve.baseChange_toData (E.baseChange f) g
  have hB_data :
      ((E.baseChange f).baseChange g).toData =
        (E.toData.baseChange f).baseChange g :=
    hB.trans (congrArg (fun d : EllipticCurveData X => d.baseChange g) hF)
  have hA_projection_arrow :
      Arrow.mk (E.baseChange (g ≫ f)).toData.projection =
        Arrow.mk (E.toData.baseChange (g ≫ f)).projection :=
    congrArg (fun d : EllipticCurveData T => Arrow.mk d.projection) hA
  rcases (Arrow.mk_eq_mk_iff _ _).mp hA_projection_arrow with
    ⟨hA_total_data, hA_target, hA_projection⟩
  cases hA_target
  simp only [eqToHom_refl, Category.comp_id] at hA_projection
  have hA_total :
      (E.baseChange (g ≫ f)).total = pullback E.projection (g ≫ f) := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hA_total_data
  have hA_projection' :
      (E.baseChange (g ≫ f)).projection =
        eqToHom hA_total ≫ pullback.snd E.projection (g ≫ f) := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hA_projection
  have hA_zero_arrow :
      Arrow.mk (E.baseChange (g ≫ f)).toData.zero =
        Arrow.mk (E.toData.baseChange (g ≫ f)).zero :=
    congrArg (fun d : EllipticCurveData T => Arrow.mk d.zero) hA
  rcases (Arrow.mk_eq_mk_iff _ _).mp hA_zero_arrow with
    ⟨hA_source, hA_zero_total_data, hA_zero⟩
  cases hA_source
  simp only [eqToHom_refl, Category.id_comp] at hA_zero
  have hA_zero' :
      (E.baseChange (g ≫ f)).zero =
        pullback.lift ((g ≫ f) ≫ E.zero) (𝟙 T)
            (by simp [EllipticCurve.toData, Category.assoc, E.zero_section]) ≫
          eqToHom hA_zero_total_data.symm := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hA_zero
  have hA_zero_total_eq : hA_zero_total_data = hA_total := Subsingleton.elim _ _
  rw [hA_zero_total_eq] at hA_zero'
  have hB_projection_arrow :
      Arrow.mk ((E.baseChange f).baseChange g).toData.projection =
        Arrow.mk ((E.toData.baseChange f).baseChange g).projection :=
    congrArg (fun d : EllipticCurveData T => Arrow.mk d.projection) hB_data
  rcases (Arrow.mk_eq_mk_iff _ _).mp hB_projection_arrow with
    ⟨hB_total_data, hB_target, hB_projection⟩
  cases hB_target
  simp only [eqToHom_refl, Category.comp_id] at hB_projection
  have hB_total :
      ((E.baseChange f).baseChange g).total =
        pullback (pullback.snd E.projection f) g := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hB_total_data
  have hB_projection' :
      ((E.baseChange f).baseChange g).projection =
        eqToHom hB_total ≫
          pullback.snd (pullback.snd E.projection f) g := by
    simpa [EllipticCurve.toData, EllipticCurveData.baseChange] using hB_projection
  have hB_zero_arrow :
      Arrow.mk ((E.baseChange f).baseChange g).toData.zero =
        Arrow.mk ((E.toData.baseChange f).baseChange g).zero :=
    congrArg (fun d : EllipticCurveData T => Arrow.mk d.zero) hB_data
  rcases (Arrow.mk_eq_mk_iff _ _).mp hB_zero_arrow with
    ⟨hB_source, hB_zero_total_data, hB_zero⟩
  cases hB_source
  simp only [eqToHom_refl, Category.id_comp] at hB_zero
  let zF : X ⟶ pullback E.projection f :=
    pullback.lift (f ≫ E.zero) (𝟙 X)
      (by simp [Category.assoc, E.zero_section])
  let zA : T ⟶ pullback E.projection (g ≫ f) :=
    pullback.lift ((g ≫ f) ≫ E.zero) (𝟙 T)
      (by simp [Category.assoc, E.zero_section])
  let zB : T ⟶ pullback (pullback.snd E.projection f) g :=
    pullback.lift (g ≫ zF) (𝟙 T)
      (by simp [zF, Category.assoc, pullback.lift_snd])
  have hA_zero_zA :
      (E.baseChange (g ≫ f)).zero = zA ≫ eqToHom hA_total.symm := by
    exact hA_zero'
  have hB_zero' :
      ((E.baseChange f).baseChange g).zero =
        zB ≫ eqToHom hB_zero_total_data.symm := by
    simpa [zB, zF, EllipticCurve.toData, EllipticCurveData.baseChange] using hB_zero
  have hB_zero_total_eq : hB_zero_total_data = hB_total := Subsingleton.elim _ _
  rw [hB_zero_total_eq] at hB_zero'
  let w : pullback E.projection (g ≫ f) ⟶ pullback E.projection f :=
    pullback.lift (pullback.fst E.projection (g ≫ f))
      (pullback.snd E.projection (g ≫ f) ≫ g)
      (by
        simpa only [Category.assoc] using
          (pullback.condition :
            pullback.fst E.projection (g ≫ f) ≫ E.projection =
              pullback.snd E.projection (g ≫ f) ≫ (g ≫ f)))
  let u : pullback E.projection (g ≫ f) ⟶
      pullback (pullback.snd E.projection f) g :=
    pullback.lift w (pullback.snd E.projection (g ≫ f))
      (by
        simpa only [w, Category.assoc] using
          (pullback.lift_snd (pullback.fst E.projection (g ≫ f))
            (pullback.snd E.projection (g ≫ f) ≫ g) _))
  let v : pullback (pullback.snd E.projection f) g ⟶
      pullback E.projection (g ≫ f) :=
    pullback.lift
      (pullback.fst (pullback.snd E.projection f) g ≫
        pullback.fst E.projection f)
      (pullback.snd (pullback.snd E.projection f) g)
      (by
        rw [Category.assoc, pullback.condition]
        simpa only [Category.assoc] using
          congrArg (fun q => q ≫ f)
            (pullback.condition (f := pullback.snd E.projection f) (g := g)))
  have huv : u ≫ v = 𝟙 _ := by
    apply pullback.hom_ext <;>
      simp [u, v, w, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc]
  have hvw : v ≫ w = pullback.fst (pullback.snd E.projection f) g := by
    apply pullback.hom_ext
    · simp [v, w, Category.assoc, pullback.lift_fst]
    · simpa [v, w, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc] using
        (pullback.condition (f := pullback.snd E.projection f) (g := g)).symm
  have hvu : v ≫ u = 𝟙 _ := by
    apply pullback.hom_ext <;>
      simp [u, v, w, hvw, Category.assoc, pullback.lift_fst, pullback.lift_snd]
  let j : pullback E.projection (g ≫ f) ≅
      pullback (pullback.snd E.projection f) g :=
    { hom := u
      inv := v
      hom_inv_id := huv
      inv_hom_id := hvu }
  have hj_snd :
      j.hom ≫ pullback.snd (pullback.snd E.projection f) g =
        pullback.snd E.projection (g ≫ f) := by
    dsimp [j, u]
    apply pullback.lift_snd
  have hzw : zA ≫ w = g ≫ zF := by
    apply pullback.hom_ext <;>
      simp [zA, w, zF, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc]
  have hz : zA ≫ j.hom = zB := by
    apply pullback.hom_ext
    · dsimp [j, u, zB]
      rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact hzw
    · dsimp [j, u, zB]
      rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact (pullback.lift_snd (g ≫ zF) (𝟙 T) _).symm
  have hB_total_cancel :
      (eqToIso hB_total).inv ≫ eqToHom hB_total = 𝟙 _ := by
    simpa only [eqToIso.hom] using (eqToIso hB_total).inv_hom_id
  have hB_total_cancel_snd :
      (eqToIso hB_total).inv ≫ eqToHom hB_total ≫
          pullback.snd (pullback.snd E.projection f) g =
        pullback.snd (pullback.snd E.projection f) g := by
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun q => q ≫ pullback.snd (pullback.snd E.projection f) g)
        hB_total_cancel
  have hA_total_cancel :
      eqToHom hA_total.symm ≫ (eqToIso hA_total).hom = 𝟙 _ := by
    simpa only [eqToIso.hom, eqToIso.inv] using (eqToIso hA_total).inv_hom_id
  have hA_total_cancel_tail :
      eqToHom hA_total.symm ≫ (eqToIso hA_total).hom ≫ j.hom ≫
          (eqToIso hB_total).inv = j.hom ≫ (eqToIso hB_total).inv := by
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun q => q ≫ j.hom ≫ (eqToIso hB_total).inv) hA_total_cancel
  let h : (E.baseChange (g ≫ f)).total ≅
      ((E.baseChange f).baseChange g).total :=
    eqToIso hA_total ≪≫ j ≪≫ (eqToIso hB_total).symm
  refine ⟨{
    hom := h
    projection_comm := by
      rw [hB_projection', hA_projection']
      simp only [h, Iso.trans_hom, Category.assoc, Iso.symm_hom]
      rw [hB_total_cancel_snd, hj_snd]
      simp only [eqToIso.hom]
    section_comm := by
      rw [hA_zero_zA, hB_zero']
      simp only [h, Iso.trans_hom, Category.assoc, Iso.symm_hom]
      rw [hA_total_cancel_tail]
      have hz_assoc :
          zA ≫ j.hom ≫ (eqToIso hB_total).inv =
            zB ≫ (eqToIso hB_total).inv := by
        simpa only [Category.assoc] using
          congrArg (fun q => q ≫ (eqToIso hB_total).inv) hz
      rw [hz_assoc]
      simp only [eqToIso.inv]
      rfl
  }⟩

/-- A chosen associativity witness for the pullback presentations. -/
noncomputable def EllipticCurveIso.baseChange_assoc {S X T : Scheme.{u}}
    (E : EllipticCurve S) (f : X ⟶ S) (g : T ⟶ X) :
    EllipticCurveIso (E.baseChange (g ≫ f))
      ((E.baseChange f).baseChange g) :=
  Classical.choice (exists_ellipticCurveIso_baseChange_assoc E f g)

/-- Chosen base changes along equal maps are identified. -/
theorem exists_ellipticCurveIso_baseChange_eq {S T : Scheme.{u}}
    (E : EllipticCurve S) {a b : T ⟶ S} (h : a = b) :
    Nonempty (EllipticCurveIso (E.baseChange a) (E.baseChange b)) := by
  subst h
  exact ⟨EllipticCurveIso.refl _⟩

noncomputable def EllipticCurveIso.baseChange_eq {S T : Scheme.{u}}
    (E : EllipticCurve S) {a b : T ⟶ S} (h : a = b) :
    EllipticCurveIso (E.baseChange a) (E.baseChange b) :=
  Classical.choice (exists_ellipticCurveIso_baseChange_eq E h)

/-- Composition of witnesses exists, as required by the source's 2-category discussion. -/
theorem exists_ellipticCurveMorphism_comp
    {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {a' : S' ⟶ S''}
    {E : EllipticCurve S} {E' : EllipticCurve S'} {E'' : EllipticCurve S''}
    (α : EllipticCurveMorphism a E E')
    (β : EllipticCurveMorphism a' E' E'') :
    Nonempty (EllipticCurveMorphism (a ≫ a') E E'') := by
  refine ⟨{
    hom := α.hom ≫ β.hom
    projection_comm := by
      calc
        (α.hom ≫ β.hom) ≫ E''.projection =
            α.hom ≫ (β.hom ≫ E''.projection) := Category.assoc _ _ _
        _ = α.hom ≫ (E'.projection ≫ a') := by rw [β.projection_comm]
        _ = (α.hom ≫ E'.projection) ≫ a' := (Category.assoc _ _ _).symm
        _ = (E.projection ≫ a) ≫ a' := by rw [α.projection_comm]
        _ = E.projection ≫ (a ≫ a') := Category.assoc _ _ _
    section_comm := by
      calc
        E.zero ≫ (α.hom ≫ β.hom) =
            (E.zero ≫ α.hom) ≫ β.hom := (Category.assoc _ _ _).symm
        _ = (a ≫ E'.zero) ≫ β.hom := by rw [α.section_comm]
        _ = a ≫ (E'.zero ≫ β.hom) := Category.assoc _ _ _
        _ = a ≫ (a' ≫ E''.zero) := by rw [β.section_comm]
        _ = (a ≫ a') ≫ E''.zero := (Category.assoc _ _ _).symm
    cartesian := α.cartesian.paste_horiz β.cartesian
  }⟩

/-- A chosen composite witness for the 2-categorical composition interface. -/
noncomputable def EllipticCurveMorphism.comp
    {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {a' : S' ⟶ S''}
    {E : EllipticCurve S} {E' : EllipticCurve S'} {E'' : EllipticCurve S''}
    (α : EllipticCurveMorphism a E E')
    (β : EllipticCurveMorphism a' E' E'') :
    EllipticCurveMorphism (a ≫ a') E E'' :=
  Classical.choice (exists_ellipticCurveMorphism_comp α β)

/-! ### The moduli projection -/

/-- The source's objects over `S`: elliptic curves over `S`. -/
abbrev ModuliPoint (S : Scheme.{u}) := EllipticCurve S

/-- The projection `p : M₁,₁ ⟶ Sch` sends a family to its base. -/
def moduliProjection {S : Scheme.{u}} (_E : ModuliPoint S) : Scheme.{u} := S

/-!
A rule out of the moduli object is represented by its value on every family,
together with the naturality equation forced by a witness.
-/
structure ModuliMorphismToScheme (T : Scheme.{u}) where
  map : ∀ {S : Scheme.{u}}, ModuliPoint S → (S ⟶ T)
  natural : ∀ {S S' : Scheme.{u}} {a : S ⟶ S'}
    {E : ModuliPoint S} {E' : ModuliPoint S'},
    EllipticCurveMorphism a E E' → map E = a ≫ map E'

end Formalization.Books.StacksIntroduction.Unit01
