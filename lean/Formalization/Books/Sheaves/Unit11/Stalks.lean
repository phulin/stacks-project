import Formalization.Books.Sheaves.Unit07.Sheaves
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Order.Filter.Germ.Basic

/-!
# Sheaves on Spaces, Chapter 11: Stalks

The source span `books/sheaves.tex:893-1049` is the section `Stalks`.  The
stalk, germ, and stalk-functor constructions are Mathlib's canonical filtered
colimit constructions.  This file adds the source-facing maps and statements
that are specific to the section, reusing the set-valued sheaves and
pointwise-product sheaves from Chapter 7.

The source's quotient notation for a stalk is recorded by
`germ_eq_iff_common_restriction`; it is not implemented as a second quotient
type.  The smooth-function example uses Mathlib's canonical smooth sheaf,
whose sections are the expected `C^∞` maps on open subsets of Euclidean space.
-/

namespace Formalization.Books.Sheaves.Unit11

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit07
open scoped ContDiff Manifold

universe w v

/-! ## Stalks, germs, and the stalk functor -/

/-- The stalk of a set-valued presheaf, using Mathlib's filtered colimit. -/
abbrev Stalk {X : TopCat.{w}} (F : TopCat.Presheaf (Type w) X) (x : X) : Type w :=
  TopCat.Presheaf.stalk F x

/-- The stalk functor at a point, using the canonical presheaf functor. -/
noncomputable abbrev StalkFunctor {X : TopCat.{w}} (x : X) :
    TopCat.Presheaf (Type w) X ⥤ Type w :=
  TopCat.Presheaf.stalkFunctor (Type w) x

/-- The map on stalks induced by a morphism of presheaves. -/
noncomputable abbrev StalkMap {X : TopCat.{w}} {F G : TopCat.Presheaf (Type w) X}
    (φ : F ⟶ G) (x : X) : Stalk F x ⟶ Stalk G x :=
  (StalkFunctor x).map φ

/-!
`TopCat.Presheaf.stalk` is definitionally the colimit over the opposite of
`OpenNhds x`; this supplies the reverse-inclusion indexing used in the source,
and `TopCat.Presheaf.germ` is the canonical colimit coprojection.  Thus no
parallel colimit or quotient implementation is introduced here.
-/

/-- Apply the canonical germ morphism to a section. -/
noncomputable abbrev germApply {X : TopCat.{w}} {F : TopCat.Presheaf (Type w) X}
    (U : Opens X) (x : X) (hx : x ∈ U) (s : Sections F U) : Stalk F x :=
  ConcreteCategory.hom (F.germ U x hx) s

/-- The source's explicit quotient criterion for equality of germs. -/
theorem germ_eq_iff_common_restriction
    {X : TopCat.{w}} {F : TopCat.Presheaf (Type w) X}
    {U V : Opens X} (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : Sections F U) (t : Sections F V) :
    germApply (F := F) U x hxU s = germApply (F := F) V x hxV t ↔
      ∃ (W : Opens X) (hxW : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ V),
        F.map (homOfLE hWU).op s = F.map (homOfLE hWV).op t := by
  sorry

/-- The canonical map from sections on `U` to the product of their stalks. -/
noncomputable def sectionToStalks {X : TopCat.{w}} {F : TopCat.Presheaf (Type w) X} (U : Opens X) :
    Sections F U → ∀ x : U, Stalk F x.1 :=
  fun s x => germApply (F := F) U x.1 x.2 s

/-- The source's injectivity lemma for a sheaf. -/
theorem sectionToStalks_injective_of_isSheaf
    {X : TopCat.{w}} {F : TopCat.Presheaf (Type w) X} (hF : SetSheaf F)
    (U : Opens X) :
    Function.Injective (sectionToStalks (F := F) U) := by
  sorry

/-- A presheaf is separated when sections are determined by all their germs. -/
def SeparatedPresheaf {X : TopCat.{w}} (F : TopCat.Presheaf (Type w) X) : Prop :=
  ∀ U : Opens X, Function.Injective (sectionToStalks (F := F) U)

/-- Every sheaf of sets is separated in the stalk sense. -/
theorem separatedPresheaf_of_isSheaf
    {X : TopCat.{w}} {F : TopCat.Presheaf (Type w) X} (hF : SetSheaf F) :
    SeparatedPresheaf F := by
  intro U
  exact sectionToStalks_injective_of_isSheaf hF U

/-- Stalk functoriality on the germ of a section. -/
theorem stalkMap_germ
    {X : TopCat.{w}} {F G : TopCat.Presheaf (Type w) X} (φ : F ⟶ G)
    {U : Opens X} (x : X) (hx : x ∈ U) (s : Sections F U) :
    StalkMap φ x (germApply (F := F) U x hx s) =
      germApply (F := G) U x hx (φ.app (op U) s) := by
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ s

/-! ## The constant-presheaf example -/

/-- The canonical map from the constant presheaf to the constant sheaf. -/
noncomputable def constantPresheafToConstantSheaf
    {X : TopCat.{w}} (A : Type w) :
    constantPresheaf (X := X) A ⟶
      (constantSheaf X A).presheaf where
  app U := letI : TopologicalSpace A := ⊥
    TypeCat.ofHom (show A → ((Opens.toTopCat X).obj U.unop ⟶ TopCat.discrete.obj A) from
      fun a => TopCat.ofHom (ContinuousMap.const ((Opens.toTopCat X).obj U.unop) a))
  naturality := by
    intro U V i
    apply ConcreteCategory.hom_ext _ _
    intro a
    apply TopCat.hom_ext
    rfl

/-- The canonical map from `A` into the stalk of the constant presheaf. -/
noncomputable def constantPresheafStalkMap {X : TopCat.{w}} (A : Type w) (x : X) :
    A → Stalk (constantPresheaf (X := X) A) x :=
  fun a =>
    germApply (F := constantPresheaf (X := X) A) (⊤ : Opens X) x (by simp) a

/-- The constant presheaf has stalk `A`. -/
theorem constantPresheafStalkMap_bijective
    {X : TopCat.{w}} (A : Type w) (x : X) :
    Function.Bijective (constantPresheafStalkMap A x) := by
  sorry

/-- A canonical equivalence between `A` and the stalk of the constant presheaf. -/
noncomputable def constantPresheafStalkEquiv
    {X : TopCat.{w}} (A : Type w) (x : X) :
    A ≃ Stalk (constantPresheaf (X := X) A) x :=
  Equiv.ofBijective (constantPresheafStalkMap A x)
    (constantPresheafStalkMap_bijective A x)

/-- The map on stalks induced by the constant-presheaf-to-constant-sheaf map. -/
noncomputable def constantSheafStalkMap {X : TopCat.{w}} (A : Type w) (x : X) :
    Stalk (constantPresheaf (X := X) A) x →
      Stalk (constantSheaf X A).presheaf x :=
  StalkMap (constantPresheafToConstantSheaf A) x

/-- The constant sheaf has stalk `A`. -/
theorem constantSheafStalkMap_bijective
    {X : TopCat.{w}} (A : Type w) (x : X) :
    Function.Bijective (constantSheafStalkMap A x) := by
  sorry

/-- The canonical bijection `A ≅ (A_p)_x ≅ \underline A_x`. -/
noncomputable def constantSheafStalkEquiv
    {X : TopCat.{w}} (A : Type w) (x : X) :
    A ≃ Stalk (constantSheaf X A).presheaf x :=
  (constantPresheafStalkEquiv A x).trans
    (Equiv.ofBijective (constantSheafStalkMap A x)
      (constantSheafStalkMap_bijective A x))

/-! ## Smooth functions and their germs -/

/-- The sheaf of smooth real-valued functions on `ℝ^n`, in Mathlib's
coordinate model `Fin n → ℝ`. -/
noncomputable abbrev smoothFunctionsSheaf (n : ℕ) :
    TopCat.Sheaf (Type) (TopCat.of (Fin n → ℝ)) :=
  smoothSheaf (𝓘(ℝ, Fin n → ℝ)) 𝓘(ℝ) (Fin n → ℝ) ℝ

/-- The presheaf underlying the smooth-function sheaf. -/
noncomputable abbrev smoothFunctionsPresheaf (n : ℕ) :=
  (smoothFunctionsSheaf n).presheaf

/-- Its sections over an open are the expected `C^∞` functions. -/
@[simp]
theorem smoothFunctionsPresheaf_obj (n : ℕ)
    (U : Opens (TopCat.of (Fin n → ℝ))) :
    (smoothFunctionsPresheaf n).obj (op U) =
      C^∞⟮𝓘(ℝ, Fin n → ℝ), U; 𝓘(ℝ), ℝ⟯ := by
  rfl

/-- Every space of smooth sections is a real vector space. -/
noncomputable instance smoothFunctionsSections_module (n : ℕ)
    (U : Opens (TopCat.of (Fin n → ℝ))) :
    Module ℝ ((smoothFunctionsPresheaf n).obj (op U)) := by
  change Module ℝ C^∞⟮𝓘(ℝ, Fin n → ℝ), U; 𝓘(ℝ), ℝ⟯
  infer_instance

/-- Evaluation of a smooth germ at its base point. -/
noncomputable abbrev smoothFunctionsStalkEvaluation (n : ℕ)
    (x : Fin n → ℝ) :
    Stalk (smoothFunctionsPresheaf n) x → ℝ :=
  smoothSheaf.eval (𝓘(ℝ, Fin n → ℝ)) 𝓘(ℝ) ℝ x

@[simp]
theorem smoothFunctionsStalkEvaluation_germ (n : ℕ)
    (U : Opens (TopCat.of (Fin n → ℝ))) (x : Fin n → ℝ) (hx : x ∈ U)
    (f : (smoothFunctionsPresheaf n).obj (op U)) :
    smoothFunctionsStalkEvaluation n x
        (germApply (F := smoothFunctionsPresheaf n) U x hx f) = f.1 ⟨x, hx⟩ := by
  exact smoothSheaf.eval_germ U x hx f

/-! ## Pointwise products and the stalk warning -/

/-!
The pointwise-product presheaf and its sheaf property are already provided by
`Unit07.pointwiseProductPresheaf` and
`Unit07.pointwiseProductPresheaf_isSheaf`.  The following cocone is the
canonical evaluation cocone at a point; its colimit descent is the map
`F_x → A_x` mentioned in the source.
-/

/-- The evaluation cocone for the pointwise-product presheaf at `x`. -/
noncomputable def pointwiseProductEvaluationCocone
    {X : TopCat.{v}} (A : X → Type v) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ pointwiseProductPresheaf A) where
  pt := A x
  ι := { app := fun U => ↾fun s => s ⟨x, (unop U).2⟩
         naturality := by
           intro U V i
           ext s
           rfl }

/-- The canonical map from the pointwise-product stalk to its fiber at `x`. -/
noncomputable def pointwiseProductStalkEvaluation
    {X : TopCat.{v}} (A : X → Type v) (x : X) :
    Stalk (pointwiseProductPresheaf A) x → A x :=
  colimit.desc _ (pointwiseProductEvaluationCocone A x)

@[simp]
theorem pointwiseProductStalkEvaluation_germ
    {X : TopCat.{v}} (A : X → Type v) (U : Opens X) (x : X) (hx : x ∈ U)
    (s : (pointwiseProductPresheaf A).obj (op U)) :
    pointwiseProductStalkEvaluation A x
        (germApply (F := pointwiseProductPresheaf A) U x hx s) = s ⟨x, hx⟩ := by
  sorry

/-- The type of tails of binary sequences, i.e. binary sequences modulo
eventual equality. -/
abbrev BinarySequenceTail :=
  Filter.Germ (Filter.cofinite : Filter ℕ) Bool

/-- There are infinitely many binary sequence tails. -/
theorem binarySequenceTail_infinite : Infinite BinarySequenceTail := by
  sorry

/-- A convergent sequence of distinct points produces all binary sequence
tails in the corresponding pointwise-product stalk. -/
theorem pointwiseProductStalk_surjects_binarySequenceTails
    {X : TopCat.{v}} (x : X) (xSeq : ℕ → X)
    (hlim : Filter.Tendsto xSeq atTop (𝓝 x))
    (hinj : Function.Injective xSeq) :
    ∃ q : TopCat.Presheaf.stalk
        (pointwiseProductPresheaf (fun _ : X => Bool)) x →
        BinarySequenceTail,
      Function.Surjective q := by
  sorry

/-- Under the preceding hypotheses, the pointwise-product stalk is not the
fiber `Bool` at the limit point. -/
theorem pointwiseProductStalk_not_equiv_bool_of_limit_sequence
    {X : TopCat.{v}} (x : X) (xSeq : ℕ → X)
    (hlim : Filter.Tendsto xSeq atTop (𝓝 x))
    (hinj : Function.Injective xSeq) :
    ¬ Nonempty (TopCat.Presheaf.stalk
      (pointwiseProductPresheaf (fun _ : X => Bool)) x ≃ Bool) := by
  sorry

/-- If every neighborhood of `x` contains an empty fiber, the pointwise-
product stalk at `x` is empty. -/
theorem pointwiseProductStalk_isEmpty_of_empty_fiber_near
    {X : TopCat.{v}} (A : X → Type v) (x : X)
    (hEmpty : ∀ U : Opens X, x ∈ U →
      ∃ y : X, y ∈ U ∧ IsEmpty (A y)) :
    IsEmpty (TopCat.Presheaf.stalk (pointwiseProductPresheaf A) x) := by
  sorry

end Formalization.Books.Sheaves.Unit11
