import Formalization.Books.Sheaves.Unit11.Stalks
import Formalization.Books.Sheaves.Unit16.ExactnessAndPoints
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Sheaves on Spaces, Chapter 17, Section 1: Sheafification

The source span is `books/sheaves.tex:1458-1661`.  The pointwise product of
stalks and the local-germ condition are Mathlib's canonical
`presheafToTypes`/`LocalPredicate` construction.  In particular, the
sheafification below is `TopCat.Presheaf.sheafify`; this avoids introducing a
second implementation of the plus construction.
-/

namespace Formalization.Books.Sheaves.Unit17

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit07
open Formalization.Books.Sheaves.Unit11
open Formalization.Books.Sheaves.Unit16

universe v

noncomputable section

/-! ## The stalkwise product and the local-germ condition -/

/-- The presheaf `Π(F)` with sections `∏ x ∈ U, Fₓ`. -/
def stalkProductPresheaf {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) : TopCat.Presheaf (Type v) X :=
  TopCat.presheafToTypes X (fun x : X => F.stalk x)

@[simp]
theorem stalkProductPresheaf_obj {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (U : Opens X) :
    (stalkProductPresheaf F).obj (op U) =
      ∀ x : U, F.stalk x := rfl

/-- `Π(F)` is the sheaf of all dependent functions into the stalks. -/
theorem stalkProductPresheaf_isSheaf {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    TopCat.Presheaf.IsSheaf (stalkProductPresheaf F) := by
  exact TopCat.Presheaf.toTypes_isSheaf X (fun x : X => F.stalk x)

/-- The sheaf corresponding to the stalkwise product presheaf. -/
def stalkProductSheaf {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) : TopCat.Sheaf (Type v) X :=
  ⟨stalkProductPresheaf F, stalkProductPresheaf_isSheaf F⟩

/-- The source's condition `(*)`, expressed through Mathlib's local-germ API. -/
def sheafificationCondition {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) {U : Opens X}
    (s : ∀ x : U, F.stalk x) : Prop :=
  (TopCat.Presheaf.Sheafify.isLocallyGerm F).pred s

/-- Expanded form of the local-germ condition used in the source. -/
theorem sheafificationCondition_iff {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) {U : Opens X}
    (s : ∀ x : U, F.stalk x) :
    sheafificationCondition F s ↔
      ∀ x : U, ∃ (V : Opens X) (hxV : x.1 ∈ V) (i : V ⟶ U)
        (σ : F.obj (op V)),
        ∀ y : V, s (i y) = F.germ V y.1 y.2 σ := by
  sorry

/-! ## The canonical sheafification and its maps -/

/-- The canonical sheafification `F#` of a set-valued presheaf. -/
def sheafification {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) : TopCat.Sheaf (Type v) X :=
  F.sheafify

/-- The presheaf underlying the canonical sheafification. -/
abbrev sheafificationPresheaf {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) : TopCat.Presheaf (Type v) X :=
  (sheafification F).presheaf

@[simp]
theorem sheafificationPresheaf_obj {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (U : Opens X) :
    (sheafificationPresheaf F).obj (op U) =
      {s : ∀ x : U, F.stalk x // sheafificationCondition F s} := rfl

/-- The sheafification map `F → F#`. -/
abbrev sheafificationUnit {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    F ⟶ sheafificationPresheaf F :=
  F.toSheafify

/-- The inclusion `F# → Π(F)`. -/
def sheafificationProductMap {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    sheafificationPresheaf F ⟶ stalkProductPresheaf F :=
  TopCat.subpresheafToTypes.subtype
    (TopCat.Presheaf.Sheafify.isLocallyGerm F).toPrelocalPredicate

/-- The canonical map `F → Π(F)` obtained from the two maps in the source. -/
abbrev presheafToStalkProduct {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    F ⟶ stalkProductPresheaf F :=
  sheafificationUnit F ≫ sheafificationProductMap F

theorem sheafificationUnit_comp_productMap {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    sheafificationUnit F ≫ sheafificationProductMap F =
      presheafToStalkProduct F := rfl

/-- The component of `F → Π(F)` sends a section to all of its germs. -/
theorem presheafToStalkProduct_app_apply {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (U : Opens X)
    (s : F.obj (op U)) (x : U) :
    (presheafToStalkProduct F).app (op U) s x =
      F.germ U x.1 x.2 s := by
  sorry

/-- The construction `F ↦ (F → F# → Π(F))` is functorial in `F`. -/
theorem sheafification_maps_are_functorial {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) :
    ∃ ψ : sheafificationPresheaf F ⟶ sheafificationPresheaf G,
      sheafificationUnit F ≫ ψ = φ ≫ sheafificationUnit G := by
  sorry

/-! ## Sheaf property, stalks, and the universal property -/

/-- The canonical `F#` is a sheaf. -/
theorem sheafification_isSheaf {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    TopCat.Presheaf.IsSheaf (sheafificationPresheaf F) := by
  exact (sheafification F).property

/-- The canonical stalk comparison `F#ₓ ≅ Fₓ`. -/
noncomputable def sheafificationStalkIso {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (x : X) :
    (sheafificationPresheaf F).stalk x ≅ F.stalk x :=
  TopCat.Presheaf.sheafifyStalkIso F x

/-- The source's stalk equality, represented by the canonical inverse equivalence. -/
noncomputable def sheafificationStalkEquiv {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (x : X) :
    F.stalk x ≃ (sheafificationPresheaf F).stalk x :=
  (sheafificationStalkIso F x).toEquiv.symm

/-- The map `Fₓ → F#ₓ` induced by the sheafification unit is bijective. -/
theorem sheafificationUnit_stalk_bijective {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (x : X) :
    Function.Bijective
      ((TopCat.Presheaf.stalkFunctor (Type v) x).map (sheafificationUnit F)) := by
  sorry

/-- Every map from `F` to a sheaf factors through `F#`. -/
theorem existsUnique_sheafificationLift {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X)
    (φ : F ⟶ G.presheaf) :
    ∃! ψ : sheafificationPresheaf F ⟶ G.presheaf,
      sheafificationUnit F ≫ ψ = φ := by
  sorry

/-- The chosen factorization through `F#`. -/
noncomputable def sheafificationLift {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X)
    (φ : F ⟶ G.presheaf) :
    sheafificationPresheaf F ⟶ G.presheaf :=
  Classical.choose (existsUnique_sheafificationLift F G φ).exists

theorem sheafificationUnit_comp_lift {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X)
    (φ : F ⟶ G.presheaf) :
    sheafificationUnit F ≫ sheafificationLift F G φ = φ := by
  exact Classical.choose_spec (existsUnique_sheafificationLift F G φ).exists

/-- The chosen lift is the unique map with the required factorization property. -/
theorem sheafificationLift_unique {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X)
    (φ : F ⟶ G.presheaf) (ψ : sheafificationPresheaf F ⟶ G.presheaf)
    (hψ : sheafificationUnit F ≫ ψ = φ) :
    ψ = sheafificationLift F G φ := by
  exact (existsUnique_sheafificationLift F G φ).unique hψ
    (sheafificationUnit_comp_lift F G φ)

/-- The Hom-set bijection expressing the sheafification adjunction. -/
noncomputable def sheafificationHomEquiv {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X) :
    (sheafificationPresheaf F ⟶ G.presheaf) ≃ (F ⟶ G.presheaf) where
  toFun ψ := sheafificationUnit F ≫ ψ
  invFun φ := sheafificationLift F G φ
  left_inv ψ := by
    let φ := sheafificationUnit F ≫ ψ
    have h₁ : sheafificationUnit F ≫ ψ = φ := rfl
    have h₂ : sheafificationUnit F ≫ sheafificationLift F G φ = φ :=
      sheafificationUnit_comp_lift F G φ
    have huniq : ψ = sheafificationLift F G φ :=
      (existsUnique_sheafificationLift F G φ).unique h₁ h₂
    exact huniq.symm
  right_inv φ := sheafificationUnit_comp_lift F G φ

/-- The adjunction in the source's direction, from presheaf maps to sheaf maps. -/
noncomputable def sheafificationAdjunctionHomEquiv {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X) :
    (F ⟶ G.presheaf) ≃ (sheafificationPresheaf F ⟶ G.presheaf) :=
  (sheafificationHomEquiv F G).symm

/-! ## The constant-presheaf example -/

noncomputable def constantPresheafSheafificationMap {X : TopCat.{v}} (A : Type v) :
    sheafificationPresheaf (constantPresheaf (X := X) A) ⟶
      (constantSheaf X A).presheaf :=
  sheafificationLift (constantPresheaf (X := X) A) (constantSheaf X A)
    (constantPresheafToConstantSheaf A)

/-- The sheafification of the constant presheaf is the constant sheaf. -/
theorem constantPresheafSheafificationMap_isIso {X : TopCat.{v}} (A : Type v) :
    IsIso (constantPresheafSheafificationMap (X := X) A) := by
  sorry

/-- A canonical isomorphism in the constant-presheaf example. -/
noncomputable def constantPresheafSheafificationIso {X : TopCat.{v}} (A : Type v) :
    sheafificationPresheaf (constantPresheaf (X := X) A) ≅
      (constantSheaf X A).presheaf := by
  letI := constantPresheafSheafificationMap_isIso (X := X) A
  exact asIso (constantPresheafSheafificationMap (X := X) A)

/-! ## Separatedness and injectivity/surjectivity -/

/-- A presheaf is separated exactly when its map to `F#` is sectionwise injective. -/
theorem separatedPresheaf_iff_sheafificationUnit_injective
    {X : TopCat.{v}} (F : TopCat.Presheaf (Type v) X) :
    SeparatedPresheaf F ↔
      PresheafInjective (sheafificationUnit F) := by
  sorry

/-- The induced map on sheafifications of a presheaf morphism. -/
noncomputable def sheafificationMap {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) :
    sheafificationPresheaf F ⟶ sheafificationPresheaf G :=
  sheafificationLift F (sheafification G) (φ ≫ sheafificationUnit G)

theorem sheafificationUnit_comp_map {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) :
    sheafificationUnit F ≫ sheafificationMap φ =
      φ ≫ sheafificationUnit G := by
  exact sheafificationUnit_comp_lift F (sheafification G)
    (φ ≫ sheafificationUnit G)

theorem sheafificationMap_id {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    sheafificationMap (𝟙 F) = 𝟙 _ := by
  sorry

theorem sheafificationMap_comp {X : TopCat.{v}}
    {F G H : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) (ψ : G ⟶ H) :
    sheafificationMap (φ ≫ ψ) = sheafificationMap φ ≫ sheafificationMap ψ := by
  sorry

/-- Sectionwise injectivity is preserved by sheafification. -/
theorem sheafificationMap_preserves_injective {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G)
    (hφ : PresheafInjective φ) :
    PresheafInjective (sheafificationMap φ) := by
  sorry

/-- Sectionwise surjectivity is preserved by sheafification. -/
theorem sheafificationMap_preserves_surjective {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G)
    (hφ : PresheafSurjective φ) :
    PresheafSurjective (sheafificationMap φ) := by
  sorry

end

end Formalization.Books.Sheaves.Unit17
