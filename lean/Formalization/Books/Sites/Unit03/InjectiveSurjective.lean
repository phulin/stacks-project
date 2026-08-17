import Formalization.Books.Sites.Unit02.Presheaves
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Sites and Sheaves, Chapter 3: Injective and surjective maps of presheaves

The source span is `books/sites.tex`, lines 138--294.  Pointwise
injectivity and surjectivity are expressed for natural transformations of
set-valued presheaves.  Subpresheaves and their image factorization reuse
Mathlib's canonical `CategoryTheory.Subfunctor` and `Subfunctor.range`
interfaces.

The source's pushout argument is retained through the canonical pushouts in
`Type` and in the presheaf functor category.  Evaluation of the latter is
canonically isomorphic, rather than definitionally equal, to the objectwise
pushout; the two bridge equations below record the source's component maps.
-/

namespace Formalization.Books.Sites.Unit03

open CategoryTheory CategoryTheory.Limits Opposite
open Formalization.Books.Sites.Unit02

universe v u

/-! ## Pointwise injectivity and surjectivity -/

/-- A morphism of presheaves is injective when every section map is injective. -/
def PresheafInjective {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) : Prop :=
  ∀ U : C, Function.Injective (φ.app (op U))

/-- A morphism of presheaves is surjective when every section map is surjective. -/
def PresheafSurjective {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) : Prop :=
  ∀ U : C, Function.Surjective (φ.app (op U))

/- The pointwise type-category criteria are exactly the source's two
   categorical characterizations. -/

theorem presheaf_injective_iff_mono {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) :
    PresheafInjective φ ↔ Mono φ := by
  constructor
  · intro h
    apply (NatTrans.mono_iff_mono_app φ).2
    intro X
    rw [mono_iff_injective]
    simpa using h X.unop
  · intro h U
    exact (mono_iff_injective _).1
      ((NatTrans.mono_iff_mono_app φ).1 h (op U))

theorem presheaf_surjective_iff_epi {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) :
    PresheafSurjective φ ↔ Epi φ := by
  constructor
  · intro h
    apply (NatTrans.epi_iff_epi_app φ).2
    intro X
    rw [epi_iff_surjective]
    simpa using h X.unop
  · intro h U
    exact (epi_iff_surjective _).1
      ((NatTrans.epi_iff_epi_app φ).1 h (op U))

theorem presheaf_isIso_iff_injective_and_surjective
    {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) :
    IsIso φ ↔ PresheafInjective φ ∧ PresheafSurjective φ := by
  constructor
  · intro h
    let _ : IsIso φ := h
    exact ⟨(presheaf_injective_iff_mono φ).2 inferInstance,
      (presheaf_surjective_iff_epi φ).2 inferInstance⟩
  · rintro ⟨hinj, hsurj⟩
    apply (NatTrans.isIso_iff_isIso_app φ).2
    intro X
    rw [isIso_iff_bijective]
    simpa using ⟨hinj X.unop, hsurj X.unop⟩

/-! ## The pushout maps used in the epimorphism argument -/

/-- The left map into the chosen pushout of two maps of types. -/
noncomputable def setPushoutInl {A B D : Type v}
    (f : A ⟶ B) (g : A ⟶ D) : B ⟶ pushout f g :=
  pushout.inl f g

/- The source's `inr_{f,g}` is the other canonical map into the same
   set-theoretic pushout. -/
/-- The right map into the chosen pushout of two maps of types. -/
noncomputable def setPushoutInr {A B D : Type v}
    (f : A ⟶ B) (g : A ⟶ D) : D ⟶ pushout f g :=
  pushout.inr f g

/-- The two maps into a pushout identify the two images of its span. -/
theorem setPushout_condition {A B D : Type v}
    (f : A ⟶ B) (g : A ⟶ D) :
    f ≫ setPushoutInl f g = g ≫ setPushoutInr f g := by
  simpa [setPushoutInl, setPushoutInr] using
    (pushout.condition (f := f) (g := g))

/- The elementary set statement used by the source's proof of the epi
   characterization. -/
theorem setPushout_inl_eq_inr_iff_surjective {A B : Type v} (f : A ⟶ B) :
    setPushoutInl f f = setPushoutInr f f ↔ Function.Surjective f := by
  sorry

/-! ## The presheaf pushout -/

/-- The pushout presheaf of two morphisms with common source. -/
noncomputable def presheafPushout {C : Type u} [Category.{v} C]
    {F G H : Presheaf C} (f : F ⟶ G) (g : F ⟶ H) : Presheaf C :=
  pushout f g

/- The two natural transformations called `i_1` and `i_2` in the source. -/
/-- The left inclusion into a presheaf pushout. -/
noncomputable def presheafPushoutInl {C : Type u} [Category.{v} C]
    {F G H : Presheaf C} (f : F ⟶ G) (g : F ⟶ H) :
    G ⟶ presheafPushout f g :=
  pushout.inl f g

/- The right inclusion into a presheaf pushout. -/
/-- The right inclusion into a presheaf pushout. -/
noncomputable def presheafPushoutInr {C : Type u} [Category.{v} C]
    {F G H : Presheaf C} (f : F ⟶ G) (g : F ⟶ H) :
    H ⟶ presheafPushout f g :=
  pushout.inr f g

/-- The defining equality of the two maps from the common presheaf source. -/
theorem presheafPushout_condition {C : Type u} [Category.{v} C]
    {F G H : Presheaf C} (f : F ⟶ G) (g : F ⟶ H) :
    f ≫ presheafPushoutInl f g = g ≫ presheafPushoutInr f g := by
  simpa [presheafPushout, presheafPushoutInl, presheafPushoutInr] using
    (pushout.condition (f := f) (g := g))

/- The source describes the components of `i_1` and `i_2` as the set
   pushout inclusions.  Mathlib's evaluated pushout comes with the canonical
   comparison isomorphism recorded here. -/

theorem presheafPushout_inl_app_comp_objIso_hom
    {C : Type u} [Category.{v} C]
    {F G H : Presheaf C} (f : F ⟶ G) (g : F ⟶ H) (U : C) :
    (presheafPushoutInl f g).app (op U) ≫
        (pushoutObjIso f g (op U)).hom =
      setPushoutInl (f.app (op U)) (g.app (op U)) := by
  change (pushout.inl f g).app (op U) ≫
      (pushoutObjIso f g (op U)).hom =
    pushout.inl (f.app (op U)) (g.app (op U))
  exact inl_comp_pushoutObjIso_hom f g (op U)

theorem presheafPushout_inr_app_comp_objIso_hom
    {C : Type u} [Category.{v} C]
    {F G H : Presheaf C} (f : F ⟶ G) (g : F ⟶ H) (U : C) :
    (presheafPushoutInr f g).app (op U) ≫
        (pushoutObjIso f g (op U)).hom =
      setPushoutInr (f.app (op U)) (g.app (op U)) := by
  change (pushout.inr f g).app (op U) ≫
      (pushoutObjIso f g (op U)).hom =
    pushout.inr (f.app (op U)) (g.app (op U))
  exact inr_comp_pushoutObjIso_hom f g (op U)

/-- An epimorphism identifies the two inclusions into its self-pushout. -/
theorem presheafPushout_inl_eq_inr_of_epi
    {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) [Epi φ] :
    presheafPushoutInl φ φ = presheafPushoutInr φ φ := by
  apply (cancel_epi φ).1
  exact presheafPushout_condition φ φ

/- The objectwise consequence used immediately afterward in the source is
   stated explicitly, using the evaluated-pushout comparison isomorphism. -/
theorem setPushout_inl_eq_inr_of_presheaf_epi
    {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) [Epi φ] (U : C) :
    setPushoutInl (φ.app (op U)) (φ.app (op U)) =
      setPushoutInr (φ.app (op U)) (φ.app (op U)) := by
  rw [← presheafPushout_inl_app_comp_objIso_hom φ φ U,
    ← presheafPushout_inr_app_comp_objIso_hom φ φ U]
  exact congrArg (fun k => k ≫ (pushoutObjIso φ φ (op U)).hom)
    (congr_app (presheafPushout_inl_eq_inr_of_epi φ) (op U))

/-! ## Subpresheaves and image factorization -/

/- `Subfunctor` is Mathlib's objectwise-subset, restriction-compatible
   implementation of a subpresheaf. -/
/-- A subpresheaf of `G`, represented by Mathlib's canonical subfunctor. -/
abbrev Subpresheaf {C : Type u} [Category.{v} C] (G : Presheaf C) :=
  Subfunctor G

/- The structure fields `obj` and `map` are respectively the objectwise
   subset and its stability under every presheaf restriction map. -/

theorem subpresheaf_restriction_closed
    {C : Type u} [Category.{v} C] {G : Presheaf C}
    (S : Subpresheaf G) {U V : C} (f : V ⟶ U)
    (s : S.toFunctor.obj (op U)) :
    G.map f.op s.1 ∈ S.obj (op V) := by
  exact S.map f.op s.2

/- The canonical inclusion is the source's family of objectwise inclusion
   maps glued into one natural transformation. -/
/-- The natural inclusion of a subpresheaf into its ambient presheaf. -/
abbrev subpresheafInclusion
    {C : Type u} [Category.{v} C] {G : Presheaf C}
    (S : Subpresheaf G) : S.toFunctor ⟶ G :=
  S.ι

theorem subpresheaf_inclusion_mono
    {C : Type u} [Category.{v} C] {G : Presheaf C}
    (S : Subpresheaf G) : Mono (subpresheafInclusion S) := by
  infer_instance

@[simp]
theorem subpresheaf_inclusion_app
    {C : Type u} [Category.{v} C] {G : Presheaf C}
    (S : Subpresheaf G) (U : C) (s : S.toFunctor.obj (op U)) :
    (subpresheafInclusion S).app (op U) s = s.1 := rfl

/- The image subpresheaf is the canonical range subfunctor. -/
/-- The image subpresheaf of a morphism of presheaves. -/
abbrev presheafImage {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) : Subpresheaf G :=
  Subfunctor.range φ

@[simp]
theorem presheafImage_obj {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) (U : C) :
    (presheafImage φ).obj (op U) = Set.range (φ.app (op U)) := rfl

/-- The canonical map from a presheaf to the subpresheaf which is its image. -/
abbrev presheafImageFactor {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) :
    F ⟶ (presheafImage φ).toFunctor :=
  Subfunctor.toRange φ

/-- The inclusion of the image subpresheaf into the target presheaf. -/
abbrev presheafImageInclusion {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) :
    (presheafImage φ).toFunctor ⟶ G :=
  (presheafImage φ).ι

@[reassoc (attr := simp)]
theorem presheafImage_factorization {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) :
    presheafImageFactor φ ≫ presheafImageInclusion φ = φ := by
  exact Subfunctor.toRange_ι φ

theorem presheafImageFactor_surjective {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) :
    PresheafSurjective (presheafImageFactor φ) := by
  exact (presheaf_surjective_iff_epi (presheafImageFactor φ)).2 inferInstance

/- The source's existence-and-uniqueness assertion is stated with the
   canonical inclusion as its second map and pointwise surjectivity as its
   first-map condition. -/
theorem exists_unique_presheafImage {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) :
    ∃! G' : Subpresheaf G,
      ∃ q : F ⟶ G'.toFunctor,
        q ≫ G'.ι = φ ∧ PresheafSurjective q := by
  sorry

/- The final source definition is a proposition naming the canonical range
   subpresheaf as the image. -/
/-- `G'` is the image of `φ` when it is the canonical range subpresheaf. -/
def IsPresheafImage {C : Type u} [Category.{v} C]
    {F G : Presheaf C} (φ : F ⟶ G) (G' : Subpresheaf G) : Prop :=
  G' = presheafImage φ

end Formalization.Books.Sites.Unit03
