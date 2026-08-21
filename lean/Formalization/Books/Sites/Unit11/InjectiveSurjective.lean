import Formalization.Books.Sites.Unit07.Sheaves
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Sites and Sheaves, Chapter 11: Injective and surjective maps of sheaves

The source section defines pointwise injective and locally surjective maps of
sheaves of sets, identifies them with categorical monomorphisms and
epimorphisms, and describes a locally surjective map by its kernel-pair
coequalizer.  Mathlib's `Presheaf.IsLocallySurjective` is the canonical
covering-sieve formulation of the source's local image condition.
-/

namespace Formalization.Books.Sites.Unit11

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presieve
open Formalization.Books.Sites.Unit06
open Opposite

universe u v w

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-! ## Injective and surjective maps -/

/-- A map of sheaves of sets is injective when it is injective on sections over
every object of the site. -/
def SheafInjective (J : Site C)
    {F G : Sheaf J.toGrothendieck (Type w)} (φ : F ⟶ G) : Prop :=
  ∀ U : C, Function.Injective (φ.hom.app (op U))

/-
The source's local-surjectivity condition is Mathlib's canonical
`Presheaf.IsLocallySurjective`: for every target section, the sieve of arrows
where it has a preimage is covering.  This is the sieve form of the source's
covering-family definition and avoids introducing a parallel notion.
-/
abbrev SheafSurjective (J : Site C)
    {F G : Sheaf J.toGrothendieck (Type w)} (φ : F ⟶ G) : Prop :=
  Presheaf.IsLocallySurjective J.toGrothendieck φ.hom

/-- The source's covering-family formulation is the image-sieve formulation
provided by Mathlib. -/
theorem sheaf_surjective_iff_imageSieve_covering (J : Site C)
    {F G : Sheaf J.toGrothendieck (Type w)} (φ : F ⟶ G) :
    SheafSurjective J φ ↔
      ∀ (U : C) (s : G.obj.obj (op U)),
        Presheaf.imageSieve φ.hom s ∈ J.toGrothendieck U := by
  constructor
  · intro h U s
    exact h.imageSieve_mem s
  · intro h
    exact ⟨fun {U} s => h U s⟩

/-! ## Categorical characterizations -/

/-- The source's injective maps of sheaves are exactly the monomorphisms. -/
theorem sheaf_injective_iff_mono (J : Site C)
    {F G : Sheaf J.toGrothendieck (Type w)} (φ : F ⟶ G) :
    SheafInjective J φ ↔ Mono φ := by
  sorry

/-- The source's surjective maps of sheaves are exactly the epimorphisms. -/
theorem sheaf_surjective_iff_epi (J : Site C)
    {F G : Sheaf J.toGrothendieck (Type w)} (φ : F ⟶ G) :
    SheafSurjective J φ ↔ Epi φ := by
  sorry

/-- A map of sheaves is an isomorphism exactly when it is injective and
surjective in the source's sense. -/
theorem sheaf_isIso_iff_injective_and_surjective (J : Site C)
    {F G : Sheaf J.toGrothendieck (Type w)} (φ : F ⟶ G) :
    IsIso φ ↔ SheafInjective J φ ∧ SheafSurjective J φ := by
  sorry

/-! ## The coequalizer of a surjection -/

/-- The kernel-pair cofork of a map of sheaves.  Its parallel arrows are the
two projections from the pullback `F ×_G F`, and its cofork projection is the
given map to `G`. -/
noncomputable def surjectionCoequalizerCofork (J : Site C)
    {F G : Sheaf J.toGrothendieck (Type w)} (φ : F ⟶ G) :
    Cofork (pullback.fst φ φ) (pullback.snd φ φ) :=
  Cofork.ofπ φ (pullback.condition (f := φ) (g := φ))

/-- A locally surjective map of sheaves presents its target as the
coequalizer of its kernel pair. -/
noncomputable def coequalizer_surjection (J : Site C)
    {F G : Sheaf J.toGrothendieck (Type w)} (φ : F ⟶ G)
    (hφ : SheafSurjective J φ) :
    IsColimit (surjectionCoequalizerCofork J φ) := by
  sorry

end Formalization.Books.Sites.Unit11
