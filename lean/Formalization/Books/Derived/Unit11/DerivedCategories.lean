import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Formalization.Books.Derived.Unit06.Quotients
import Formalization.Books.Derived.Unit09.ConesAndTermwiseSplitSequences
import Formalization.Books.Homology.Unit13.Complexes

/-!
# Derived Categories, Chapter 11: derived categories

The source's derived category is Mathlib's `DerivedCategory`.  The
homotopy-category acyclic objects, quasi-isomorphisms, canonical cohomology
functors, bounded t-structure pieces, and bounded-below localization are
therefore exposed through the existing Mathlib interfaces.  The bounded-above
and bounded localization statements are retained as theorem interfaces until
their proofs are formalized.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit05
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit09
open Formalization.Books.Categories.Unit27
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Derived.Unit11

/- The earlier chapter's complex aliases use its bundled additive-category
   interface.  An abelian category already supplies precisely those fields. -/
noncomputable instance abelian_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    Formalization.Books.Homology.Unit03.AdditiveCategory C :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

/-! ## The homological cohomology functor on the homotopy category -/

abbrev BookComplex (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  Formalization.Books.Derived.Unit08.Comp C

abbrev BookHomotopyCategory (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  Formalization.Books.Derived.Unit08.K C

noncomputable instance bookHomotopyCategory_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (BookHomotopyCategory C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

/-- The source's `Hⁿ : K(𝒜) ⥤ 𝒜`, using Mathlib's cochain homology functor. -/
abbrev cohomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    BookHomotopyCategory C ⥤ C :=
  HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n

/-- The source's reindexing convention `Hⁿ = H⁰ ∘ [n]`. -/
theorem cohomologyFunctor_shift
  (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    (cohomologyFunctor C 0).shift n = cohomologyFunctor C n :=
  rfl

/-- The degree-zero cohomology functor on `K(𝒜)` is homological. -/
theorem cohomologyZero_homological
    (C : Type u) [Category.{v} C] [Abelian C] :
    (cohomologyFunctor C 0).IsHomological := by
  infer_instance

/-- A finite exact window of the long cohomology sequence of a triangle. -/
noncomputable def cohomologyLongExactWindow
    (C : Type u) [Category.{v} C] [Abelian C]
    (T : Triangle (BookHomotopyCategory C)) (n : ℤ) :
    ComposableArrows C 5 :=
  (cohomologyFunctor C 0).homologySequenceComposableArrows₅ T n (n + 1) rfl

/-- Every cohomology window of a distinguished triangle is exact. -/
theorem cohomologyLongExactWindow_exact
    (C : Type u) [Category.{v} C] [Abelian C]
    (T : Triangle (BookHomotopyCategory C))
    (hT : T ∈ distTriang (BookHomotopyCategory C)) (n : ℤ) :
    (cohomologyLongExactWindow C T n).Exact :=
  (cohomologyFunctor C 0).homologySequenceComposableArrows₅_exact T hT n (n + 1) rfl

/-! ### The snake-lemma sequence and its termwise-split comparison -/

/-- The cochain long-exact window attached to a short exact sequence. -/
noncomputable def cochainCohomologyWindow
    (C : Type u) [Category.{v} C] [Abelian C]
    {S : ShortComplex (BookComplex C)} (hS : S.ShortExact) (n : ℤ) :
    ComposableArrows C 5 :=
  Formalization.Books.Homology.Unit13.cochainCohomologySequence hS n

theorem cochainCohomologyWindow_exact
    (C : Type u) [Category.{v} C] [Abelian C]
    {S : ShortComplex (BookComplex C)} (hS : S.ShortExact) (n : ℤ) :
    (cochainCohomologyWindow C hS n).Exact :=
  Formalization.Books.Homology.Unit13.cochainCohomologySequence_exact hS n

/- The source says that the triangle sequence and the snake-lemma sequence
   agree for a termwise split short exact sequence.  The comparison is made
   explicit as an isomorphism of finite exact windows. -/
theorem termwiseSplitShortComplex_shortExact
    (C : Type u) [Category.{v} C] [Abelian C]
    {A B D : BookComplex C}
    (S : Formalization.Books.Derived.Unit09.TermwiseSplitExactSequence A B D) :
    (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex S).ShortExact := by
  exact HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (S.splitting n).shortExact)

theorem cohomologyLongExactWindow_termwiseSplit_compatibility
    (C : Type u) [Category.{v} C] [Abelian C]
    {A B D : BookComplex C}
    (S : Formalization.Books.Derived.Unit09.TermwiseSplitExactSequence A B D)
    (n : ℤ) :
    Nonempty
      (cohomologyLongExactWindow C
          (Formalization.Books.Derived.Unit09.termwiseSplitTriangleh S) n ≅
        cochainCohomologyWindow C
          (termwiseSplitShortComplex_shortExact C S) n) := by
  let H := cohomologyFunctor C 0
  let T₁ := Formalization.Books.Derived.Unit09.coneTriangleh S.f
  let T₂ := Formalization.Books.Derived.Unit09.termwiseSplitTriangleh S
  obtain ⟨e, he₁, he₂⟩ :=
    Formalization.Books.Derived.Unit09.same_up_to_isomorphisms_of_termwise_split S
  let R₁ := H.homologySequenceComposableArrows₅ T₁ n (n + 1) rfl
  let R₂ := H.homologySequenceComposableArrows₅ T₂ n (n + 1) rfl
  have h₁₀ : R₁.obj' 0 = (H.shift n).obj T₁.obj₁ := by rfl
  have h₁₁ : R₁.obj' 1 = (H.shift n).obj T₁.obj₂ := by rfl
  have h₁₂ : R₁.obj' 2 = (H.shift n).obj T₁.obj₃ := by rfl
  have h₁₃ : R₁.obj' 3 = (H.shift (n + 1)).obj T₁.obj₁ := by rfl
  have h₁₄ : R₁.obj' 4 = (H.shift (n + 1)).obj T₁.obj₂ := by rfl
  have h₁₅ : R₁.obj' 5 = (H.shift (n + 1)).obj T₁.obj₃ := by rfl
  have h₂₀ : R₂.obj' 0 = (H.shift n).obj T₂.obj₁ := by rfl
  have h₂₁ : R₂.obj' 1 = (H.shift n).obj T₂.obj₂ := by rfl
  have h₂₂ : R₂.obj' 2 = (H.shift n).obj T₂.obj₃ := by rfl
  have h₂₃ : R₂.obj' 3 = (H.shift (n + 1)).obj T₂.obj₁ := by rfl
  have h₂₄ : R₂.obj' 4 = (H.shift (n + 1)).obj T₂.obj₂ := by rfl
  have h₂₅ : R₂.obj' 5 = (H.shift (n + 1)).obj T₂.obj₃ := by rfl
  have h₁₀_rfl : h₁₀ = rfl := Subsingleton.elim _ _
  have h₁₁_rfl : h₁₁ = rfl := Subsingleton.elim _ _
  have h₁₂_rfl : h₁₂ = rfl := Subsingleton.elim _ _
  have h₁₃_rfl : h₁₃ = rfl := Subsingleton.elim _ _
  have h₁₄_rfl : h₁₄ = rfl := Subsingleton.elim _ _
  have h₁₅_rfl : h₁₅ = rfl := Subsingleton.elim _ _
  have h₂₀_rfl : h₂₀ = rfl := Subsingleton.elim _ _
  have h₂₁_rfl : h₂₁ = rfl := Subsingleton.elim _ _
  have h₂₂_rfl : h₂₂ = rfl := Subsingleton.elim _ _
  have h₂₃_rfl : h₂₃ = rfl := Subsingleton.elim _ _
  have h₂₄_rfl : h₂₄ = rfl := Subsingleton.elim _ _
  have h₂₅_rfl : h₂₅ = rfl := Subsingleton.elim _ _
  have hm₁₀ :
      R₁.map' 0 1 =
        eqToHom h₁₀ ≫ (H.shift n).map T₁.mor₁ ≫ eqToHom h₁₁.symm := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₁, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
    simp only [Category.id_comp, Category.comp_id]
  have hm₁₁ :
      R₁.map' 1 2 =
        eqToHom h₁₁ ≫ (H.shift n).map T₁.mor₂ ≫ eqToHom h₁₂.symm := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₁, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
    simp only [Category.id_comp, Category.comp_id]
  have hm₁₂ :
      R₁.map' 2 3 =
        eqToHom h₁₂ ≫ H.homologySequenceδ T₁ n (n + 1) rfl ≫ eqToHom h₁₃.symm := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₁, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
    simp only [Category.id_comp, Category.comp_id]
  have hm₁₃ :
      R₁.map' 3 4 =
        eqToHom h₁₃ ≫ (H.shift (n + 1)).map T₁.mor₁ ≫ eqToHom h₁₄.symm := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₁, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
    simp only [Category.id_comp, Category.comp_id]
  have hm₁₄ :
      R₁.map' 4 5 =
        eqToHom h₁₄ ≫ (H.shift (n + 1)).map T₁.mor₂ ≫ eqToHom h₁₅.symm := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₁, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
    simp only [Category.id_comp, Category.comp_id]
  have hm₂₀ :
      R₂.map' 0 1 =
        eqToHom h₂₀ ≫ (H.shift n).map T₂.mor₁ ≫ eqToHom h₂₁.symm := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₂, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
    simp only [Category.id_comp, Category.comp_id]
  have hm₂₁ :
      R₂.map' 1 2 =
        eqToHom h₂₁ ≫ (H.shift n).map T₂.mor₂ ≫ eqToHom h₂₂.symm := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₂, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
    simp only [Category.id_comp, Category.comp_id]
  have hm₂₂ :
      R₂.map' 2 3 =
        eqToHom h₂₂ ≫ H.homologySequenceδ T₂ n (n + 1) rfl ≫ eqToHom h₂₃.symm := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₂, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
    simp only [Category.id_comp, Category.comp_id]
  have hm₂₃ :
      R₂.map' 3 4 =
        eqToHom h₂₃ ≫ (H.shift (n + 1)).map T₂.mor₁ ≫ eqToHom h₂₄.symm := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₂, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
    simp only [Category.id_comp, Category.comp_id]
  have hm₂₄ :
      R₂.map' 4 5 =
        eqToHom h₂₄ ≫ (H.shift (n + 1)).map T₂.mor₂ ≫ eqToHom h₂₅.symm := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₂, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
    simp only [Category.id_comp, Category.comp_id]
  let t₀ : R₁.obj' 0 ≅ R₂.obj' 0 :=
    eqToIso h₁₀ ≪≫ (H.shift n).mapIso (asIso e.hom.hom₁) ≪≫ eqToIso h₂₀.symm
  let t₁ : R₁.obj' 1 ≅ R₂.obj' 1 :=
    eqToIso h₁₁ ≪≫ (H.shift n).mapIso (asIso e.hom.hom₂) ≪≫ eqToIso h₂₁.symm
  let t₂ : R₁.obj' 2 ≅ R₂.obj' 2 :=
    eqToIso h₁₂ ≪≫ (H.shift n).mapIso (asIso e.hom.hom₃) ≪≫ eqToIso h₂₂.symm
  let t₃ : R₁.obj' 3 ≅ R₂.obj' 3 :=
    eqToIso h₁₃ ≪≫ (H.shift (n + 1)).mapIso (asIso e.hom.hom₁) ≪≫
      eqToIso h₂₃.symm
  let t₄ : R₁.obj' 4 ≅ R₂.obj' 4 :=
    eqToIso h₁₄ ≪≫ (H.shift (n + 1)).mapIso (asIso e.hom.hom₂) ≪≫
      eqToIso h₂₄.symm
  let t₅ : R₁.obj' 5 ≅ R₂.obj' 5 :=
    eqToIso h₁₅ ≪≫ (H.shift (n + 1)).mapIso (asIso e.hom.hom₃) ≪≫
      eqToIso h₂₅.symm
  have hm₁₀' :
      R₁.map' 0 1 = (H.shift n).map T₁.mor₁ := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₁, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₁₁' :
      R₁.map' 1 2 = (H.shift n).map T₁.mor₂ := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₁, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₁₂' :
      R₁.map' 2 3 = H.homologySequenceδ T₁ n (n + 1) rfl := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₁, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₁₃' :
      R₁.map' 3 4 = (H.shift (n + 1)).map T₁.mor₁ := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₁, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₁₄' :
      R₁.map' 4 5 = (H.shift (n + 1)).map T₁.mor₂ := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₁, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₂₀' :
      R₂.map' 0 1 = (H.shift n).map T₂.mor₁ := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₂, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₂₁' :
      R₂.map' 1 2 = (H.shift n).map T₂.mor₂ := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₂, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₂₂' :
      R₂.map' 2 3 = H.homologySequenceδ T₂ n (n + 1) rfl := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₂, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₂₃' :
      R₂.map' 3 4 = (H.shift (n + 1)).map T₂.mor₁ := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₂, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₂₄' :
      R₂.map' 4 5 = (H.shift (n + 1)).map T₂.mor₂ := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₂, Functor.homologySequenceComposableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  let ψ : R₁ ⟶ R₂ := ComposableArrows.homMk₅
      ((H.shift n).map e.hom.hom₁)
      ((H.shift n).map e.hom.hom₂)
      ((H.shift n).map e.hom.hom₃)
      ((H.shift (n + 1)).map e.hom.hom₁)
      ((H.shift (n + 1)).map e.hom.hom₂)
      ((H.shift (n + 1)).map e.hom.hom₃)
      (by
        rw [hm₁₀', hm₂₀']
        change (H.shift n).map T₁.mor₁ ≫ (H.shift n).map e.hom.hom₂ =
          (H.shift n).map e.hom.hom₁ ≫ (H.shift n).map T₂.mor₁
        simpa only [eqToHom_trans, eqToHom_refl, Category.id_comp,
          Category.comp_id, Category.assoc, Functor.map_comp] using
          congrArg ((H.shift n).map) e.hom.comm₁)
      (by
        rw [hm₁₁', hm₂₁']
        change (H.shift n).map T₁.mor₂ ≫ (H.shift n).map e.hom.hom₃ =
          (H.shift n).map e.hom.hom₂ ≫ (H.shift n).map T₂.mor₂
        simpa only [eqToHom_trans, eqToHom_refl, Category.id_comp,
          Category.comp_id, Category.assoc, Functor.map_comp] using
          congrArg ((H.shift n).map) e.hom.comm₂)
      (by
        rw [hm₁₂', hm₂₂']
        change H.homologySequenceδ T₁ n (n + 1) rfl ≫
            (H.shift (n + 1)).map e.hom.hom₁ =
          (H.shift n).map e.hom.hom₃ ≫ H.homologySequenceδ T₂ n (n + 1) rfl
        simpa [eqToHom_trans, eqToHom_refl, Category.id_comp,
          Category.comp_id, Category.assoc] using
          (H.homologySequenceδ_naturality T₁ T₂ e.hom n (n + 1) rfl).symm)
      (by
        rw [hm₁₃', hm₂₃']
        change (H.shift (n + 1)).map T₁.mor₁ ≫
            (H.shift (n + 1)).map e.hom.hom₂ =
          (H.shift (n + 1)).map e.hom.hom₁ ≫
            (H.shift (n + 1)).map T₂.mor₁
        simpa only [eqToHom_trans, eqToHom_refl, Category.id_comp,
          Category.comp_id, Category.assoc, Functor.map_comp] using
          congrArg ((H.shift (n + 1)).map) e.hom.comm₁)
      (by
        rw [hm₁₄', hm₂₄']
        change (H.shift (n + 1)).map T₁.mor₂ ≫
            (H.shift (n + 1)).map e.hom.hom₃ =
          (H.shift (n + 1)).map e.hom.hom₂ ≫
            (H.shift (n + 1)).map T₂.mor₂
        simpa only [eqToHom_trans, eqToHom_refl, Category.id_comp,
          Category.comp_id, Category.assoc, Functor.map_comp] using
          congrArg ((H.shift (n + 1)).map) e.hom.comm₂)
  have hψ : IsIso ψ := by
    let : ∀ X : Fin (5 + 1), IsIso (ψ.app X) := by
      intro j
      fin_cases j
      · simp only [ψ]
        change IsIso ((H.shift n).map e.hom.hom₁)
        infer_instance
      · simp only [ψ]
        change IsIso ((H.shift n).map e.hom.hom₂)
        infer_instance
      · simp only [ψ]
        change IsIso ((H.shift n).map e.hom.hom₃)
        infer_instance
      · simp only [ψ]
        change IsIso ((H.shift (n + 1)).map e.hom.hom₁)
        infer_instance
      · simp only [ψ]
        change IsIso ((H.shift (n + 1)).map e.hom.hom₂)
        infer_instance
      · simp only [ψ]
        change IsIso ((H.shift (n + 1)).map e.hom.hom₃)
        infer_instance
    exact NatIso.isIso_of_isIso_app ψ
  let _ : IsIso ψ := hψ
  let heT : R₁ ≅ R₂ := asIso ψ
  let S₀ := Formalization.Books.Derived.Unit09.termwiseSplitShortComplex S
  have hS₀ : S₀.ShortExact := termwiseSplitShortComplex_shortExact C S
  let R₃ :=
    HomologicalComplex.HomologySequence.composableArrows₅ hS₀ n (n + 1) rfl
  let Fₙ := HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n
  let Fₙ₁ := HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (n + 1)
  let d := CochainComplex.mappingCone.descShortComplex S₀
  have hdₙ : IsIso (HomologicalComplex.homologyMap d n) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact
      (CochainComplex.mappingCone.quasiIso_descShortComplex hS₀).quasiIsoAt n
  have hdₙ₁ : IsIso (HomologicalComplex.homologyMap d (n + 1)) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact
      (CochainComplex.mappingCone.quasiIso_descShortComplex hS₀).quasiIsoAt (n + 1)
  let e_dₙ :
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).obj
          (CochainComplex.mappingCone S.f) ≅
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).obj S₀.X₃ :=
    { hom := HomologicalComplex.homologyMap d n
      inv := Classical.choose hdₙ.out
      hom_inv_id := (Classical.choose_spec hdₙ.out).1
      inv_hom_id := (Classical.choose_spec hdₙ.out).2 }
  let e_dₙ₁ :
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (n + 1)).obj
          (CochainComplex.mappingCone S.f) ≅
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (n + 1)).obj
          S₀.X₃ :=
    { hom := HomologicalComplex.homologyMap d (n + 1)
      inv := Classical.choose hdₙ₁.out
      hom_inv_id := (Classical.choose_spec hdₙ₁.out).1
      inv_hom_id := (Classical.choose_spec hdₙ₁.out).2 }
  have hm₃₀' :
      R₃.map' 0 1 = HomologicalComplex.homologyMap S₀.f n := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₃, HomologicalComplex.HomologySequence.composableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₃₁' :
      R₃.map' 1 2 = HomologicalComplex.homologyMap S₀.g n := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₃, HomologicalComplex.HomologySequence.composableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₃₂' :
      R₃.map' 2 3 = hS₀.δ n (n + 1) rfl := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₃, HomologicalComplex.HomologySequence.composableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₃₃' :
      R₃.map' 3 4 = HomologicalComplex.homologyMap S₀.f (n + 1) := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₃, HomologicalComplex.HomologySequence.composableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hm₃₄' :
      R₃.map' 4 5 = HomologicalComplex.homologyMap S₀.g (n + 1) := by
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
    dsimp [R₃, HomologicalComplex.HomologySequence.composableArrows₅,
      ComposableArrows.map', ComposableArrows.precomp,
      ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj]
  have hᵢₙᵣₙ :
      HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr S₀.f) n ≫
          HomologicalComplex.homologyMap d n =
        HomologicalComplex.homologyMap S₀.g n := by
    rw [← HomologicalComplex.homologyMap_comp]
    rw [CochainComplex.mappingCone.inr_descShortComplex]
  have hᵢₙᵣₙ₁ :
      HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr S₀.f) (n + 1) ≫
          HomologicalComplex.homologyMap d (n + 1) =
        HomologicalComplex.homologyMap S₀.g (n + 1) := by
    rw [← HomologicalComplex.homologyMap_comp]
    rw [CochainComplex.mappingCone.inr_descShortComplex]
  have hᵢₙᵣₙ' :
      HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr S.f) n ≫
          HomologicalComplex.homologyMap d n =
        HomologicalComplex.homologyMap S₀.g n := by
    change
      HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr S₀.f) n ≫
          HomologicalComplex.homologyMap d n =
        HomologicalComplex.homologyMap S₀.g n
    exact hᵢₙᵣₙ
  have hᵢₙᵣₙ₁' :
      HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr S.f) (n + 1) ≫
          HomologicalComplex.homologyMap d (n + 1) =
        HomologicalComplex.homologyMap S₀.g (n + 1) := by
    change
      HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr S₀.f) (n + 1) ≫
          HomologicalComplex.homologyMap d (n + 1) =
      HomologicalComplex.homologyMap S₀.g (n + 1)
    exact hᵢₙᵣₙ₁
  let Gₙ :
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)) ⋙ H.shift n ≅
        HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n := Fₙ
  let Gₙ₁ :
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)) ⋙ H.shift (n + 1) ≅
        HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (n + 1) := Fₙ₁
  have hcone₂ :
      (coneTriangleh S.f).mor₂ =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (CochainComplex.mappingCone.inr S.f) := by
    rfl
  let e₀ : R₁.obj' 0 ≅ R₃.obj' 0 :=
    Gₙ.app S₀.X₁
  let e₁ : R₁.obj' 1 ≅ R₃.obj' 1 :=
    Gₙ.app S₀.X₂
  let e₂ : R₁.obj' 2 ≅ R₃.obj' 2 :=
    { hom := Gₙ.hom.app (CochainComplex.mappingCone S.f) ≫
        HomologicalComplex.homologyMap d n
      inv := e_dₙ.inv ≫ Gₙ.inv.app (CochainComplex.mappingCone S.f)
      hom_inv_id := by
        change (Gₙ.hom.app (CochainComplex.mappingCone S.f) ≫ e_dₙ.hom) ≫
            (e_dₙ.inv ≫ Gₙ.inv.app (CochainComplex.mappingCone S.f)) = _
        simp [Category.assoc]
        change 𝟙 ((H.shift n).obj T₁.obj₃) =
          𝟙 ((H.shift n).obj T₁.obj₃)
        rfl
      inv_hom_id := by
        change (e_dₙ.inv ≫ Gₙ.inv.app (CochainComplex.mappingCone S.f)) ≫
            (Gₙ.hom.app (CochainComplex.mappingCone S.f) ≫ e_dₙ.hom) = _
        simp [Category.assoc]
        change 𝟙 ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).obj S₀.X₃) =
          𝟙 ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).obj S₀.X₃)
        rfl }
  let e₃ : R₁.obj' 3 ≅ R₃.obj' 3 :=
    Gₙ₁.app S₀.X₁
  let e₄ : R₁.obj' 4 ≅ R₃.obj' 4 :=
    Gₙ₁.app S₀.X₂
  let e₅ : R₁.obj' 5 ≅ R₃.obj' 5 :=
    { hom := Gₙ₁.hom.app (CochainComplex.mappingCone S.f) ≫
        HomologicalComplex.homologyMap d (n + 1)
      inv := e_dₙ₁.inv ≫ Gₙ₁.inv.app (CochainComplex.mappingCone S.f)
      hom_inv_id := by
        change (Gₙ₁.hom.app (CochainComplex.mappingCone S.f) ≫ e_dₙ₁.hom) ≫
            (e_dₙ₁.inv ≫ Gₙ₁.inv.app (CochainComplex.mappingCone S.f)) = _
        simp [Category.assoc]
        change 𝟙 ((H.shift (n + 1)).obj T₁.obj₃) =
          𝟙 ((H.shift (n + 1)).obj T₁.obj₃)
        rfl
      inv_hom_id := by
        change (e_dₙ₁.inv ≫ Gₙ₁.inv.app (CochainComplex.mappingCone S.f)) ≫
            (Gₙ₁.hom.app (CochainComplex.mappingCone S.f) ≫ e_dₙ₁.hom) = _
        simp [Category.assoc]
        change
          𝟙 ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (n + 1)).obj S₀.X₃) =
            𝟙 ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (n + 1)).obj
              S₀.X₃)
        rfl }
  let φ : R₁ ⟶ R₃ := ComposableArrows.homMk₅
      e₀.hom e₁.hom e₂.hom e₃.hom e₄.hom e₅.hom
      (by
        rw [hm₁₀', hm₃₀']
        change
          (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map
              ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map S₀.f) ≫
          Gₙ.hom.app S₀.X₂ =
          Gₙ.hom.app S₀.X₁ ≫ HomologicalComplex.homologyMap S₀.f n
        exact Gₙ.hom.naturality S₀.f)
      (by
        rw [hm₁₁', hm₃₁']
        dsimp [T₁, e₁, e₂]
        rw [hcone₂]
        rw [← hᵢₙᵣₙ']
        have hnat :=
          congrArg (fun k => k ≫ HomologicalComplex.homologyMap d n)
            (Gₙ.hom.naturality (CochainComplex.mappingCone.inr S.f))
        have hnat' := (Category.assoc _ _ _).symm.trans hnat
        have hnat'' := hnat'.trans (Category.assoc _ _ _)
        convert hnat'' using 1 <;> rfl)
      (by
        rw [hm₁₂', hm₃₂']
        dsimp [T₁, e₂, e₃]
        change
          (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
              (CochainComplex.mappingCone.triangleh S₀.f) n (n + 1) rfl ≫
            Gₙ₁.hom.app S₀.X₁ =
          (Gₙ.hom.app (CochainComplex.mappingCone S.f) ≫
              HomologicalComplex.homologyMap d n) ≫
            hS₀.δ n (n + 1) rfl
        have hδraw :
            (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
                (CochainComplex.mappingCone.triangleh S₀.f) n (n + 1) rfl ≫
                Fₙ₁.hom.app S₀.X₁ =
              (Fₙ.hom.app (CochainComplex.mappingCone S₀.f) ≫
                  HomologicalComplex.homologyMap
                    (CochainComplex.mappingCone.descShortComplex S₀) n) ≫
                hS₀.δ n (n + 1) rfl := by
          have hraw :=
            congrArg (fun k => k ≫ Gₙ₁.hom.app S₀.X₁)
              (CochainComplex.mappingCone.homologySequenceδ_triangleh
                hS₀ n (n + 1) rfl)
          have hG := Gₙ₁.inv_hom_id_app S₀.X₁
          dsimp [Gₙ₁] at hraw
          change
            (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
                (CochainComplex.mappingCone.triangleh S₀.f) n (n + 1) rfl ≫
                Fₙ₁.hom.app S₀.X₁ =
              ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.app
                    (CochainComplex.mappingCone S₀.f) ≫
                  HomologicalComplex.homologyMap
                    (CochainComplex.mappingCone.descShortComplex S₀) n ≫
                  hS₀.δ n (n + 1) rfl ≫ Fₙ₁.inv.app S₀.X₁) ≫ Fₙ₁.hom.app S₀.X₁ at hraw
          simp only [Category.assoc] at hraw
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.defeqAttrib.useBackward true in
          (convert hraw using 1;
            simp only [Fₙ, Category.assoc, HomologicalComplex.homologyFunctor_obj] ;
            rw [hG] ;
            simp only [HomologicalComplex.homologyFunctor_obj, Category.comp_id])
        set_option backward.isDefEq.respectTransparency false in
        set_option backward.defeqAttrib.useBackward true in
        simpa [S₀, d, termwiseSplitShortComplex, Gₙ, Gₙ₁, Fₙ, Fₙ₁,
          HomologicalComplex.homologyFunctor_obj, Category.assoc] using hδraw)
      (by
        rw [hm₁₃', hm₃₃']
        dsimp [H, T₁, e₃, e₄]
        simp only [cohomologyFunctor_shift C (n + 1)]
        change
          (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (n + 1)).map
              ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map S₀.f) ≫
          Gₙ₁.hom.app S₀.X₂ =
          Gₙ₁.hom.app S₀.X₁ ≫ HomologicalComplex.homologyMap S₀.f (n + 1)
        exact Gₙ₁.hom.naturality S₀.f)
      (by
        rw [hm₁₄', hm₃₄']
        dsimp [T₁, e₄, e₅]
        rw [hcone₂]
        rw [← hᵢₙᵣₙ₁']
        have hnat :=
          congrArg (fun k => k ≫ HomologicalComplex.homologyMap d (n + 1))
            (Gₙ₁.hom.naturality (CochainComplex.mappingCone.inr S.f))
        have hnat' := (Category.assoc _ _ _).symm.trans hnat
        have hnat'' := hnat'.trans (Category.assoc _ _ _)
        convert hnat'' using 1 <;> rfl)
  have hφ : IsIso φ := by
    let : ∀ X : Fin (5 + 1), IsIso (φ.app X) := by
      intro j
      fin_cases j
      · simp only [φ]
        change IsIso e₀.hom
        infer_instance
      · simp only [φ]
        change IsIso e₁.hom
        infer_instance
      · simp only [φ, ComposableArrows.homMk₅_app_two]
        change IsIso e₂.hom
        exact e₂.isIso_hom
      · simp only [φ, ComposableArrows.homMk₅_app_three]
        change IsIso e₃.hom
        infer_instance
      · simp only [φ, ComposableArrows.homMk₅_app_four]
        change IsIso e₄.hom
        infer_instance
      · simp only [φ, ComposableArrows.homMk₅_app_five]
        change IsIso e₅.hom
        exact e₅.isIso_hom
    exact NatIso.isIso_of_isIso_app φ
  let _ : IsIso φ := hφ
  let hraw : R₁ ≅ R₃ := asIso φ
  exact ⟨heT.symm ≪≫ hraw⟩

/-! ## Acyclic complexes, quasi-isomorphisms, and the unbounded derived category -/

/-- The source's acyclic subcategory of `K(𝒜)`. -/
abbrev acyclicHomotopyProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (BookHomotopyCategory C) :=
  HomotopyCategory.subcategoryAcyclic C

/-- The source's quasi-isomorphism multiplicative system on `K(𝒜)`. -/
abbrev quasiIsoHomotopyProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (BookHomotopyCategory C) :=
  HomotopyCategory.quasiIso C (ComplexShape.up ℤ)

/-- The recalled complex-level notion of acyclicity. -/
abbrev AcyclicComplex
    {C : Type u} [Category.{v} C] [Abelian C] (K : BookComplex C) : Prop :=
  K.Acyclic

/-- The recalled complex-level notion of quasi-isomorphism. -/
abbrev QuasiIsomorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : BookComplex C} (f : K ⟶ L) : Prop :=
  QuasiIso f

theorem acyclicComplex_iff_cohomology_zero
    (C : Type u) [Category.{v} C] [Abelian C] (K : BookComplex C) :
    AcyclicComplex K ↔ ∀ n : ℤ, IsZero (K.homology n) :=
  Formalization.Books.Homology.Unit13.cochain_acyclic_iff_cohomology_isZero K

theorem quasiIsomorphism_iff_cohomology_isIso
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : BookComplex C} (f : K ⟶ L) :
    QuasiIsomorphism f ↔
      ∀ n : ℤ, IsIso (HomologicalComplex.homologyMap f n) :=
  Formalization.Books.Homology.Unit13.cochain_quasiIso_iff_cohomologyMap_isIso f

/-- The object property of objects killed by a functor. -/
def functorKernel {E F : Type*} [Category* E] [Category* F]
    (G : E ⥤ F) : ObjectProperty E :=
  fun X => IsZero (G.obj X)

/-- Acyclic objects form the source's strictly full saturated triangulated subcategory. -/
theorem acyclicHomotopyProperty_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    IsStrictlyFullSaturatedPretriangulated (acyclicHomotopyProperty C) := by
  simpa [acyclicHomotopyProperty, HomotopyCategory.subcategoryAcyclic] using
    homologicalFunctorKernel_properties (cohomologyFunctor C 0)

/-- Quasi-isomorphisms are the saturated multiplicative system attached to acyclic objects. -/
theorem quasiIsoHomotopyProperty_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    SaturatedMultiplicativeSystem (quasiIsoHomotopyProperty C) ∧
      CompatibleWithTriangulation (quasiIsoHomotopyProperty C) := by
  change SaturatedMultiplicativeSystem (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ∧
    CompatibleWithTriangulation (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic C]
  have hP := homologicalFunctorKernel_properties (cohomologyFunctor C 0)
  constructor
  · simpa only [subcategoryOperation, quotientMorphismProperty,
      ObjectProperty.trW_isoClosure] using
      ((quotientMorphismProperty_isSaturated_iff (acyclicHomotopyProperty C)).2 hP.2.2)
  · infer_instance

/-- Mathlib identifies quasi-isomorphisms with the cone morphism property of acyclic objects. -/
theorem quasiIsoHomotopyProperty_eq_acyclic_trW
    (C : Type u) [Category.{v} C] [Abelian C] :
    quasiIsoHomotopyProperty C = (acyclicHomotopyProperty C).trW :=
  HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic C

/-- The derived category, as supplied by Mathlib, is the localization of `K(𝒜)`. -/
theorem derivedCategory_is_localization
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (DerivedCategory.Qh (C := C)).IsLocalization
      (quasiIsoHomotopyProperty C) := by
  infer_instance

/-- The same localization is the Verdier quotient by the acyclic subcategory. -/
theorem derivedCategory_is_acyclic_localization
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (DerivedCategory.Qh (C := C)).IsLocalization
      (acyclicHomotopyProperty C).trW := by
  infer_instance

/-- The kernel of the localization functor is the acyclic subcategory. -/
theorem derivedCategory_kernel
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    functorKernel (DerivedCategory.Qh (C := C)) = acyclicHomotopyProperty C := by
  ext X
  let P : ObjectProperty (BookHomotopyCategory C) := acyclicHomotopyProperty C
  have hP : IsStrictlyFullSaturatedPretriangulated P := by
    simpa [P, acyclicHomotopyProperty, HomotopyCategory.subcategoryAcyclic] using
      homologicalFunctorKernel_properties (cohomologyFunctor C 0)
  have hW : quasiIsoHomotopyProperty C = quotientMorphismProperty P := by
    change HomotopyCategory.quasiIso C (ComplexShape.up ℤ) = P.isoClosure.trW
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic C]
    simp [P, ObjectProperty.trW_isoClosure]
  let _ : P.IsClosedUnderIsomorphisms := hP.1
  let _ : P.IsTriangulated := hP.2.1
  let _ : (DerivedCategory.Qh (C := C)).IsLocalization
      (quotientMorphismProperty P) := by
    rw [← hW]
    infer_instance
  let E := Localization.uniq (quotientFunctor P) (DerivedCategory.Qh (C := C))
    (quotientMorphismProperty P)
  have hQ (X : BookHomotopyCategory C) :
      IsZero ((DerivedCategory.Qh (C := C)).obj X) ↔
        IsZero ((quotientFunctor P).obj X) := by
    have eInv : E.inverse.obj ((DerivedCategory.Qh (C := C)).obj X) ≅
        (quotientFunctor P).obj X := by
      simpa [E] using
        (Localization.compUniqInverse (quotientFunctor P)
          (DerivedCategory.Qh (C := C)) (quotientMorphismProperty P)).app X
    have eFun : E.functor.obj ((quotientFunctor P).obj X) ≅
        (DerivedCategory.Qh (C := C)).obj X := by
      simpa [E] using
        (Localization.compUniqFunctor (quotientFunctor P)
          (DerivedCategory.Qh (C := C)) (quotientMorphismProperty P)).app X
    constructor
    · intro hX
      exact (E.inverse.map_isZero hX).of_iso eInv.symm
    · intro hX
      exact (E.functor.map_isZero hX).of_iso eFun.symm
  have hK (X : BookHomotopyCategory C) : quotientKernel P X ↔ P X := by
    constructor
    · rintro ⟨Y, hY⟩
      have hparts := hP.2.2 hY
      rw [ObjectProperty.isoClosure_eq_self] at hparts
      exact hparts.1
    · intro hX
      exact (quotientKernel_is_smallest P).2.1 X hX
  constructor
  · intro hX
    exact (hK X).1 ((quotientFunctor_kernel_iff P X).1 ((hQ X).1 hX))
  · intro hX
    exact (hQ X).2 ((quotientFunctor_kernel_iff P X).2 ((hK X).2 hX))

/-! ### Cohomology on the derived category and the size warning -/

/-- The canonical degree-`n` cohomology functor on `D(𝒜)`. -/
noncomputable abbrev derivedCohomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (n : ℤ) : DerivedCategory C ⥤ C :=
  DerivedCategory.homologyFunctor C n

/-- The canonical factorization of `H⁰` through the localization. -/
noncomputable def derivedCohomologyZeroFactorIso
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (DerivedCategory.Qh (C := C)) ⋙ derivedCohomologyFunctor C 0 ≅
      cohomologyFunctor C 0 :=
  DerivedCategory.homologyFunctorFactorsh C 0

/-- Two complexes are quasi-isomorphic as objects when their images in `D(𝒜)`
are isomorphic. -/
def DerivedQuasiIsomorphic
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K L : BookComplex C) : Prop :=
  Nonempty ((DerivedCategory.Q (C := C)).obj K ≅
    (DerivedCategory.Q (C := C)).obj L)

/- The source's smallness warning is represented by Mathlib's explicit choice
   of a universe for the morphisms in a derived category.  For a Grothendieck
   category, a K-injective replacement gives the following usable Hom-set
   comparison; the existence of such replacements is supplied by the relevant
   later injective-resolution development. -/
theorem derivedCategory_map_bijective_to_KInjective
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : BookHomotopyCategory C) (I : BookComplex C) [I.IsKInjective] :
    Function.Bijective
      ((DerivedCategory.Qh (C := C)).map :
        (K ⟶ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I) → _) :=
  CochainComplex.IsKInjective.Qh_map_bijective K I

/-- The K-injective replacement assertion used in the size discussion. -/
def HasKInjectiveResolution
    (C : Type u) [Category.{v} C] [Abelian C] (L : BookComplex C) : Prop :=
  ∃ (I : BookComplex C) (f : L ⟶ I),
    QuasiIsomorphism f ∧ I.IsKInjective

theorem grothendieck_hasKInjectiveResolution
    (C : Type u) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] (L : BookComplex C) :
    HasKInjectiveResolution C L := by
  sorry

/-! ## Bounded pieces of the derived category -/

/-- Vanishing of cohomology in all sufficiently negative degrees. -/
def derivedCohomologyVanishesBelow
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero ((derivedCohomologyFunctor C n).obj X)

/-- Vanishing of cohomology in all sufficiently positive degrees. -/
def derivedCohomologyVanishesAbove
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero ((derivedCohomologyFunctor C n).obj X)

/-- Vanishing of cohomology outside a bounded range. -/
def derivedCohomologyVanishesBounded
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) : Prop :=
  derivedCohomologyVanishesBelow C X ∧ derivedCohomologyVanishesAbove C X

/-- The canonical t-structure properties used for `D⁺`, `D⁻`, and `Dᵇ`. -/
abbrev derivedPlusProperty
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    ObjectProperty (DerivedCategory C) :=
  (DerivedCategory.TStructure.t (C := C)).plus

abbrev derivedMinusProperty
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    ObjectProperty (DerivedCategory C) :=
  (DerivedCategory.TStructure.t (C := C)).minus

abbrev derivedBoundedProperty
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    ObjectProperty (DerivedCategory C) :=
  (DerivedCategory.TStructure.t (C := C)).bounded

/-- The source's bounded-below derived category, using Mathlib's canonical one. -/
abbrev DPlus
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :=
  DerivedCategory.Plus C

/-- The source's bounded-above derived category, using Mathlib's canonical one. -/
abbrev DMinus
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :=
  DerivedCategory.Minus C

/-- The source's bounded derived category, using Mathlib's canonical one. -/
abbrev DBounded
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :=
  DerivedCategory.Bounded C

noncomputable instance derivedCategory_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    AdditiveCategory (DerivedCategory C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

theorem derivedPlusProperty_iff
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) :
    derivedPlusProperty C X ↔ derivedCohomologyVanishesBelow C X := by
  sorry

theorem derivedMinusProperty_iff
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) :
    derivedMinusProperty C X ↔ derivedCohomologyVanishesAbove C X := by
  sorry

theorem derivedBoundedProperty_iff
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) :
    derivedBoundedProperty C X ↔ derivedCohomologyVanishesBounded C X := by
  sorry

/-- The three bounded derived pieces are strictly full saturated triangulated subcategories. -/
theorem derivedBoundedSubcategory_properties
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    IsStrictlyFullSaturatedPretriangulated (derivedPlusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (derivedMinusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (derivedBoundedProperty C) := by
  sorry

/-! ## Bounded-cohomology replacements -/

theorem boundedCohomology_replacement_below
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : BookComplex C)
    (hK : ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero (K.homology n)) :
    ∃ (L : BookComplex C) (f : K ⟶ L),
      QuasiIso f ∧ IsBoundedBelow L := by
  sorry

theorem boundedCohomology_replacement_above
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : BookComplex C)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K.homology n)) :
    ∃ (M : BookComplex C) (f : M ⟶ K),
      QuasiIso f ∧ IsBoundedAbove M := by
  sorry

theorem boundedCohomology_replacement_bounded
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : BookComplex C)
    (hK :
      (∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero (K.homology n)) ∧
      (∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K.homology n))) :
    ∃ (L M N : BookComplex C)
      (f : K ⟶ L) (g : M ⟶ K) (u : M ⟶ N) (v : N ⟶ L),
      g ≫ f = u ≫ v ∧
      QuasiIso f ∧ QuasiIso g ∧ QuasiIso u ∧ QuasiIso v ∧
      IsBoundedBelow L ∧ IsBoundedAbove M ∧ IsBounded N := by
  sorry

/-! ## Bounded homotopy subcategories and their acyclic localizations -/

abbrev KPlusInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    KPlus C ⥤ BookHomotopyCategory C :=
  HomotopyCategory.Plus.ι C

abbrev KMinusInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    KMinus C ⥤ BookHomotopyCategory C :=
  (boundedAboveHomotopyProperty C).ι

abbrev KBoundedInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    KBounded C ⥤ BookHomotopyCategory C :=
  (boundedHomotopyProperty C).ι

abbrev acyclicPlusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (KPlus C) :=
  HomotopyCategory.Plus.subcategoryAcyclic C

abbrev acyclicMinusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (KMinus C) :=
  (acyclicHomotopyProperty C).inverseImage (KMinusInclusion C)

abbrev acyclicBoundedProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (KBounded C) :=
  (acyclicHomotopyProperty C).inverseImage (KBoundedInclusion C)

abbrev quasiIsoPlusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (KPlus C) :=
  HomotopyCategory.Plus.quasiIso C

abbrev quasiIsoMinusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (KMinus C) :=
  (quasiIsoHomotopyProperty C).inverseImage (KMinusInclusion C)

abbrev quasiIsoBoundedProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (KBounded C) :=
  (quasiIsoHomotopyProperty C).inverseImage (KBoundedInclusion C)

noncomputable instance kPlus_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (KPlus C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

noncomputable instance kMinus_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (KMinus C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

noncomputable instance kBounded_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (KBounded C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

theorem boundedAcyclicSubcategory_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    IsStrictlyFullSaturatedPretriangulated (acyclicPlusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (acyclicMinusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (acyclicBoundedProperty C) := by
  sorry

theorem boundedQuasiIsoProperty_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    SaturatedMultiplicativeSystem (quasiIsoPlusProperty C) ∧
      SaturatedMultiplicativeSystem (quasiIsoMinusProperty C) ∧
      SaturatedMultiplicativeSystem (quasiIsoBoundedProperty C) := by
  sorry

/-! ### The three localization functors -/

noncomputable abbrev plusDerivedLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    KPlus C ⥤ DPlus C :=
  DerivedCategory.Plus.Qh (C := C)

theorem plusDerivedLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (plusDerivedLocalizationFunctor C).IsLocalization
      (quasiIsoPlusProperty C) := by
  infer_instance

noncomputable def plusLocalizationComparison
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (quasiIsoPlusProperty C).Localization ⥤ DPlus C :=
  Localization.Construction.lift (plusDerivedLocalizationFunctor C) (by
    intro X Y f hf
    exact Localization.inverts (plusDerivedLocalizationFunctor C)
      (quasiIsoPlusProperty C) f hf)

theorem plusLocalizationComparison_is_equivalence
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    Functor.IsEquivalence (plusLocalizationComparison C) := by
  sorry

theorem plusDerivedLocalizationFunctor_kernel
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    functorKernel (plusDerivedLocalizationFunctor C) = acyclicPlusProperty C := by
  sorry

theorem derivedQh_maps_KMinus_to_DMinus
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : KMinus C) :
    derivedMinusProperty C
      ((KMinusInclusion C ⋙ DerivedCategory.Qh (C := C)).obj X) := by
  sorry

noncomputable def minusDerivedLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    KMinus C ⥤ DMinus C :=
  (derivedMinusProperty C).lift
    (KMinusInclusion C ⋙ DerivedCategory.Qh (C := C))
    (derivedQh_maps_KMinus_to_DMinus C)

theorem minusDerivedLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (minusDerivedLocalizationFunctor C).IsLocalization
      (quasiIsoMinusProperty C) := by
  sorry

noncomputable def minusLocalizationComparison
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (quasiIsoMinusProperty C).Localization ⥤ DMinus C :=
  Localization.Construction.lift (minusDerivedLocalizationFunctor C) (by
    exact (minusDerivedLocalizationFunctor_is_localization C).inverts)

theorem minusLocalizationComparison_is_equivalence
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    Functor.IsEquivalence (minusLocalizationComparison C) := by
  sorry

theorem minusDerivedLocalizationFunctor_kernel
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    functorKernel (minusDerivedLocalizationFunctor C) = acyclicMinusProperty C := by
  sorry

theorem derivedQh_maps_KBounded_to_DBounded
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : KBounded C) :
    derivedBoundedProperty C
      ((KBoundedInclusion C ⋙ DerivedCategory.Qh (C := C)).obj X) := by
  sorry

noncomputable def boundedDerivedLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    KBounded C ⥤ DBounded C :=
  (derivedBoundedProperty C).lift
    (KBoundedInclusion C ⋙ DerivedCategory.Qh (C := C))
    (derivedQh_maps_KBounded_to_DBounded C)

theorem boundedDerivedLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (boundedDerivedLocalizationFunctor C).IsLocalization
      (quasiIsoBoundedProperty C) := by
  sorry

noncomputable def boundedLocalizationComparison
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (quasiIsoBoundedProperty C).Localization ⥤ DBounded C :=
  Localization.Construction.lift (boundedDerivedLocalizationFunctor C) (by
    exact (boundedDerivedLocalizationFunctor_is_localization C).inverts)

theorem boundedLocalizationComparison_is_equivalence
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    Functor.IsEquivalence (boundedLocalizationComparison C) := by
  sorry

theorem boundedDerivedLocalizationFunctor_kernel
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    functorKernel (boundedDerivedLocalizationFunctor C) = acyclicBoundedProperty C := by
  sorry

end Formalization.Books.Derived.Unit11
