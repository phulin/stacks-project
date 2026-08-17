import Formalization.Books.Categories.Unit16.ConnectedLimits
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Limits.Final.Connected

/-!
# Categories, Chapter 17: Cofinal and initial categories

The source's cofinal and initial functors are Mathlib's `Functor.Final` and
`Functor.Initial`.  Their connected structured-arrow and costructured-arrow
characterizations retain the source's existence and zigzag conditions, while
Mathlib's comparison isomorphisms give the canonical (co)limit statements.
-/

namespace Formalization.Books.Categories.Unit17

open CategoryTheory
open CategoryTheory.Limits

universe u v u' v'

noncomputable section

/-! ## Cofinal functors -/

/- The source notes that “final” is also used for the notion called
   “cofinal” here.  Mathlib uses `Functor.Final` for this canonical notion. -/

/-- The source's predicate that a functor is cofinal. -/
abbrev IsCofinal {I J : Type*} [Category I] [Category J] (H : I ⥤ J) : Prop :=
  Functor.Final H

/-- Cofinality is connectedness of every structured-arrow category. -/
theorem isCofinal_iff_structuredArrow_connected
    {I J : Type*} [Category I] [Category J] (H : I ⥤ J) :
    IsCofinal H ↔ ∀ y : J, IsConnected (StructuredArrow y H) := by
  constructor
  · intro h y
    exact h.out y
  · intro h
    exact ⟨h⟩

/-- The source's existence and generated-equivalence conditions for cofinality.

`StructuredArrow y H` has as objects the pairs `(x, y ⟶ H.obj x)`, and
`Zigzag` is the generated equivalence relation on these choices. -/
theorem isCofinal_iff_zigzag
    {I J : Type*} [Category I] [Category J] (H : I ⥤ J) :
    IsCofinal H ↔
      ∀ y : J,
        Nonempty (StructuredArrow y H) ∧
          ∀ a b : StructuredArrow y H, Zigzag a b := by
  constructor
  · intro h y
    exact
      (Formalization.Books.Categories.Unit16.category_connected_iff_zigzag
          (StructuredArrow y H)).mp (h.out y)
  · intro h
    refine ⟨fun y => ?_⟩
    exact
      (Formalization.Books.Categories.Unit16.category_connected_iff_zigzag
          (StructuredArrow y H)).mpr (h y)

/-! ## Cofinal functors and colimits -/

/-- A cofinal functor preserves existence of colimits, in both directions. -/
theorem hasColimit_comp_iff_of_cofinal
    {I J C : Type*} [Category I] [Category J] [Category C]
    (H : I ⥤ J) [IsCofinal H] (M : J ⥤ C) :
    HasColimit (H ⋙ M) ↔ HasColimit M :=
  Functor.Final.hasColimit_comp_iff H

/-- The canonical comparison isomorphism for a cofinal functor. -/
noncomputable def colimit_comp_iso_of_cofinal
    {I J C : Type*} [Category I] [Category J] [Category C]
    (H : I ⥤ J) [IsCofinal H] (M : J ⥤ C) [HasColimit M] :
    colimit (H ⋙ M) ≅ colimit M :=
  Functor.Final.colimitIso H M

/-! ## Initial functors -/

/-- The source's predicate that a functor is initial. -/
abbrev IsInitialFunctor {I J : Type*} [Category I] [Category J] (H : I ⥤ J) : Prop :=
  Functor.Initial H

/-- Initiality is connectedness of every costructured-arrow category. -/
theorem isInitial_iff_costructuredArrow_connected
    {I J : Type*} [Category I] [Category J] (H : I ⥤ J) :
    IsInitialFunctor H ↔ ∀ y : J, IsConnected (CostructuredArrow H y) := by
  constructor
  · intro h y
    exact h.out y
  · intro h
    exact ⟨h⟩

/-- Initiality is the dual of cofinality, via passage to opposite categories. -/
theorem isInitial_iff_isCofinal_op
    {I J : Type*} [Category I] [Category J] (H : I ⥤ J) :
    IsInitialFunctor H ↔ IsCofinal H.op := by
  constructor
  · intro h
    exact @Functor.final_op_of_initial I _ J _ H h
  · intro h
    exact @Functor.initial_of_final_op I _ J _ H h

/-- The source's existence and generated-equivalence conditions for initiality.

`CostructuredArrow H y` has as objects the pairs `(x, H.obj x ⟶ y)`, with
`Zigzag` recording the source's alternating sequence of compatible arrows. -/
theorem isInitial_iff_zigzag
    {I J : Type*} [Category I] [Category J] (H : I ⥤ J) :
    IsInitialFunctor H ↔
      ∀ y : J,
        Nonempty (CostructuredArrow H y) ∧
          ∀ a b : CostructuredArrow H y, Zigzag a b := by
  constructor
  · intro h y
    exact
      (Formalization.Books.Categories.Unit16.category_connected_iff_zigzag
          (CostructuredArrow H y)).mp (h.out y)
  · intro h
    refine ⟨fun y => ?_⟩
    exact
      (Formalization.Books.Categories.Unit16.category_connected_iff_zigzag
          (CostructuredArrow H y)).mpr (h y)

/-! ## Initial functors and limits -/

/-- An initial functor preserves existence of limits, in both directions. -/
theorem hasLimit_comp_iff_of_initial
    {I J C : Type*} [Category I] [Category J] [Category C]
    (H : I ⥤ J) [IsInitialFunctor H] (M : J ⥤ C) :
    HasLimit (H ⋙ M) ↔ HasLimit M :=
  Functor.Initial.hasLimit_comp_iff H

/-- The canonical comparison isomorphism for an initial functor. -/
noncomputable def limit_comp_iso_of_initial
    {I J C : Type*} [Category I] [Category J] [Category C]
    (H : I ⥤ J) [IsInitialFunctor H] (M : J ⥤ C) [HasLimit M] :
    limit (H ⋙ M) ≅ limit M :=
  Functor.Initial.limitIso H M

/-! ## Connected fibres -/

/- The source states that every morphism in the target is the image of a
   morphism upstairs.  Since Lean records the endpoints of a morphism in its
   type, the endpoint equalities and their canonical transports are explicit. -/

/-- Every morphism in the target of `F` is lifted from a morphism in its source.

The equality uses `eqToHom` to transport the endpoints of `F.map g` to the
specified endpoints of the target morphism. -/
def LiftsMorphisms {I J : Type*} [Category I] [Category J] (F : I ⥤ J) : Prop :=
  ∀ {X Y : J} (f : X ⟶ Y),
    ∃ (x y : I) (hx : F.obj x = X) (hy : F.obj y = Y) (g : x ⟶ y),
      eqToHom hx.symm ≫ F.map g ≫ eqToHom hy = f

/- The informal proof of the connected-fibre lemma first establishes
   cofinality and then applies the cofinal-colimit comparison. -/
theorem isCofinal_of_connected_fibers
    {I J : Type*} [Category I] [Category J]
    (F : I ⥤ J)
    (hF : ∀ y : J, IsConnected (Functor.Fiber F y))
    (hmap : LiftsMorphisms F) :
    IsCofinal F := by
  sorry

/-- Connected fibres and lifting of all target morphisms preserve colimits. -/
theorem hasColimit_comp_iff_of_connected_fibers
    {I J C : Type*} [Category I] [Category J] [Category C]
    (F : I ⥤ J)
    (hF : ∀ y : J, IsConnected (Functor.Fiber F y))
    (hmap : LiftsMorphisms F) (M : J ⥤ C) :
    HasColimit (F ⋙ M) ↔ HasColimit M := by
  exact
    @Functor.Final.hasColimit_comp_iff I _ J _ F
      (isCofinal_of_connected_fibers F hF hmap) C _ M

/-- The canonical colimit comparison under the connected-fibre hypotheses. -/
noncomputable def colimit_comp_iso_of_connected_fibers
    {I J C : Type*} [Category I] [Category J] [Category C]
    (F : I ⥤ J)
    (hF : ∀ y : J, IsConnected (Functor.Fiber F y))
    (hmap : LiftsMorphisms F) (M : J ⥤ C) [HasColimit M]
    [HasColimit (F ⋙ M)] :
    colimit (F ⋙ M) ≅ colimit M := by
  exact
    @Functor.Final.colimitIso I _ J _ F
      (isCofinal_of_connected_fibers F hF hmap) C _ M inferInstance

/-! ## Product with a connected category -/

/-- A connected first factor does not change the existence of a colimit. -/
theorem hasColimit_prod_snd_iff
    {I J C : Type*} [Category I] [Category J] [Category C]
    [IsConnected I] (M : J ⥤ C) :
    HasColimit M ↔ HasColimit ((CategoryTheory.Prod.snd I J) ⋙ M) :=
  (Functor.Final.hasColimit_comp_iff (CategoryTheory.Prod.snd I J)).symm

/-- The canonical comparison for the projection `I × J ⥤ J`. -/
noncomputable def colimit_prod_snd_iso
    {I J C : Type*} [Category I] [Category J] [Category C]
    [IsConnected I] (M : J ⥤ C) [HasColimit M] :
    colimit ((CategoryTheory.Prod.snd I J) ⋙ M) ≅ colimit M :=
  Functor.Final.colimitIso (CategoryTheory.Prod.snd I J) M

end

end Formalization.Books.Categories.Unit17
