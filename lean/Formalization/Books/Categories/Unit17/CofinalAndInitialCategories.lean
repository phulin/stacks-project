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

/-- Cofinality is connectedness of every structured-arrow category. -/
theorem isCofinal_iff_structuredArrow_connected
    {I J : Type*} [Category I] [Category J] (H : I ⥤ J) :
    Functor.Final H ↔ ∀ y : J, IsConnected (StructuredArrow y H) := by
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
    Functor.Final H ↔
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
    (H : I ⥤ J) [Functor.Final H] (M : J ⥤ C) :
    HasColimit (H ⋙ M) ↔ HasColimit M :=
  Functor.Final.hasColimit_comp_iff H

/-- The canonical comparison isomorphism for a cofinal functor. -/
noncomputable def colimit_comp_iso_of_cofinal
    {I J C : Type*} [Category I] [Category J] [Category C]
    (H : I ⥤ J) [Functor.Final H] (M : J ⥤ C) [HasColimit M] :
    colimit (H ⋙ M) ≅ colimit M :=
  Functor.Final.colimitIso H M

/-- The same comparison when the colimit of the restricted diagram is given. -/
noncomputable def colimit_comp_iso_of_cofinal_of_comp
    {I J C : Type*} [Category I] [Category J] [Category C]
    (H : I ⥤ J) [Functor.Final H] (M : J ⥤ C) [HasColimit (H ⋙ M)] :
    letI : HasColimit M := Functor.Final.hasColimit_of_comp H
    colimit (H ⋙ M) ≅ colimit M := by
  letI : HasColimit M := Functor.Final.hasColimit_of_comp H
  exact Functor.Final.colimitIso H M

/-! ## Initial functors -/

/-- Initiality is connectedness of every costructured-arrow category. -/
theorem isInitial_iff_costructuredArrow_connected
    {I J : Type*} [Category I] [Category J] (H : I ⥤ J) :
    Functor.Initial H ↔ ∀ y : J, IsConnected (CostructuredArrow H y) := by
  constructor
  · intro h y
    exact h.out y
  · intro h
    exact ⟨h⟩

/-- Initiality is the dual of cofinality, via passage to opposite categories. -/
theorem isInitial_iff_isCofinal_op
    {I J : Type*} [Category I] [Category J] (H : I ⥤ J) :
    Functor.Initial H ↔ Functor.Final H.op := by
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
    Functor.Initial H ↔
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
    (H : I ⥤ J) [Functor.Initial H] (M : J ⥤ C) :
    HasLimit (H ⋙ M) ↔ HasLimit M :=
  Functor.Initial.hasLimit_comp_iff H

/-- The canonical comparison isomorphism for an initial functor. -/
noncomputable def limit_comp_iso_of_initial
    {I J C : Type*} [Category I] [Category J] [Category C]
    (H : I ⥤ J) [Functor.Initial H] (M : J ⥤ C) [HasLimit M] :
    limit (H ⋙ M) ≅ limit M :=
  Functor.Initial.limitIso H M

/-- The same comparison when the limit of the restricted diagram is given. -/
noncomputable def limit_comp_iso_of_initial_of_comp
    {I J C : Type*} [Category I] [Category J] [Category C]
    (H : I ⥤ J) [Functor.Initial H] (M : J ⥤ C) [HasLimit (H ⋙ M)] :
    letI : HasLimit M := Functor.Initial.hasLimit_of_comp H
    limit (H ⋙ M) ≅ limit M := by
  letI : HasLimit M := Functor.Initial.hasLimit_of_comp H
  exact Functor.Initial.limitIso H M

/-! ## Connected fibres -/

/- The source states that every morphism in the target is the image of a
   morphism upstairs.  `Functor.IsHomLift` supplies the endpoint equalities
   and their canonical transports. -/

/-- Every morphism in the target of `F` is lifted from a morphism in its source.

`Functor.IsHomLift` records both the endpoint equalities and the equality of
the transported image with the target morphism. -/
def LiftsMorphisms {I J : Type*} [Category I] [Category J] (F : I ⥤ J) : Prop :=
  ∀ {X Y : J} (f : X ⟶ Y),
    ∃ (x y : I) (g : x ⟶ y), F.IsHomLift f g

/- The informal proof of the connected-fibre lemma first establishes
   cofinality and then applies the cofinal-colimit comparison. -/
theorem isCofinal_of_connected_fibers
    {I J : Type*} [Category I] [Category J]
    (F : I ⥤ J)
    (hF : ∀ y : J, IsConnected (Functor.Fiber F y))
    (hmap : LiftsMorphisms F) :
    Functor.Final F := by
  refine ⟨fun y => ?_⟩
  let fiberToStructured (y z : J) (f : y ⟶ z) :
      Functor.Fiber F z ⥤ StructuredArrow y F :=
    { obj := fun x => StructuredArrow.mk (f ≫ eqToHom x.2.symm)
      map := fun {x x'} φ => by
        exact StructuredArrow.homMk φ.1 (by
          change (f ≫ eqToHom x.2.symm) ≫ F.map φ.1 =
            f ≫ eqToHom x'.2.symm
          rw [Category.assoc,
            @IsHomLift.fac' _ _ _ _ F _ _ _ _ (𝟙 z) φ.1 φ.2]
          simp) }
  let source := fiberToStructured y y (𝟙 y)
  obtain ⟨x₀, x₁, g, hg⟩ := hmap (𝟙 y)
  have hnonempty : Nonempty (StructuredArrow y F) :=
    ⟨StructuredArrow.mk
      (eqToHom (@IsHomLift.domain_eq _ _ _ _ F _ _ _ _ (𝟙 y) g hg).symm)⟩
  apply @zigzag_isConnected (StructuredArrow y F) _ hnonempty
  intro a b
  obtain ⟨x₀, x₁, g, hg⟩ := hmap a.hom
  let p₁ : Functor.Fiber F y :=
    ⟨x₀, @IsHomLift.domain_eq _ _ _ _ F _ _ _ _ a.hom g hg⟩
  let q₁ : Functor.Fiber F (F.obj a.right) :=
    ⟨x₁, @IsHomLift.codomain_eq _ _ _ _ F _ _ _ _ a.hom g hg⟩
  let r₁ : Functor.Fiber F (F.obj a.right) := ⟨a.right, rfl⟩
  have h₁ : (fiberToStructured y (F.obj a.right) a.hom).obj r₁ = a := by
    calc
      (fiberToStructured y (F.obj a.right) a.hom).obj r₁ =
          StructuredArrow.mk a.hom := by simp [fiberToStructured, r₁]
      _ = a := (StructuredArrow.eq_mk a).symm
  have hz₁ :
    Zigzag ((fiberToStructured y (F.obj a.right) a.hom).obj q₁) a :=
    (zigzag_obj_of_zigzag (fiberToStructured y (F.obj a.right) a.hom)
      (@isPreconnected_zigzag _ _ (hF (F.obj a.right)).toIsPreconnected q₁ r₁)).trans
        (by rw [h₁])
  have hg₁ :
      (source.obj p₁ ⟶
        (fiberToStructured y (F.obj a.right) a.hom).obj q₁) := by
    exact StructuredArrow.homMk g (by
      rw [@IsHomLift.fac _ _ _ _ F _ _ _ _ a.hom g hg]
      simp [source, fiberToStructured, p₁, q₁])
  obtain ⟨x₂, x₃, g', hg'⟩ := hmap b.hom
  let p₂ : Functor.Fiber F y :=
    ⟨x₂, @IsHomLift.domain_eq _ _ _ _ F _ _ _ _ b.hom g' hg'⟩
  let q₂ : Functor.Fiber F (F.obj b.right) :=
    ⟨x₃, @IsHomLift.codomain_eq _ _ _ _ F _ _ _ _ b.hom g' hg'⟩
  let r₂ : Functor.Fiber F (F.obj b.right) := ⟨b.right, rfl⟩
  have h₂ : (fiberToStructured y (F.obj b.right) b.hom).obj r₂ = b := by
    calc
      (fiberToStructured y (F.obj b.right) b.hom).obj r₂ =
          StructuredArrow.mk b.hom := by simp [fiberToStructured, r₂]
      _ = b := (StructuredArrow.eq_mk b).symm
  have hz₂ :
    Zigzag ((fiberToStructured y (F.obj b.right) b.hom).obj q₂) b :=
    (zigzag_obj_of_zigzag (fiberToStructured y (F.obj b.right) b.hom)
      (@isPreconnected_zigzag _ _ (hF (F.obj b.right)).toIsPreconnected q₂ r₂)).trans
        (by rw [h₂])
  have hg₂ :
      (source.obj p₂ ⟶
        (fiberToStructured y (F.obj b.right) b.hom).obj q₂) := by
    exact StructuredArrow.homMk g' (by
      rw [@IsHomLift.fac _ _ _ _ F _ _ _ _ b.hom g' hg']
      simp [source, fiberToStructured, p₂, q₂])
  exact hz₁.symm.trans (Zigzag.of_inv hg₁) |>.trans
    ((zigzag_obj_of_zigzag source
      (@isPreconnected_zigzag _ _ (hF y).toIsPreconnected p₁ p₂)).trans
      ((Zigzag.of_hom hg₂).trans hz₂))

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
    (hmap : LiftsMorphisms F) (M : J ⥤ C) [HasColimit M] :
    letI : Functor.Final F := isCofinal_of_connected_fibers F hF hmap
    colimit (F ⋙ M) ≅ colimit M := by
  letI : Functor.Final F := isCofinal_of_connected_fibers F hF hmap
  exact
    Functor.Final.colimitIso F M

/-- The same comparison when the restricted diagram's colimit is given. -/
noncomputable def colimit_comp_iso_of_connected_fibers_of_comp
    {I J C : Type*} [Category I] [Category J] [Category C]
    (F : I ⥤ J)
    (hF : ∀ y : J, IsConnected (Functor.Fiber F y))
    (hmap : LiftsMorphisms F) (M : J ⥤ C) [HasColimit (F ⋙ M)] :
    letI : Functor.Final F := isCofinal_of_connected_fibers F hF hmap
    letI : HasColimit M := Functor.Final.hasColimit_of_comp F
    colimit (F ⋙ M) ≅ colimit M := by
  letI : Functor.Final F := isCofinal_of_connected_fibers F hF hmap
  letI : HasColimit M := Functor.Final.hasColimit_of_comp F
  exact Functor.Final.colimitIso F M

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

/-- The same comparison when the product diagram's colimit is given. -/
noncomputable def colimit_prod_snd_iso_of_comp
    {I J C : Type*} [Category I] [Category J] [Category C]
    [IsConnected I] (M : J ⥤ C)
    [HasColimit ((CategoryTheory.Prod.snd I J) ⋙ M)] :
    letI : HasColimit M :=
      Functor.Final.hasColimit_of_comp (CategoryTheory.Prod.snd I J)
    colimit ((CategoryTheory.Prod.snd I J) ⋙ M) ≅ colimit M := by
  letI : HasColimit M :=
    Functor.Final.hasColimit_of_comp (CategoryTheory.Prod.snd I J)
  exact Functor.Final.colimitIso (CategoryTheory.Prod.snd I J) M

end

end Formalization.Books.Categories.Unit17
