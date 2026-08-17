import Formalization.Books.Sites.Unit05.Functoriality
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Sites and Sheaves, Chapter 19: More functoriality of presheaves

For a functor `u : C ⥤ D`, this file adds the right adjoint of restriction of
presheaves.  The source suppresses size hypotheses; the declarations below
record the needed existence of the corresponding Kan extensions explicitly.
The category written `_V^u I` in the source is Mathlib's
`CostructuredArrow u V`, while the category used for the pointwise right Kan
extension is its canonical opposite structured-arrow equivalent.
-/

namespace Formalization.Books.Sites.Unit19

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Sites.Unit02
open Formalization.Books.Sites.Unit05
open Opposite

universe u u' v v' w w'

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v} D]

/-! ## The right-hand index categories -/

/- The source's category `_V^u I` is the costructured-arrow category. -/
abbrev rightIndexCategory (u : C ⥤ D) (V : D) :=
  CostructuredArrow u V

/-- The object `(U, ψ : u.obj U ⟶ V)` of `_V^u I`. -/
def rightIndexObject (u : C ⥤ D) (V : D) (U : C) (ψ : u.obj U ⟶ V) :
    rightIndexCategory u V :=
  CostructuredArrow.mk ψ

/-- The defining equation for a morphism in `_V^u I`. -/
theorem rightIndexMorphism_condition (u : C ⥤ D) (V : D)
    {X Y : rightIndexCategory u V} (β : X ⟶ Y) :
    u.map β.left ≫ Y.hom = X.hom :=
  CostructuredArrow.w β

/- A morphism `g : V' ⟶ V` gives `_V' I ⥤ _V I` by postcomposition. -/
def rightIndexRestriction {V' V : D} (u : C ⥤ D) (g : V' ⟶ V) :
    rightIndexCategory u V' ⥤ rightIndexCategory u V :=
  CostructuredArrow.map g

@[simp]
theorem rightIndexRestriction_obj {V' V : D} (u : C ⥤ D) (g : V' ⟶ V)
    (U : C) (ψ : u.obj U ⟶ V') :
    (rightIndexRestriction u g).obj (rightIndexObject u V' U ψ) =
      rightIndexObject u V U (ψ ≫ g) :=
  rfl

@[simp]
theorem rightIndexRestriction_id (u : C ⥤ D) (V : D) :
    rightIndexRestriction u (𝟙 V) = 𝟭 (rightIndexCategory u V) := by
  exact CategoryTheory.Functor.ext_of_iso (Comma.mapRightId _ _)
    (by intro X; simp [rightIndexRestriction])

theorem rightIndexRestriction_comp {V₀ V₁ V₂ : D} (u : C ⥤ D)
    (g : V₀ ⟶ V₁) (h : V₁ ⟶ V₂) :
    rightIndexRestriction u (g ≫ h) =
      rightIndexRestriction u g ⋙ rightIndexRestriction u h := by
  let e : rightIndexRestriction u (g ≫ h) ≅
      rightIndexRestriction u g ⋙ rightIndexRestriction u h :=
    NatIso.ofComponents
      (fun X => CostructuredArrow.isoMk (Iso.refl X.left) (by
        dsimp [rightIndexRestriction, CostructuredArrow.map, Comma.mapRight]
        change u.map (𝟙 X.left) ≫ ((X.hom ≫ g) ≫ h) =
          X.hom ≫ (g ≫ h)
        simp [Category.assoc]))
      (by
        intro X Y k
        apply CostructuredArrow.hom_ext
        simp [CostructuredArrow.isoMk, rightIndexRestriction,
          CostructuredArrow.map, Comma.mapRight])
  let hobj : ∀ X : rightIndexCategory u V₀,
      (rightIndexRestriction u (g ≫ h)).obj X =
        (rightIndexRestriction u g ⋙ rightIndexRestriction u h).obj X := by
    intro X
    exact CostructuredArrow.map_comp
  refine CategoryTheory.Functor.ext_of_iso e hobj (happ := fun X => ?_)
  apply CostructuredArrow.ext
  change (e.hom.app X).left = (eqToHom (hobj X)).left
  rw [CostructuredArrow.eqToHom_left]
  dsimp [e, NatIso.ofComponents, CostructuredArrow.isoMk, Comma.isoMk]
  have hleft :
      ((rightIndexRestriction u (g ≫ h)).obj X).left =
        ((rightIndexRestriction u g ⋙ rightIndexRestriction u h).obj X).left := rfl
  change (𝟙 X.left) = eqToHom hleft
  have hh := eqToHom_heq_id_dom
    (((rightIndexRestriction u (g ≫ h)).obj X).left)
    (((rightIndexRestriction u g ⋙ rightIndexRestriction u h).obj X).left) hleft
  exact (eq_of_heq hh).symm

/-! ## The diagrams and the right pushforward -/

/-- The source's functor `_V F : (_V^u I)ᵒᵖ ⥤ Type v`. -/
def rightIndexPresheaf (u : C ⥤ D) (F : Presheaf C) (V : D) :
    (rightIndexCategory u V)ᵒᵖ ⥤ Type v :=
  (CostructuredArrow.proj u V).op ⋙ F

@[simp]
theorem rightIndexPresheaf_obj (u : C ⥤ D) (F : Presheaf C) (V : D)
    (X : rightIndexCategory u V) :
    (rightIndexPresheaf u F V).obj (op X) = F.obj (op X.left) :=
  rfl

/-- The diagrams for `_V F` are compatible with the index restriction maps. -/
theorem rightIndexPresheaf_restrict {V' V : D} (u : C ⥤ D) (F : Presheaf C)
    (g : V' ⟶ V) :
    (rightIndexRestriction u g).op ⋙ rightIndexPresheaf u F V =
      rightIndexPresheaf u F V' := by
  rfl

/-- The structured-arrow index used by Mathlib's pointwise right Kan extension. -/
abbrev rightKanIndexCategory (u : C ⥤ D) (V : D) :=
  StructuredArrow (op V) u.op

/-- The canonical pointwise right Kan extension diagram at `op V`. -/
abbrev rightKanIndexDiagram (u : C ⥤ D) (F : Presheaf C) (V : D) :=
  StructuredArrow.proj (op V) u.op ⋙ F

/-- The canonical equivalence between the source index and the Kan index. -/
def rightIndexEquivalence (u : C ⥤ D) (V : D) :
    (rightIndexCategory u V)ᵒᵖ ≌ rightKanIndexCategory u V :=
  costructuredArrowOpEquivalence u V

/-- Under the canonical equivalence, the source diagram is the Kan diagram. -/
theorem rightIndexPresheaf_under_equivalence (u : C ⥤ D) (F : Presheaf C)
    (V : D) :
    (rightIndexEquivalence u V).functor ⋙ rightKanIndexDiagram u F V =
      rightIndexPresheaf u F V := by
  rfl

/- The source suppresses the size conditions ensuring these right Kan
   extensions.  They are explicit here, as in the preceding chapter's left
   pushforward API. -/
abbrev HasRightPushforward (u : C ⥤ D) :=
  ∀ F : Presheaf C, Functor.HasRightKanExtension u.op F

abbrev HasPointwiseRightPushforward (u : C ⥤ D) :=
  ∀ F : Presheaf C, Functor.HasPointwiseRightKanExtension u.op F

theorem hasRightPushforward_of_pointwise (u : C ⥤ D)
    [HasPointwiseRightPushforward u] :
    HasRightPushforward u :=
  fun _F => inferInstance

/-- The right pushforward `{}_p u`, implemented by Mathlib's right Kan functor. -/
noncomputable def rightPushforwardPresheafFunctor (u : C ⥤ D)
    [HasRightPushforward u] : PSh C ⥤ PSh D :=
  Functor.ran u.op

/-- The right pushforward of an individual presheaf. -/
noncomputable def rightPushforwardPresheaf (u : C ⥤ D) (F : Presheaf C)
    [HasRightPushforward u] : Presheaf D :=
  (rightPushforwardPresheafFunctor u).obj F

/-- The pointwise limit formula for the value of the right pushforward. -/
noncomputable def rightPushforwardValueLimitIso (u : C ⥤ D) (F : Presheaf C)
    (V : D) [hRight : HasRightPushforward u]
    [hPoint : HasPointwiseRightPushforward u] :
    (rightPushforwardPresheaf u F).obj (op V) ≅
      limit (rightKanIndexDiagram u F V) := by
  letI : Functor.HasRightKanExtension u.op F := hRight F
  letI : Functor.HasPointwiseRightKanExtension u.op F := hPoint F
  simpa [rightPushforwardPresheaf, rightPushforwardPresheafFunctor] using
    (Functor.ranObjObjIsoLimit u.op F (op V))

/-! ## Projections and compatible collections -/

/-- The projection `c(ψ)` from the pointwise limit description. -/
noncomputable def rightPushforwardProjection (u : C ⥤ D) (F : Presheaf C)
    (V : D) (U : C) (ψ : u.obj U ⟶ V)
    [HasRightPushforward u] [HasPointwiseRightPushforward u] :
    (rightPushforwardPresheaf u F).obj (op V) ⟶ F.obj (op U) :=
  (rightPushforwardValueLimitIso u F V).hom ≫
    limit.π (rightKanIndexDiagram u F V) (StructuredArrow.mk ψ.op)

/-- The type of compatible collections displayed in the source. -/
def rightPushforwardCompatibleFamily (u : C ⥤ D) (F : Presheaf C) (V : D) :
    Type (max u v) :=
  {s : ∀ X : rightIndexCategory u V, F.obj (op X.left) //
    ∀ {X Y : rightIndexCategory u V} (β : X ⟶ Y),
      F.map β.left.op (s Y) = s X}

/-- The projections produce a compatible collection. -/
theorem rightPushforwardProjection_compatible (u : C ⥤ D) (F : Presheaf C)
    (V : D) [HasRightPushforward u] [HasPointwiseRightPushforward u]
    (s : (rightPushforwardPresheaf u F).obj (op V))
    {X Y : rightIndexCategory u V} (β : X ⟶ Y) :
    F.map β.left.op
        (rightPushforwardProjection u F V Y.left Y.hom s) =
      rightPushforwardProjection u F V X.left X.hom s := by
  let Y' : rightKanIndexCategory u V :=
    StructuredArrow.mk (Y := op Y.left) Y.hom.op
  let X' : rightKanIndexCategory u V :=
    StructuredArrow.mk (Y := op X.left) X.hom.op
  let β' : Y' ⟶ X' := StructuredArrow.homMk β.left.op (by
    change Y.hom.op ≫ (u.map β.left).op = X.hom.op
    exact congrArg Quiver.Hom.op (rightIndexMorphism_condition u V β))
  have hπ := (limit.cone (rightKanIndexDiagram u F V)).π.naturality β'
  simp [Functor.const_obj_map] at hπ
  have hπ' := congrArg
    (fun k => (rightPushforwardValueLimitIso u F V).hom ≫ k) hπ
  convert (ConcreteCategory.congr_hom hπ'.symm s) using 1
  · rfl
  · simp only [rightPushforwardProjection, rightKanIndexDiagram, β', X', Y']
    exact heq_of_eq (congrArg (ConcreteCategory.hom (F.map β.left.op))
      (ConcreteCategory.comp_apply (rightPushforwardValueLimitIso u F V).hom
        (limit.π (rightKanIndexDiagram u F V) Y') s))
  · change ((rightPushforwardValueLimitIso u F V).hom ≫
        limit.π (rightKanIndexDiagram u F V) X') s ≍
      (limit.π (rightKanIndexDiagram u F V) X')
        ((rightPushforwardValueLimitIso u F V).hom s)
    exact heq_of_eq (ConcreteCategory.comp_apply _ _ _)

/- The following map is the source's correspondence
   `s ↦ (c(ψ)(s))_(U,ψ)`. -/
noncomputable def rightPushforwardProjectionFamily (u : C ⥤ D) (F : Presheaf C) (V : D)
    [HasRightPushforward u] [HasPointwiseRightPushforward u]
    (s : (rightPushforwardPresheaf u F).obj (op V)) :
    ∀ X : rightIndexCategory u V, F.obj (op X.left) :=
  fun X => rightPushforwardProjection u F V X.left X.hom s

theorem rightPushforwardProjectionFamily_compatible (u : C ⥤ D)
    (F : Presheaf C) (V : D) [HasRightPushforward u]
    [HasPointwiseRightPushforward u]
    (s : (rightPushforwardPresheaf u F).obj (op V)) :
    ∀ {X Y : rightIndexCategory u V} (β : X ⟶ Y),
      F.map β.left.op
          (rightPushforwardProjectionFamily u F V s Y) =
        rightPushforwardProjectionFamily u F V s X := by
  intro X Y β
  exact rightPushforwardProjection_compatible u F V s β

/- The map is made into the subtype of compatible families using the
   preceding compatibility theorem; the underlying construction is real. -/
noncomputable def rightPushforwardProjectionFamilyMap (u : C ⥤ D)
    (F : Presheaf C) (V : D) [HasRightPushforward u]
    [HasPointwiseRightPushforward u] :
    (rightPushforwardPresheaf u F).obj (op V) →
      rightPushforwardCompatibleFamily u F V :=
  fun s => ⟨rightPushforwardProjectionFamily u F V s,
    rightPushforwardProjectionFamily_compatible u F V s⟩

theorem rightPushforwardProjectionFamilyMap_bijective (u : C ⥤ D)
    (F : Presheaf C) (V : D) [HasRightPushforward u]
    [HasPointwiseRightPushforward u] :
    Function.Bijective (rightPushforwardProjectionFamilyMap u F V) := by
  let eSec :=
    Types.isLimitEquivSections (limit.isLimit (rightKanIndexDiagram u F V))
  let eFam :
      (rightKanIndexDiagram u F V).sections ≃
        rightPushforwardCompatibleFamily u F V :=
    { toFun := fun s =>
        ⟨fun X => s.1 (StructuredArrow.mk (Y := op X.left) X.hom.op), by
          intro X Y β
          let X' : rightKanIndexCategory u V :=
            StructuredArrow.mk (Y := op X.left) X.hom.op
          let Y' : rightKanIndexCategory u V :=
            StructuredArrow.mk (Y := op Y.left) Y.hom.op
          let β' : Y' ⟶ X' := StructuredArrow.homMk β.left.op (by
            change Y.hom.op ≫ (u.map β.left).op = X.hom.op
            exact congrArg Quiver.Hom.op (rightIndexMorphism_condition u V β))
          change F.map β'.right (s.1 Y') = s.1 X'
          exact s.2 β'
      ⟩
      invFun := fun t =>
        ⟨fun Q => t.1 (((rightIndexEquivalence u V).inverse.obj Q).unop), by
          intro Q R β
          let A_Q : rightIndexCategory u V :=
            ((rightIndexEquivalence u V).inverse.obj Q).unop
          let A_R : rightIndexCategory u V :=
            ((rightIndexEquivalence u V).inverse.obj R).unop
          let β' : A_R ⟶ A_Q :=
            ((rightIndexEquivalence u V).inverse.map β).unop
          change F.map β'.left.op (t.1 A_Q) = t.1 A_R
          exact t.2 β'
      ⟩
      left_inv := by
        intro s
        apply Subtype.ext
        funext Q
        rfl
      right_inv := by
        intro t
        apply Subtype.ext
        funext X
        rfl }
  let e :
      (rightPushforwardPresheaf u F).obj (op V) ≃
        rightPushforwardCompatibleFamily u F V :=
    (Iso.toEquiv (rightPushforwardValueLimitIso u F V)).trans
      (eSec.trans eFam)
  have hmap :
      rightPushforwardProjectionFamilyMap u F V = e := by
    funext s
    apply Subtype.ext
    funext X
    rfl
  rw [hmap]
  exact ⟨e.injective, e.surjective⟩

/-- The limit value is canonically the set of compatible collections. -/
noncomputable def rightPushforwardValue_compatibleFamily_equiv (u : C ⥤ D)
    (F : Presheaf C) (V : D) [HasRightPushforward u]
    [HasPointwiseRightPushforward u] :
    (rightPushforwardPresheaf u F).obj (op V) ≃
      rightPushforwardCompatibleFamily u F V :=
  Equiv.ofBijective (rightPushforwardProjectionFamilyMap u F V)
    (rightPushforwardProjectionFamilyMap_bijective u F V)

/-! ## Restriction maps, recovery, and functoriality in `F` -/

/-- The restriction map associated to `g : V' ⟶ V`. -/
noncomputable def rightPushforwardRestrictionMap (u : C ⥤ D) (F : Presheaf C)
    {V' V : D} (g : V' ⟶ V) [HasRightPushforward u] :
    (rightPushforwardPresheaf u F).obj (op V) ⟶
      (rightPushforwardPresheaf u F).obj (op V') :=
  (rightPushforwardPresheaf u F).map g.op

@[simp]
theorem rightPushforwardRestrictionMap_id (u : C ⥤ D) (F : Presheaf C)
    (V : D) [HasRightPushforward u] :
    rightPushforwardRestrictionMap u F (𝟙 V) = 𝟙 _ := by
  simp [rightPushforwardRestrictionMap]

theorem rightPushforwardRestrictionMap_comp (u : C ⥤ D) (F : Presheaf C)
    {V₀ V₁ V₂ : D} (g : V₀ ⟶ V₁) (h : V₁ ⟶ V₂)
    [HasRightPushforward u] :
    rightPushforwardRestrictionMap u F h ≫
        rightPushforwardRestrictionMap u F g =
      rightPushforwardRestrictionMap u F (g ≫ h) := by
  simp [rightPushforwardRestrictionMap]

/-- The canonical recovery map `{}_p u(F)(u(U)) ⟶ F(U)`. -/
noncomputable def rightPushforwardRecoverMap (u : C ⥤ D) (F : Presheaf C)
    (U : C) [HasRightPushforward u] :
    (rightPushforwardPresheaf u F).obj (op (u.obj U)) ⟶ F.obj (op U) :=
  ((Functor.ranCounit u.op).app F).app (op U)

/-- The recovery map is the projection at the identity arrow. -/
theorem rightPushforwardRecoverMap_eq_projection (u : C ⥤ D) (F : Presheaf C)
    (U : C) [HasRightPushforward u] [HasPointwiseRightPushforward u] :
    rightPushforwardRecoverMap u F U =
      rightPushforwardProjection u F (u.obj U) U (𝟙 (u.obj U)) := by
  change ((Functor.ranCounit u.op).app F).app (op U) =
    (rightPushforwardValueLimitIso u F (u.obj U)).hom ≫
      limit.π (rightKanIndexDiagram u F (u.obj U))
        (StructuredArrow.mk (𝟙 (u.obj U)).op)
  let : Functor.HasPointwiseRightKanExtension u.op F :=
    (inferInstance : HasPointwiseRightPushforward u) F
  simp [rightPushforwardValueLimitIso, rightPushforwardPresheaf,
    rightPushforwardPresheafFunctor]

/-- Recovery maps commute with restriction in the source presheaf. -/
theorem rightPushforwardRecoverMap_naturality (u : C ⥤ D) (F : Presheaf C)
    {U V : C} (f : V ⟶ U) [HasRightPushforward u] :
    rightPushforwardRestrictionMap u F (u.map f) ≫
        rightPushforwardRecoverMap u F V =
      rightPushforwardRecoverMap u F U ≫ F.map f.op := by
  exact ((Functor.ranCounit u.op).app F).naturality f.op

/-- A map of presheaves is sent to the corresponding map of right pushforwards. -/
noncomputable def rightPushforwardPresheafMap (u : C ⥤ D)
    {F F' : Presheaf C} (η : F ⟶ F') [HasRightPushforward u] :
    rightPushforwardPresheaf u F ⟶ rightPushforwardPresheaf u F' :=
  (rightPushforwardPresheafFunctor u).map η

/-! ## The right adjoint -/

/-- The adjunction `u^p ⊣ {}_p u`. -/
noncomputable def pullbackRightPushforwardAdjunction (u : C ⥤ D)
    [HasRightPushforward u] :
    pullbackPresheafFunctor u ⊣ rightPushforwardPresheafFunctor u := by
  simpa [pullbackPresheafFunctor, rightPushforwardPresheafFunctor] using
    (Functor.ranAdjunction u.op (Type v))

/-- The hom-set equivalence expressing `u^p ⊣ {}_p u`. -/
noncomputable def pullbackRightPushforwardHomEquiv (u : C ⥤ D)
    (G : Presheaf D) (F : Presheaf C) [HasRightPushforward u] :
    (pullbackPresheaf u G ⟶ F) ≃
      (G ⟶ rightPushforwardPresheaf u F) :=
  (pullbackRightPushforwardAdjunction u).homEquiv G F

/- The restriction functors induced by an adjunction are themselves adjoint;
   this is Mathlib's opposite-adjunction plus whiskering construction. -/
noncomputable def pullbackAdjunctionOfAdjunction
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v) :
    pullbackPresheafFunctor u ⊣ pullbackPresheafFunctor v := by
  simpa [pullbackPresheafFunctor] using h.op.whiskerLeft (Type v)

/-! ## The five assertions for an adjoint pair -/

/-- The representable formula `u^p h_V ≅ h_{v(V)}`. -/
noncomputable def pullbackRepresentableIsoOfAdjunction
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v) (V : D) :
    pullbackPresheaf u (representablePresheaf V) ≅
      representablePresheaf (v.obj V) := by
  simpa [pullbackPresheaf, pullbackPresheafFunctor, representablePresheaf] using
    (h.compYonedaIso.app V).symm

/-- The initial object of `I^v_U` supplied by the unit of `u ⊣ v`. -/
def adjunctionIndexInitialObject {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v)
    (U : C) : indexCategory v U :=
  StructuredArrow.mk (h.unit.app U)

theorem adjunctionIndexInitialObject_isInitial
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v) (U : C) :
    Nonempty (IsInitial (adjunctionIndexInitialObject h U)) := by
  refine ⟨IsInitial.ofUniqueHom (fun X =>
    StructuredArrow.homMk ((h.homEquiv U X.right).symm X.hom) (by
      change h.unit.app U ≫ v.map ((h.homEquiv U X.right).symm X.hom) = X.hom
      calc
        h.unit.app U ≫ v.map ((h.homEquiv U X.right).symm X.hom) =
            (h.homEquiv U X.right) ((h.homEquiv U X.right).symm X.hom) :=
          (h.homEquiv_unit U X.right
            ((h.homEquiv U X.right).symm X.hom)).symm
        _ = X.hom := (h.homEquiv U X.right).apply_symm_apply X.hom)) ?_⟩
  intro X f
  apply StructuredArrow.hom_ext
  change f.right = (h.homEquiv U X.right).symm X.hom
  apply (h.homEquiv U X.right).injective
  calc
    (h.homEquiv U X.right) f.right =
        h.unit.app U ≫ v.map f.right :=
      h.homEquiv_unit U X.right f.right
    _ = X.hom := by simpa [adjunctionIndexInitialObject] using f.w
    _ = (h.homEquiv U X.right) ((h.homEquiv U X.right).symm X.hom) := by simp

/-- The final object of `_V^u I` supplied by the counit of `u ⊣ v`. -/
def adjunctionRightIndexFinalObject {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v)
    (V : D) : rightIndexCategory u V :=
  CostructuredArrow.mk (h.counit.app V)

theorem adjunctionRightIndexFinalObject_isTerminal
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v) (V : D) :
    Nonempty (IsTerminal (adjunctionRightIndexFinalObject h V)) := by
  refine ⟨IsTerminal.ofUniqueHom (fun X =>
    CostructuredArrow.homMk (h.homEquiv X.left V X.hom) (by
      change u.map (h.homEquiv X.left V X.hom) ≫ h.counit.app V = X.hom
      exact (h.homEquiv_counit X.left V
        (h.homEquiv X.left V X.hom)).symm.trans
        ((h.homEquiv X.left V).symm_apply_apply X.hom))) ?_⟩
  intro X f
  apply CostructuredArrow.hom_ext
  change f.left = h.homEquiv X.left V X.hom
  apply (h.homEquiv X.left V).symm.injective
  calc
    (h.homEquiv X.left V).symm f.left =
        u.map f.left ≫ h.counit.app V :=
      h.homEquiv_counit X.left V f.left
    _ = X.hom := by simpa [adjunctionRightIndexFinalObject] using f.w
    _ = (h.homEquiv X.left V).symm (h.homEquiv X.left V X.hom) := by simp

/-- The right pushforward is canonically the restriction along `v`. -/
noncomputable def rightPushforwardIsoPullbackOfAdjunction
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v) [HasRightPushforward u] :
    rightPushforwardPresheafFunctor u ≅ pullbackPresheafFunctor v :=
  Adjunction.rightAdjointUniq (pullbackRightPushforwardAdjunction u)
    (pullbackAdjunctionOfAdjunction h)

/-- The restriction along `u` is canonically the left pushforward along `v`. -/
noncomputable def pullbackIsoPushforwardOfAdjunction
    {u : C ⥤ D} {v : D ⥤ C} (h : u ⊣ v) [HasLeftPushforward v] :
    pullbackPresheafFunctor u ≅ pushforwardPresheafFunctor v :=
  Adjunction.leftAdjointUniq (pullbackAdjunctionOfAdjunction h)
    (pushforwardPullbackAdjunction v)

end Formalization.Books.Sites.Unit19
