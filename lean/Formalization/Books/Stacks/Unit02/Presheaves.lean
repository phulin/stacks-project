import Formalization.Books.Stacks.Unit01.Setoids

/-!
# Stacks, Chapter 2: presheaves of morphisms associated to fibred categories

The canonical implementation of the source construction is already provided
by Mathlib's `Pseudofunctor.presheafHom` API and exposed by the preceding
Stacks interfaces as `MorphismPresheaf` and `IsomorphismPresheaf`.  This file
keeps that implementation and records the source-facing formulas and
statements in the chapter namespace.  In particular, it does not introduce a
second pullback convention or a second definition of the morphism presheaf.

The explicit `\alpha_{g,f}` terms in the source are the coherence isomorphisms
used by `Pseudofunctor.presheafHom`; its `pullHom` identity and composition
lemmas are the presheaf verification.  The source's final 2-fibre-product
claim is represented below by a presentation with the explicit fibre objects
and the canonical object-isomorphism-class presheaf.
-/

namespace Formalization.Books.Stacks.Unit02

open CategoryTheory
open Opposite
open Formalization.Books.Stacks.Unit01

universe w v u

/-! ## The morphism and isomorphism presheaves -/

@[simp]
theorem morphism_presheaf_obj
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U V : C} (x y : Fiber F U)
    (f : V ⟶ U) :
    (MorphismPresheaf F x y).obj (op (Over.mk f)) =
      ((F.map f.op.toLoc).toFunctor.obj x ⟶
        (F.map f.op.toLoc).toFunctor.obj y) := by
  rfl

@[simp]
theorem isomorphism_presheaf_obj
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U V : C} (x y : Fiber F U)
    (f : V ⟶ U) :
    (IsomorphismPresheaf F x y).obj (op (Over.mk f)) =
      { φ : (MorphismPresheaf F x y).obj (op (Over.mk f)) // IsIso φ } := by
  rfl

/- The assertion that the restriction construction is a presheaf is already
   the functor equality supplied by the canonical implementation. -/
theorem mor_presheaf_is_presheaf
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) :
    MorphismPresheaf F x y = F.presheafHom x y :=
  Formalization.Books.Stacks.Unit01.mor_presheaf_is_presheaf F x y

@[simp]
theorem morphism_presheaf_map_id
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U)
    (T : (Over C U)ᵒᵖ) (φ : (MorphismPresheaf F x y).obj T) :
    (MorphismPresheaf F x y).map (𝟙 T) φ = φ := by
  simp

theorem morphism_presheaf_map_comp
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U)
    {T₀ T₁ T₂ : (Over C U)ᵒᵖ}
    (q₀₁ : T₀ ⟶ T₁) (q₁₂ : T₁ ⟶ T₂)
    (φ : (MorphismPresheaf F x y).obj T₀) :
    (MorphismPresheaf F x y).map (q₀₁ ≫ q₁₂) φ =
      (MorphismPresheaf F x y).map q₁₂
        ((MorphismPresheaf F x y).map q₀₁ φ) := by
  simp

/- The objectwise subtype is the source's subpresheaf of isomorphisms. -/
theorem isomorphism_presheaf_is_subpresheaf
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U)
    (T : (Over C U)ᵒᵖ)
    (φ : (IsomorphismPresheaf F x y).obj T) :
    IsIso φ.1 :=
  Formalization.Books.Stacks.Unit01.isom_presheaf_is_subpresheaf F x y T φ

theorem isomorphism_presheaf_inclusion_app
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U)
    (T : (Over C U)ᵒᵖ)
    (φ : (IsomorphismPresheaf F x y).obj T) :
    (isomorphismPresheafInclusion F x y).app T φ = φ.1 :=
  Formalization.Books.Stacks.Unit01.isomorphism_presheaf_inclusion_app F x y T φ

/-! ## Maps induced by morphisms of fibred categories -/

/- The imported definition
`presheaf_mor_map_fibred_categories` is the canonical map.  Its component is
the source formula `β_V⁻¹ ≫ F(φ) ≫ α_V`, and the following statement records
the existence of that natural transformation in the chapter namespace. -/
theorem presheaf_mor_map_fibred_categories_exists
    {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) {U : C}
    (x y : Fiber F U) :
    Nonempty
      (F.presheafHom x y ⟶
        G.presheafHom ((η.app (.mk (op U))).toFunctor.obj x)
          ((η.app (.mk (op U))).toFunctor.obj y)) :=
  Formalization.Books.Stacks.Unit01.presheaf_mor_map_fibred_categories_exists η x y

theorem presheaf_mor_map_fibred_categories_is_induced
    {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) {U : C}
    (x y : Fiber F U) :
      IsInducedMorphismPresheafMap η x y
      (Formalization.Books.Stacks.Unit01.presheaf_mor_map_fibred_categories η x y) := by
  intro T f
  rfl

/-! ## Groupoids and the 2-fibre-product presentation -/

theorem isom_presheaf_is_morphism_presheaf_of_groupoid
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    (hF : FiberwiseGroupoid F) {U : C} (x y : Fiber F U) :
    Nonempty (IsomorphismPresheaf F x y ≅ MorphismPresheaf F x y) :=
  Formalization.Books.Stacks.Unit01.isom_presheaf_is_morphism_presheaf_of_groupoid
    hF x y

/-! The objects displayed in the proof of the source's 2-fibre-product lemma.
For `T : C/U`, these are an object over `T.left` together with the two
specified isomorphisms to the pullbacks of `x` and `y`. -/

structure TwoFiberProductObject
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U)
    (T : Over C U) where
  object : Fiber F T.left
  alpha : object ≅ (F.map T.hom.op.toLoc).toFunctor.obj x
  beta : object ≅ (F.map T.hom.op.toLoc).toFunctor.obj y

structure TwoFiberProductHom
    {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {U : C} {x y : Fiber F U}
    {T : Over C U} (A B : TwoFiberProductObject F x y T) where
  hom : A.object ⟶ B.object
  alpha_comm : hom ≫ B.alpha.hom = A.alpha.hom
  beta_comm : hom ≫ B.beta.hom = A.beta.hom

@[ext]
lemma TwoFiberProductHom.ext
    {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {U : C} {x y : Fiber F U}
    {T : Over C U} {A B : TwoFiberProductObject F x y T}
    {f g : TwoFiberProductHom A B} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance twoFiberProductObjectCategory
    {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {U : C} {x y : Fiber F U}
    (T : Over C U) : Category (TwoFiberProductObject F x y T) where
  Hom A B := TwoFiberProductHom A B
  id A :=
    { hom := 𝟙 A.object
      alpha_comm := by simp
      beta_comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      alpha_comm := by
        simp only [Category.assoc, g.alpha_comm, f.alpha_comm]
      beta_comm := by
        simp only [Category.assoc, g.beta_comm, f.beta_comm] }
  id_comp f := by
    apply TwoFiberProductHom.ext
    simp
  comp_id f := by
    apply TwoFiberProductHom.ext
    simp
  assoc f g h := by
    apply TwoFiberProductHom.ext
    simp [Category.assoc]

/-! This is the source-facing interface for the final lemma.  The
`objectClassPresheafIso` field uses the established quotient-by-isomorphism
construction from Chapter 1; `fibreEquivalence` prevents the apex from being
an arbitrary setoid-valued replacement and records the displayed objects in
the source proof. -/
structure TwoFiberProductPresentation
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) where
  apex : FiberedCategory (Over C U)
  isSetoid : FiberwiseSetoid apex
  objectClassPresheafIso : ObjectClassPresheaf apex ≅ IsomorphismPresheaf F x y
  fibreEquivalence : ∀ T : Over C U, Nonempty
    (apex.obj (.mk (op T)) ≌ TwoFiberProductObject F x y T)

theorem isom_as_two_fibre_product
    {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) :
    Nonempty (TwoFiberProductPresentation F x y) :=
  by
    let P := IsomorphismPresheaf F x y
    let Q : (Over C U)ᵒᵖ ⥤ Cat := {
      obj := fun T => Cat.of (Discrete (P.obj T))
      map := fun {T₁ T₂} f =>
        (Discrete.functor (fun z => Discrete.mk (P.map f z))).toCatHom
      map_id := fun T => by
        apply Cat.Hom.ext
        apply Discrete.functor_ext
        intro Z
        have hZ : P.map (𝟙 T) Z = Z :=
          congrArg (fun h : P.obj T ⟶ P.obj T => h Z) (P.map_id T)
        exact congrArg Discrete.mk hZ
      map_comp := fun {T₀ T₁ T₂} f g => by
        apply Cat.Hom.ext
        refine CategoryTheory.Functor.ext ?_ ?_
        · intro Z
          have hZ : P.map (f ≫ g) Z.as = P.map g (P.map f Z.as) :=
            congrArg (fun h : P.obj T₀ ⟶ P.obj T₂ => h Z.as) (P.map_comp f g)
          change Discrete.mk (P.map (f ≫ g) Z.as) =
            Discrete.mk (P.map g (P.map f Z.as))
          exact congrArg Discrete.mk hZ
        · intro Z Z' q
          rcases Z with ⟨Z⟩
          rcases Z' with ⟨Z'⟩
          rcases q with ⟨⟨h⟩⟩
          change Z = Z' at h
          subst Z'
          rfl }
    let A : FiberedCategory (Over C U) := Q.toPseudofunctor'
    have hclass : ObjectClassPresheaf A ≅ P := by
      refine NatIso.ofComponents (fun T => ?_) ?_
      · change Quotient (ObjectIsoSetoid (Discrete (P.obj T))) ≅ P.obj T
        refine
          { hom := ↾(@Quotient.lift _ _ (ObjectIsoSetoid (Discrete (P.obj T)))
              (fun z : Discrete (P.obj T) => z.as) ?_)
            inv := ↾(fun z => Quotient.mk (ObjectIsoSetoid (Discrete (P.obj T)))
              (Discrete.mk z))
            hom_inv_id := ?_
            inv_hom_id := ?_ }
        · intro a b hab
          rcases hab with ⟨e⟩
          exact Discrete.eq_of_hom e.hom
        · ext z
          refine Quotient.inductionOn z ?_
          intro z
          rfl
        · ext z
          rfl
      · intro T₁ T₂ q
        ext z
        refine Quotient.inductionOn z ?_
        intro z
        rfl
    refine ⟨{ apex := A, isSetoid := ?_, objectClassPresheafIso := hclass, fibreEquivalence := ?_ }⟩
    · constructor <;> intro T
      · change IsGroupoid (Discrete (P.obj (op T)))
        infer_instance
      · change ∀ (X Y : Discrete (P.obj (op T))), Subsingleton (X ⟶ Y)
        infer_instance
    · intro T
      change Nonempty
        (Discrete (P.obj (op T)) ≌ TwoFiberProductObject F x y T)
      let fwdObj : Discrete (P.obj (op T)) → TwoFiberProductObject F x y T :=
        fun a => by
          letI := a.as.2
          exact
            { object := (F.map T.hom.op.toLoc).toFunctor.obj x
              alpha := Iso.refl _
              beta := asIso a.as.1 }
      let fwdMap : ∀ {a b : Discrete (P.obj (op T))},
          (a ⟶ b) → (fwdObj a ⟶ fwdObj b) :=
        fun {a b} q => by
          rcases a with ⟨a⟩
          rcases b with ⟨b⟩
          rcases q with ⟨⟨h⟩⟩
          dsimp at h
          subst b
          exact 𝟙 _
      have hfwdMap : ∀ {a b : Discrete (P.obj (op T))} (q : a ⟶ b),
          (fwdMap q).hom = 𝟙 _ := by
        intro a b q
        rcases a with ⟨a⟩
        rcases b with ⟨b⟩
        rcases q with ⟨⟨h⟩⟩
        dsimp at h
        subst b
        rfl
      let fwd : Discrete (P.obj (op T)) ⥤ TwoFiberProductObject F x y T :=
        { obj := fwdObj
          map := fwdMap
          map_id := by
            intro a
            apply TwoFiberProductHom.ext
            change (fwdMap (𝟙 a)).hom = 𝟙 _
            rw [hfwdMap]
          map_comp := by
            intro a b c f g
            apply TwoFiberProductHom.ext
            change (fwdMap (f ≫ g)).hom = (fwdMap f).hom ≫ (fwdMap g).hom
            rw [hfwdMap, hfwdMap, hfwdMap]
            simp }
      let bwd : TwoFiberProductObject F x y T ⥤ Discrete (P.obj (op T)) :=
        { obj := fun A =>
            Discrete.mk
              (⟨A.alpha.inv ≫ A.beta.hom, by infer_instance⟩ : P.obj (op T))
          map := fun {A B} h => by
            apply Discrete.eqToHom
            apply Subtype.ext
            have hh : h.hom = A.alpha.hom ≫ B.alpha.inv := by
              apply (cancel_mono B.alpha.hom).1
              simp only [Category.assoc, h.alpha_comm]
              simp
            calc
              A.alpha.inv ≫ A.beta.hom =
                  A.alpha.inv ≫ (h.hom ≫ B.beta.hom) := by rw [h.beta_comm]
              _ = A.alpha.inv ≫
                    ((A.alpha.hom ≫ B.alpha.inv) ≫ B.beta.hom) := by rw [hh]
              _ = B.alpha.inv ≫ B.beta.hom := by simp [Category.assoc]
          map_id := by
            intro A
            apply Subsingleton.elim
          map_comp := by
            intro A B D f g
            apply Subsingleton.elim }
      let unitIso : 𝟭 (Discrete (P.obj (op T))) ≅ fwd ⋙ bwd :=
        NatIso.ofComponents (fun a => by
          apply Discrete.eqToIso
          apply Subtype.ext
          change a.as.1 = (fwdObj a).alpha.inv ≫ (fwdObj a).beta.hom
          dsimp [fwdObj]
          simp) (by
            intro A B h
            apply Subsingleton.elim)
      let counitIso : bwd ⋙ fwd ≅ 𝟭 (TwoFiberProductObject F x y T) :=
        NatIso.ofComponents (fun A => by
          letI : IsIso (A.alpha.inv ≫ A.beta.hom) := by infer_instance
          dsimp [fwd, fwdObj, bwd]
          refine
            { hom :=
                { hom := A.alpha.inv
                  alpha_comm := by simp
                  beta_comm := by simp only [asIso_hom] }
              inv :=
                { hom := A.alpha.hom
                  alpha_comm := by simp
                  beta_comm := by simp [Category.assoc] }
              hom_inv_id := by
                apply TwoFiberProductHom.ext
                change A.alpha.inv ≫ A.alpha.hom = 𝟙 _
                simp
              inv_hom_id := by
                apply TwoFiberProductHom.ext
                change A.alpha.hom ≫ A.alpha.inv = 𝟙 _
                simp }) (by
            intro A B h
            apply TwoFiberProductHom.ext
            dsimp [fwdObj]
            have hh : A.alpha.inv ≫ h.hom = B.alpha.inv := by
              apply (cancel_mono B.alpha.hom).1
              simp only [Category.assoc, h.alpha_comm]
              simp
            change (fwdMap (bwd.map h)).hom ≫ B.alpha.inv = A.alpha.inv ≫ h.hom
            rw [hfwdMap]
            dsimp [fwdObj]
            simpa only [Category.id_comp] using hh.symm)
      refine ⟨Equivalence.mk' fwd bwd unitIso counitIso ?_⟩
      intro a
      apply TwoFiberProductHom.ext
      dsimp [fwd, unitIso, counitIso, fwdObj, bwd]
      change (fwdMap (unitIso.hom.app a)).hom ≫
          𝟙 ((F.map T.hom.op.toLoc).toFunctor.obj x) =
        𝟙 ((F.map T.hom.op.toLoc).toFunctor.obj x)
      rw [hfwdMap]
      simp

/- The source's strict groupoid presentation remark is proof guidance: the
   preceding groupoid equivalence and the canonical induced presheaf map are
   already the relevant interfaces, so no second strictification is defined
   here.  The mathematical invariance assertion is recorded explicitly. -/
theorem equivalent_fibred_categories_preserve_morphism_presheaf
    {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (hη : FiberwiseEquivalence η) {U : C} (x y : Fiber F U) :
    Nonempty
      (MorphismPresheaf F x y ≅
        MorphismPresheaf G
          ((η.app (.mk (op U))).toFunctor.obj x)
          ((η.app (.mk (op U))).toFunctor.obj y)) := by
  let φ := presheaf_mor_map_fibred_categories η x y
  refine ⟨NatIso.ofComponents (fun T => ?_) ?_⟩
  · let e :
        (MorphismPresheaf F x y).obj T ≃
          (MorphismPresheaf G
            ((η.app (.mk (op U))).toFunctor.obj x)
            ((η.app (.mk (op U))).toFunctor.obj y)).obj T :=
      by
        let hff := Classical.choice (hη.1 T.unop.left)
        exact Equiv.mk (φ.app T)
          (fun g => by
            simpa [Pseudofunctor.presheafHom] using
              hff.preimage
                ((η.naturality T.unop.hom.op.toLoc).hom.toNatTrans.app x ≫
                  g ≫
                  (η.naturality T.unop.hom.op.toLoc).inv.toNatTrans.app y))
          (by
            intro f
            apply hff.map_injective
            simp only [hff.map_preimage]
            rw [presheaf_mor_map_fibred_categories_is_induced η x y T f]
            simp)
          (by
            intro g
            rw [presheaf_mor_map_fibred_categories_is_induced η x y T]
            simp)
    exact Equiv.toIso e
  · intro T₁ T₂ q
    exact φ.naturality q

end Formalization.Books.Stacks.Unit02
