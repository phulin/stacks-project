import Formalization.Books.Homology.Unit29.AdjointFunctors
import Formalization.Books.MoreAlgebra.Unit55.InjectiveModules
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Ring.ULift
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Injectives, Chapter 6: Abelian presheaves on a category

An abelian presheaf is modeled by a functor to a universe-lifted copy of
`ModuleCat ℤ`.  This is
equivalent to the usual category of abelian-group-valued presheaves, while
retaining the canonical abelian and injective-object APIs used in the earlier
chapters.  Restriction along the discrete-object inclusion is precomposition;
the functor called `u` in the source is its right Kan extension.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit27
open Formalization.Books.Homology.Unit29
open Formalization.Books.MoreAlgebra.Unit55

universe u v w

namespace Formalization.Books.Injectives.Unit06

/-! ## Abelian presheaves and restriction to objects -/

/-- The category of objects of `C`, regarded as a discrete category. -/
abbrev objectCategory (C : Type u) [Category.{v} C] := Discrete C

/-- A universe-lifted copy of `ℤ`, used so the explicit injective-envelope
construction is available at the universe of the presheaf values. -/
abbrev abelianScalar (C : Type u) [Category.{v} C] := ULift.{max u v} ℤ

/-- The inclusion of the discrete category of objects into `C`. -/
def objectInclusion {C : Type u} [Category.{v} C] : objectCategory C ⥤ C :=
  Discrete.functor (fun X : C => X)

/-- Abelian presheaves on `C`, represented by abelian groups as ℤ-modules. -/
abbrev AbelianPresheaf (C : Type u) [Category.{v} C] :=
  Cᵒᵖ ⥤ ModuleCat.{max u v} (abelianScalar C)

/-- Abelian presheaves on the discrete category of objects of `C`. -/
abbrev ObjectAbelianPresheaf (C : Type u) [Category.{v} C] :=
  (objectCategory C)ᵒᵖ ⥤ ModuleCat.{max u v} (abelianScalar C)

/-- Restriction of an abelian presheaf to the objects of the category. -/
noncomputable def presheafRestriction {C : Type u} [Category.{v} C] :
    AbelianPresheaf C ⥤ ObjectAbelianPresheaf C :=
  (Functor.whiskeringLeft ((objectCategory C)ᵒᵖ) Cᵒᵖ
      (ModuleCat.{max u v} (abelianScalar C))).obj
    (objectInclusion (C := C)).op

/-! ## The product formula for `u` -/

/-- The indexing type of all arrows with fixed target `U`. -/
abbrev incomingMorphismIndex {C : Type u} [Category.{v} C] (U : C) :=
  Σ X : C, X ⟶ U

/-- The product appearing in the source's explicit formula for `u A U`. -/
noncomputable def incomingProduct {C : Type u} [Category.{v} C]
    (A : ObjectAbelianPresheaf C) (U : C) :
      ModuleCat.{max u v} (abelianScalar C) :=
  ∏ᶜ fun p : incomingMorphismIndex U =>
    A.obj (Opposite.op (Discrete.mk p.1))

/-! ## The right adjoint `u` -/

/-- The source's functor `u`, defined canonically as a right Kan extension. -/
noncomputable def presheafRightKanExtension {C : Type u} [Category.{v} C] :
    ObjectAbelianPresheaf C ⥤ AbelianPresheaf C :=
  (objectInclusion (C := C)).op.ran

/-- The adjunction `v ⊣ u` from the source. -/
noncomputable def presheafRestrictionAdjunction {C : Type u} [Category.{v} C] :
    presheafRestriction (C := C) ⊣ presheafRightKanExtension (C := C) := by
  simpa [presheafRestriction, presheafRightKanExtension] using
    ((objectInclusion (C := C)).op.ranAdjunction
      (ModuleCat.{max u v} (abelianScalar C)))

/-- The right Kan extension has the source's product description at every object. -/
theorem presheafRightKanExtension_obj_iso_incomingProduct
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C) (U : C) :
    Nonempty
      (((presheafRightKanExtension (C := C)).obj A).obj (Opposite.op U) ≅
        incomingProduct A U) := by
  let e : StructuredArrow (Opposite.op U) (objectInclusion (C := C)).op ≃
      incomingMorphismIndex U :=
    { toFun := fun j => ⟨j.right.unop.as, j.hom.unop⟩
      invFun := fun p =>
        StructuredArrow.mk (Y := Opposite.op (Discrete.mk p.1)) p.2.op
      left_inv := by
        intro j
        obtain ⟨Y, f, rfl⟩ := j.mk_surjective
        rfl
      right_inv := by
        intro p
        rfl }
  let J := StructuredArrow (Opposite.op U) (objectInclusion (C := C)).op
  have j_eq_of_hom {j k : J} (f : j ⟶ k) : j = k := by
    have hr : j.right = k.right := by
      apply Opposite.unop_injective
      apply Discrete.ext
      exact (Discrete.eq_of_hom f.right.unop).symm
    refine StructuredArrow.obj_ext j k hr ?_
    have hf : eqToHom hr = f.right := Subsingleton.elim _ _
    simpa [hf] using StructuredArrow.w f
  let E : Discrete J ≌ J :=
    { functor := Discrete.functor id
      inverse :=
        { obj := fun j => Discrete.mk j
          map := fun f => Discrete.eqToHom (j_eq_of_hom f)
          map_id := by
            intro j
            simp
          map_comp := by
            intro j k l f g
            simp }
      unitIso := NatIso.ofComponents (fun j => Iso.refl _)
      counitIso := NatIso.ofComponents (fun j => Iso.refl _) }
  let K := StructuredArrow.proj (Opposite.op U) (objectInclusion (C := C)).op ⋙ A
  have hobj (j : J) :
      A.obj (Opposite.op (Discrete.mk (e j).1)) = K.obj j := by
    dsimp [e, K]
    congr 1
  let w₁ : E.functor ⋙ K ≅ Discrete.functor K.obj :=
    NatIso.ofComponents (fun j => Iso.refl _)
      (by
        rintro ⟨j⟩ ⟨k⟩ f
        cases f.down.down
        simp)
  let e₁ : limit (Discrete.functor K.obj) ≅ limit K :=
    HasLimit.isoOfEquivalence E w₁
  let w₂ : (Discrete.equivalence e).functor ⋙
      Discrete.functor (fun p : incomingMorphismIndex U =>
        A.obj (Opposite.op (Discrete.mk p.1))) ≅
      Discrete.functor K.obj :=
    Discrete.natIso (fun ⟨j⟩ => eqToIso (hobj j))
  let e₂ : limit (Discrete.functor K.obj) ≅
      limit (Discrete.functor (fun p : incomingMorphismIndex U =>
        A.obj (Opposite.op (Discrete.mk p.1)))) :=
    HasLimit.isoOfEquivalence (Discrete.equivalence e) w₂
  refine ⟨?_⟩
  simpa [K, incomingProduct, presheafRightKanExtension] using
    (((objectInclusion (C := C)).op.ranObjObjIsoLimit A (Opposite.op U)).trans
      (e₁.symm.trans e₂))

/-- The component of the right Kan extension counit at an incoming arrow. -/
noncomputable def presheafRightKanExtensionProjection
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C)
    {X U : C} (φ : X ⟶ U) :
    ((presheafRightKanExtension (C := C)).obj A).obj (Opposite.op U) ⟶
      A.obj (Opposite.op (Discrete.mk X)) :=
  ((objectInclusion (C := C)).op.ranObjObjIsoLimit A (Opposite.op U)).hom ≫
    limit.π
      (StructuredArrow.proj (Opposite.op U) (objectInclusion (C := C)).op ⋙ A)
      (StructuredArrow.mk (Y := Opposite.op (Discrete.mk X)) φ.op)

/-- Restriction along `g : V ⟶ U` reindexes the family by composition. -/
theorem presheafRightKanExtension_map_projection
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C)
    {X V U : C} (g : V ⟶ U) (ψ : X ⟶ V) :
      ((presheafRightKanExtension (C := C)).obj A).map g.op ≫
        presheafRightKanExtensionProjection A ψ =
      presheafRightKanExtensionProjection A (ψ ≫ g) := by
  simp only [presheafRightKanExtension, presheafRightKanExtensionProjection]
  let fV : StructuredArrow (Opposite.op V) (objectInclusion (C := C)).op :=
    StructuredArrow.mk (Y := Opposite.op (Discrete.mk X)) ψ.op
  let fU : StructuredArrow (Opposite.op U) (objectInclusion (C := C)).op :=
    StructuredArrow.mk (Y := Opposite.op (Discrete.mk X)) (ψ ≫ g).op
  have hV := Functor.ranObjObjIsoLimit_hom_π
    (objectInclusion (C := C)).op A (Opposite.op V) fV
  have hU := Functor.ranObjObjIsoLimit_hom_π
    (objectInclusion (C := C)).op A (Opposite.op U) fU
  dsimp [fV] at hV
  change
    ((objectInclusion (C := C)).op.ran.obj A).map g.op ≫
        (((objectInclusion (C := C)).op.ranObjObjIsoLimit A
          (Opposite.op V)).hom ≫
          limit.π
            (StructuredArrow.proj (Opposite.op V) (objectInclusion (C := C)).op ⋙ A)
            fV) =
      ((objectInclusion (C := C)).op.ranObjObjIsoLimit A
          (Opposite.op U)).hom ≫
        limit.π
          (StructuredArrow.proj (Opposite.op U) (objectInclusion (C := C)).op ⋙ A)
          fU
  rw [hV, hU]
  change (((objectInclusion (C := C)).op.ran.obj A).map g.op ≫
      ((objectInclusion (C := C)).op.ran.obj A).map ψ.op) ≫
        ((objectInclusion (C := C)).op.ranCounit.app A).app
          (Opposite.op (Discrete.mk X)) =
    ((objectInclusion (C := C)).op.ran.obj A).map (g.op ≫ ψ.op) ≫
      ((objectInclusion (C := C)).op.ranCounit.app A).app
        (Opposite.op (Discrete.mk X))
  rw [← (objectInclusion (C := C)).op.ran.obj A |>.map_comp]

/-! ## Exactness and the canonical maps -/

/-- Restriction is exact because it is precomposition. -/
theorem presheafRestriction_isExact {C : Type u} [Category.{v} C] :
    IsExact (presheafRestriction (C := C)) := by
  constructor
  · change PreservesFiniteLimits
      ((Functor.whiskeringLeft ((objectCategory C)ᵒᵖ) Cᵒᵖ
        (ModuleCat.{max u v} (abelianScalar C))).obj
          (objectInclusion (C := C)).op)
    infer_instance
  · change PreservesFiniteColimits
      ((Functor.whiskeringLeft ((objectCategory C)ᵒᵖ) Cᵒᵖ
        (ModuleCat.{max u v} (abelianScalar C))).obj
          (objectInclusion (C := C)).op)
    infer_instance

/-- The right Kan extension is exact, as asserted in the source. -/
theorem presheafRightKanExtension_isExact {C : Type u} [Category.{v} C] :
    IsExact (presheafRightKanExtension (C := C)) := by
  constructor
  · change PreservesFiniteLimits (presheafRightKanExtension (C := C))
    refine ⟨fun J _ _ => ?_⟩
    exact (presheafRestrictionAdjunction (C := C)).rightAdjoint_preservesLimits.preservesLimitsOfShape
  · change PreservesFiniteColimits (presheafRightKanExtension (C := C))
    exact preservesFiniteColimits_of_evaluation
      (presheafRightKanExtension (C := C)) (fun U => by
      let J := StructuredArrow U (objectInclusion (C := C)).op
      have j_eq_of_hom {j k : J} (f : j ⟶ k) : j = k := by
        have hr : j.right = k.right := by
          apply Opposite.unop_injective
          apply Discrete.ext
          exact (Discrete.eq_of_hom f.right.unop).symm
        refine StructuredArrow.obj_ext j k hr ?_
        have hf : eqToHom hr = f.right := Subsingleton.elim _ _
        simpa [hf] using StructuredArrow.w f
      let E : Discrete J ≌ J :=
        { functor := Discrete.functor id
          inverse :=
            { obj := fun j => Discrete.mk j
              map := fun f => Discrete.eqToHom (j_eq_of_hom f)
              map_id := by
                intro j
                simp
              map_comp := by
                intro j k l f g
                simp }
          unitIso := NatIso.ofComponents (fun j => Iso.refl _)
          counitIso := NatIso.ofComponents (fun j => Iso.refl _) }
      let : HasLimitsOfShape J (ModuleCat.{max u v} (abelianScalar C)) :=
        hasLimitsOfShape_of_equivalence E
      let : HasExactLimitsOfShape J (ModuleCat.{max u v} (abelianScalar C)) :=
        HasExactLimitsOfShape.of_domain_equivalence _ E
      let Kfun :=
        (Functor.whiskeringLeft J ((objectCategory C)ᵒᵖ)
          (ModuleCat.{max u v} (abelianScalar C))).obj
          (StructuredArrow.proj U (objectInclusion (C := C)).op)
      let Ffun :=
        (presheafRightKanExtension (C := C)) ⋙
          (evaluation (Cᵒᵖ) (ModuleCat.{max u v} (abelianScalar C))).obj U
      let Lfun := (lim : (J ⥤ ModuleCat.{max u v} (abelianScalar C)) ⥤
        ModuleCat.{max u v} (abelianScalar C))
      let η : Ffun ≅ Kfun ⋙ Lfun := NatIso.ofComponents
        (fun A => by
          simpa [Ffun, Kfun, Lfun, presheafRightKanExtension] using
            ((objectInclusion (C := C)).op.ranObjObjIsoLimit A U))
        (by
          intro A B f
          apply limit.hom_ext
          intro j
          dsimp [Ffun, Kfun, Lfun, presheafRightKanExtension]
          rw [Category.assoc, Category.assoc, limMap_π,
            Functor.ranObjObjIsoLimit_hom_π_assoc,
            Functor.ranObjObjIsoLimit_hom_π]
          change
            ((objectInclusion (C := C)).op.ran.map f).app U ≫
                ((objectInclusion (C := C)).op.ran.obj B).map j.hom ≫
                ((objectInclusion (C := C)).op.ranCounit.app B).app j.right =
              ((objectInclusion (C := C)).op.ran.obj A).map j.hom ≫
                ((objectInclusion (C := C)).op.ranCounit.app A).app j.right ≫
                f.app j.right
          rw [← Category.assoc,
            ← ((objectInclusion (C := C)).op.ran.map f).naturality j.hom]
          have hc :
              ((objectInclusion (C := C)).op.ran.map f).app
                  ((objectInclusion (C := C)).op.obj j.right) ≫
                ((objectInclusion (C := C)).op.ranCounit.app B).app j.right =
              ((objectInclusion (C := C)).op.ranCounit.app A).app j.right ≫
                f.app j.right := by
            have hc' :=
              congr_app ((objectInclusion (C := C)).op.ranCounit.naturality f) j.right
            change
              ((objectInclusion (C := C)).op.ran.map f).app
                    ((objectInclusion (C := C)).op.obj j.right) ≫
                  ((objectInclusion (C := C)).op.ranCounit.app B).app j.right =
                ((objectInclusion (C := C)).op.ranCounit.app A).app j.right ≫
                  f.app j.right at hc'
            exact hc'
          rw [Category.assoc, hc])
      let : PreservesFiniteColimits (Kfun ⋙ Lfun) :=
        comp_preservesFiniteColimits Kfun Lfun
      exact preservesFiniteColimits_of_natIso η.symm)

/-- Restriction preserves monomorphisms. -/
theorem presheafRestriction_preservesMonomorphisms
    {C : Type u} [Category.{v} C] :
    PreservesMonomorphisms (presheafRestriction (C := C)) := by
  change PreservesMonomorphisms
    ((Functor.whiskeringLeft ((objectCategory C)ᵒᵖ) Cᵒᵖ
      (ModuleCat.{max u v} (abelianScalar C))).obj
        (objectInclusion (C := C)).op)
  infer_instance

instance presheafRestriction_additive
    {C : Type u} [Category.{v} C] :
    (presheafRestriction (C := C)).Additive := by
  change ((Functor.whiskeringLeft ((objectCategory C)ᵒᵖ) Cᵒᵖ
    (ModuleCat.{max u v} (abelianScalar C))).obj
      (objectInclusion (C := C)).op).Additive
  infer_instance

/-- The canonical map `v u A ⟶ A`, called the canonical surjection in the source. -/
noncomputable def presheafCanonicalCounit
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C) :
    (presheafRestriction (C := C)).obj
          ((presheafRightKanExtension (C := C)).obj A) ⟶ A :=
  (presheafRestrictionAdjunction (C := C)).counit.app A

/-- The canonical map `B ⟶ u v B`, called the canonical injection in the source. -/
noncomputable def presheafCanonicalUnit
    {C : Type u} [Category.{v} C] (B : AbelianPresheaf C) :
    B ⟶ (presheafRightKanExtension (C := C)).obj
      ((presheafRestriction (C := C)).obj B) :=
  (presheafRestrictionAdjunction (C := C)).unit.app B

theorem presheafCanonicalCounit_epi
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C) :
    Epi (presheafCanonicalCounit A) := by
  rw [presheafCanonicalCounit, NatTrans.epi_iff_epi_app]
  intro k
  change Epi (((objectInclusion (C := C)).op.ranCounit.app A).app k)
  let X := (objectInclusion (C := C)).op.obj k
  let J := StructuredArrow X (objectInclusion (C := C)).op
  let f : J := StructuredArrow.mk (Y := k) (𝟙 X)
  let K := StructuredArrow.proj X (objectInclusion (C := C)).op ⋙ A
  classical
  have j_eq_of_hom {j l : J} (g : j ⟶ l) : j = l := by
    have hr : j.right = l.right := by
      apply Opposite.unop_injective
      apply Discrete.ext
      exact (Discrete.eq_of_hom g.right.unop).symm
    refine StructuredArrow.obj_ext j l hr ?_
    have hg : eqToHom hr = g.right := Subsingleton.elim _ _
    simpa [hg] using StructuredArrow.w g
  let c : Cone K :=
    { pt := K.obj f
      π :=
        { app := fun j =>
            if h : j = f then eqToHom (congrArg K.obj h.symm) else 0
          naturality := by
            intro j l g
            have h : j = l := j_eq_of_hom g
            subst l
            have hg : g.right = 𝟙 _ := Subsingleton.elim _ _
            have hg' : g = 𝟙 j := StructuredArrow.hom_ext g (𝟙 j) hg
            rw [hg']
            simp } }
  let s : K.obj f ⟶ limit K := limit.lift K c
  have hs : s ≫ limit.π K f = 𝟙 _ := by
    dsimp [s]
    rw [limit.lift_π]
    dsimp [c]
    simp
  let se : SplitEpi (limit.π K f) := { section_ := s, id := hs }
  have hπ : Epi (limit.π K f) := se.epi
  have hfac :
      ((objectInclusion (C := C)).op.ranObjObjIsoLimit A X).hom ≫ limit.π K f =
        ((objectInclusion (C := C)).op.ranCounit.app A).app k := by
    simpa [K, f, X] using
      Functor.ranObjObjIsoLimit_hom_π
        (objectInclusion (C := C)).op A X f
  rw [← hfac]
  exact epi_comp' (inferInstance :
    Epi ((objectInclusion (C := C)).op.ranObjObjIsoLimit A X).hom) hπ

theorem presheafCanonicalUnit_mono
    {C : Type u} [Category.{v} C] (B : AbelianPresheaf C) :
    Mono (presheafCanonicalUnit B) := by
  let hAdj := presheafRestrictionAdjunction (C := C)
  let _ : Functor.Faithful (presheafRestriction (C := C)) := by
    constructor
    intro X Y f g hfg
    apply NatTrans.ext
    funext U
    exact congr_app hfg (Opposite.op (Discrete.mk U.unop))
  change Mono (hAdj.unit.app B)
  infer_instance

/-! ## The adjunction hom equivalence -/

/-- The source's displayed hom-set equality, as the canonical adjunction equivalence. -/
def presheafHomEquiv {C : Type u} [Category.{v} C]
    (B : AbelianPresheaf C) (A : ObjectAbelianPresheaf C) :
    (B ⟶ (presheafRightKanExtension (C := C)).obj A) ≃
      ((presheafRestriction (C := C)).obj B ⟶ A) :=
  ((presheafRestrictionAdjunction (C := C)).homEquiv B A).symm

/-! ## Objectwise enough injectives -/

/-- The objectwise injective envelope functor from More on Algebra, Chapter 55. -/
noncomputable def objectPresheafInjectiveFunctor
    {C : Type u} [Category.{v} C] :
    ObjectAbelianPresheaf C ⥤ ObjectAbelianPresheaf C :=
  (Functor.whiskeringRight ((objectCategory C)ᵒᵖ)
      (ModuleCat.{max u v} (abelianScalar C))
      (ModuleCat.{max u v} (abelianScalar C))).obj
    (injectiveEnvelopeFunctor (abelianScalar C))

/-- The objectwise unit supplied by the arrow-valued injective-envelope
construction from More on Algebra, Chapter 55. -/
noncomputable def moduleInjectiveUnit {R : Type w} [CommRing R] :
    𝟭 (ModuleCat.{w} R) ⟶ injectiveEnvelopeFunctor R where
  app M := ((injectiveEmbeddingFunctor R).obj M).hom
  naturality := by
    intro X Y f
    change f ≫ ((injectiveEmbeddingFunctor R).obj Y).hom =
      ((injectiveEmbeddingFunctor R).obj X).hom ≫
        (injectiveEnvelopeFunctor R).map f
    exact ((injectiveEmbeddingFunctor R).map f).w

/-- The objectwise unit `A ⟶ J(A)`. -/
noncomputable def objectPresheafInjectiveUnit
    {C : Type u} [Category.{v} C] :
    𝟭 (ObjectAbelianPresheaf C) ⟶ objectPresheafInjectiveFunctor (C := C) := by
  simpa [objectPresheafInjectiveFunctor, Functor.whiskeringRight_obj_id] using
    ((Functor.whiskeringRight ((objectCategory C)ᵒᵖ)
      (ModuleCat.{max u v} (abelianScalar C))
      (ModuleCat.{max u v} (abelianScalar C))).map
        (moduleInjectiveUnit (R := abelianScalar C)))

/-- A functorial injective embedding in the objectwise presheaf category. -/
noncomputable def objectPresheafInjectiveEmbedding
    {C : Type u} [Category.{v} C] :
    ObjectAbelianPresheaf C ⥤ Arrow (ObjectAbelianPresheaf C) where
  obj A := Arrow.mk ((objectPresheafInjectiveUnit (C := C)).app A)
  map f := Arrow.homMk f
    ((objectPresheafInjectiveFunctor (C := C)).map f)
    (w := by simpa using (objectPresheafInjectiveUnit (C := C)).naturality f)
  map_id A := by
    apply Arrow.hom_ext <;> simp
  map_comp f g := by
    apply Arrow.hom_ext <;> simp

theorem objectPresheafInjectiveEmbedding_left
    {C : Type u} [Category.{v} C] :
    objectPresheafInjectiveEmbedding (C := C) ⋙ Arrow.leftFunc =
      𝟭 (ObjectAbelianPresheaf C) := by
  exact CategoryTheory.Functor.ext (fun A => rfl) (fun A B f => by rfl)

theorem objectPresheafInjectiveEmbedding_mono
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C) :
    Mono ((objectPresheafInjectiveEmbedding (C := C)).obj A).hom := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  change Mono ((moduleInjectiveUnit (R := abelianScalar C)).app (A.obj k))
  rw [ModuleCat.mono_iff_injective]
  exact injectiveEnvelopeMap_injective (R := abelianScalar C) (M := (A.obj k : Type _))

theorem objectPresheafInjectiveEmbedding_injective
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C) :
    Injective ((objectPresheafInjectiveEmbedding (C := C)).obj A).right := by
  change Injective ((objectPresheafInjectiveFunctor (C := C)).obj A)
  let J := (objectPresheafInjectiveFunctor (C := C)).obj A
  have hJ (k : (objectCategory C)ᵒᵖ) : Injective (J.obj k) := by
    dsimp [J, objectPresheafInjectiveFunctor]
    exact injectiveEnvelope_injective (R := abelianScalar C) (M := (A.obj k : Type _))
  refine ⟨?_⟩
  intro X Y g f hf
  let q : Y ⟶ J :=
    { app := fun k => by
        letI := hJ k
        exact Injective.factorThru (g.app k) (f.app k)
      naturality := by
        intro k l α
        have hkl : k = l := by
          apply Opposite.unop_injective
          apply Discrete.ext
          exact (Discrete.eq_of_hom α.unop).symm
        subst l
        have hα : α = 𝟙 _ := Subsingleton.elim _ _
        rw [hα]
        simp }
  refine ⟨q, ?_⟩
  apply NatTrans.ext
  funext k
  exact Injective.comp_factorThru (g.app k) (f.app k)

theorem objectPresheaves_have_functorial_injective_embeddings
    {C : Type u} [Category.{v} C] :
    HasFunctorialInjectiveEmbeddings (C := ObjectAbelianPresheaf C) := by
  refine ⟨objectPresheafInjectiveEmbedding (C := C),
    objectPresheafInjectiveEmbedding_left, ?_, ?_⟩
  · exact objectPresheafInjectiveEmbedding_mono
  · exact objectPresheafInjectiveEmbedding_injective

theorem objectPresheaves_have_enough_injectives
    {C : Type u} [Category.{v} C] :
    EnoughInjectives (ObjectAbelianPresheaf C) := by
  obtain ⟨J, hJleft, hJmono, hJinjective⟩ :=
    objectPresheaves_have_functorial_injective_embeddings (C := C)
  refine ⟨?_⟩
  intro A
  have hleft : (J.obj A).left = A :=
    congrArg (fun F => F.obj A) hJleft
  refine ⟨{ J := (J.obj A).right
            injective := hJinjective A
            f := eqToHom hleft.symm ≫ (J.obj A).hom
            mono := inferInstance }⟩

/-! ## The construction `B ↦ u J(v B)` -/

/-- The right Kan extension preserves injective objects by the adjunction. -/
theorem presheafRightKanExtension_preservesInjectiveObjects
    {C : Type u} [Category.{v} C] :
    Functor.PreservesInjectiveObjects (presheafRightKanExtension (C := C)) := by
  let hMono : PreservesMonomorphisms (presheafRestriction (C := C)) :=
    presheafRestriction_preservesMonomorphisms
  exact @Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    _ _ _ _ _ _ (presheafRestrictionAdjunction (C := C)) hMono

instance presheafRightKanExtension_additive
    {C : Type u} [Category.{v} C] :
    (presheafRightKanExtension (C := C)).Additive := by
  constructor
  intro X Y f g
  apply ((presheafRestrictionAdjunction (C := C)).homEquiv _ _).symm.injective
  simp [Adjunction.homEquiv_counit]

/-- The unit followed by the image of the objectwise injective embedding. -/
noncomputable def presheafInjectiveEmbedding
    {C : Type u} [Category.{v} C] (B : AbelianPresheaf C) :
    B ⟶ (presheafRightKanExtension (C := C)).obj
      ((objectPresheafInjectiveFunctor (C := C)).obj
        ((presheafRestriction (C := C)).obj B)) :=
  presheafCanonicalUnit B ≫
    (presheafRightKanExtension (C := C)).map
      ((objectPresheafInjectiveUnit (C := C)).app
        ((presheafRestriction (C := C)).obj B))

theorem presheafInjectiveEmbedding_mono
    {C : Type u} [Category.{v} C] (B : AbelianPresheaf C) :
    Mono (presheafInjectiveEmbedding B) := by
  have hRight : PreservesMonomorphisms (presheafRightKanExtension (C := C)) :=
    Functor.preservesMonomorphisms_of_adjunction
      (presheafRestrictionAdjunction (C := C))
  have hJ : Mono ((objectPresheafInjectiveUnit (C := C)).app
      ((presheafRestriction (C := C)).obj B)) :=
    objectPresheafInjectiveEmbedding_mono ((presheafRestriction (C := C)).obj B)
  have hMap : Mono ((presheafRightKanExtension (C := C)).map
      ((objectPresheafInjectiveUnit (C := C)).app
        ((presheafRestriction (C := C)).obj B))) :=
    @Functor.PreservesMonomorphisms.preserves _ _ _ _ _
      hRight _ _ _ hJ
  have hUnit : Mono (presheafCanonicalUnit B) := presheafCanonicalUnit_mono B
  constructor
  intro Z f g hfg
  apply hUnit.right_cancellation
  apply hMap.right_cancellation
  simpa only [presheafInjectiveEmbedding, Category.assoc] using hfg

theorem presheafInjectiveEmbedding_target_injective
    {C : Type u} [Category.{v} C] (B : AbelianPresheaf C) :
    Injective ((presheafRightKanExtension (C := C)).obj
      ((objectPresheafInjectiveFunctor (C := C)).obj
        ((presheafRestriction (C := C)).obj B)) : AbelianPresheaf C) := by
  have hU : Functor.PreservesInjectiveObjects
      (presheafRightKanExtension (C := C)) :=
    presheafRightKanExtension_preservesInjectiveObjects (C := C)
  exact hU.injective_obj
    (X := (objectPresheafInjectiveFunctor (C := C)).obj
      ((presheafRestriction (C := C)).obj B))
    (objectPresheafInjectiveEmbedding_injective
      ((presheafRestriction (C := C)).obj B))

/-! ## Functorial injective embeddings -/

theorem abelianPresheaves_have_functorial_injective_embeddings
    {C : Type u} [Category.{v} C] :
    HasFunctorialInjectiveEmbeddings (C := AbelianPresheaf C) := by
  exact adjoint_functorial_injective_embeddings
    (presheafRightKanExtension (C := C)) (presheafRestriction (C := C))
    (presheafRestrictionAdjunction (C := C))
    (presheafRestriction_preservesMonomorphisms (C := C))
    (objectPresheaves_have_enough_injectives (C := C))
    (fun B hB => by
      have hFaithful : Functor.Faithful (presheafRestriction (C := C)) := by
        constructor
        intro X Y f g hfg
        apply NatTrans.ext
        funext U
        exact congr_app hfg (Opposite.op (Discrete.mk U.unop))
      apply (IsZero.iff_id_eq_zero B).2
      apply hFaithful.map_injective
      simpa using (IsZero.iff_id_eq_zero ((presheafRestriction (C := C)).obj B)).1 hB)
    (objectPresheaves_have_functorial_injective_embeddings (C := C))

end Formalization.Books.Injectives.Unit06
