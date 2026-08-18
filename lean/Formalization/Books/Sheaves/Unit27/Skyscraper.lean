import Formalization.Books.Sheaves.Unit08.AbelianSheaves
import Formalization.Books.Sheaves.Unit10.SheavesOfModules
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Algebra.Module.PUnit
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Sheaves on Spaces, Chapter 27: Skyscraper sheaves and stalks

This file formalizes `books/sheaves.tex:3269-3366`.  Mathlib's canonical
skyscraper presheaf and sheaf are used for sets, abelian groups, and general
category-valued sheaves.  The module-valued construction is expressed with a
chosen sheaf of modules whose underlying additive sheaf is the canonical
abelian skyscraper; its support and away-from-support stalk interfaces retain
the scalar structures required by the source.

Stalk equalities are represented by canonical categorical isomorphisms, and
the displayed Hom identities are represented by the corresponding adjunction
Hom equivalences.
-/

namespace Formalization.Books.Sheaves.Unit27

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit10
open scoped ZeroObject

universe v

noncomputable section

/-! ## The skyscraper construction -/

/-- The point map used to realize a skyscraper as a point pushforward. -/
noncomputable def skyscraperPointMap {X : TopCat.{v}} (x : X) :
    TopCat.of (ULift.{v} PUnit) ⟶ X :=
  TopCat.ofHom (ContinuousMap.const (TopCat.of (ULift.{v} PUnit)) x)

/-- The set-valued skyscraper presheaf at `x` with value `A`. -/
noncomputable def setSkyscraperPresheaf {X : TopCat.{v}}
    (x : X) (A : Type v) : TopCat.Presheaf (Type v) X := by
  classical
  exact skyscraperPresheaf x A

/-- The set-valued skyscraper sheaf at `x` with value `A`. -/
noncomputable def setSkyscraperSheaf {X : TopCat.{v}}
    (x : X) (A : Type v) : TopCat.Sheaf (Type v) X := by
  classical
  exact skyscraperSheaf x A

/-- Functoriality of the set-valued skyscraper construction. -/
noncomputable def setSkyscraperSheafFunctor {X : TopCat.{v}} (x : X) :
    Type v ⥤ TopCat.Sheaf (Type v) X := by
  classical
  exact skyscraperSheafFunctor x

/-- The abelian-group-valued skyscraper presheaf and sheaf. -/
noncomputable def abelianSkyscraperPresheaf {X : TopCat.{v}}
    (x : X) (A : AddCommGrpCat.{v}) :
    TopCat.Presheaf AddCommGrpCat.{v} X := by
  classical
  exact skyscraperPresheaf x A

noncomputable def abelianSkyscraperSheaf {X : TopCat.{v}}
    (x : X) (A : AddCommGrpCat.{v}) :
    TopCat.Sheaf AddCommGrpCat.{v} X := by
  classical
  exact skyscraperSheaf x A

/-- Functoriality of the abelian-group-valued skyscraper construction. -/
noncomputable def abelianSkyscraperSheafFunctor {X : TopCat.{v}} (x : X) :
    AddCommGrpCat.{v} ⥤ TopCat.Sheaf AddCommGrpCat.{v} X := by
  classical
  exact skyscraperSheafFunctor x

/-- The generic algebraic-structure-valued skyscraper presheaf and sheaf. -/
noncomputable def algebraicSkyscraperPresheaf
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (x : X) (A : C) : TopCat.Presheaf C X := by
  classical
  exact skyscraperPresheaf x A

noncomputable def algebraicSkyscraperSheaf
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (x : X) (A : C) : TopCat.Sheaf C X := by
  classical
  exact skyscraperSheaf x A

/-- Functoriality of the algebraic-structure-valued construction. -/
noncomputable def algebraicSkyscraperSheafFunctor
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (x : X) : C ⥤ TopCat.Sheaf C X := by
  classical
  exact skyscraperSheafFunctor x

/-! ## The four skyscraper-sheaf predicates -/

/-- A set-valued sheaf is a skyscraper sheaf when it is isomorphic to one at a
point. -/
def IsSetSkyscraperSheaf {X : TopCat.{v}}
    (F : TopCat.Sheaf (Type v) X) : Prop :=
  ∃ x : X, ∃ A : Type v, Nonempty (F ≅ setSkyscraperSheaf x A)

/-- An abelian sheaf is a skyscraper sheaf when it is isomorphic to one at a
point. -/
def IsAbelianSkyscraperSheaf {X : TopCat.{v}}
    (F : Ab X) : Prop :=
  ∃ x : X, ∃ A : AddCommGrpCat.{v}, Nonempty (F ≅ abelianSkyscraperSheaf x A)

/-- A sheaf of algebraic structures is a skyscraper sheaf when it is
isomorphic to one at a point. -/
def IsAlgebraicSkyscraperSheaf
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (F : TopCat.Sheaf C X) : Prop :=
  ∃ x : X, ∃ A : C, Nonempty (F ≅ algebraicSkyscraperSheaf x A)

/-! The module-valued construction -/

/-- Data for a module-valued skyscraper sheaf with prescribed support stalk. -/
structure ModuleSkyscraperData {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) where
  sheaf : Mod O
  underlying_iso :
    Nonempty (sheaf.val.presheaf ≅
      (abelianSkyscraperSheaf x (AddCommGrpCat.of (↑A))).presheaf)
  stalk_at_support :
    Nonempty (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
        sheaf.val.presheaf x)) ≅ A)
  stalk_away : ∀ {x' : X}, ¬x ⤳ x' →
    Nonempty (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x')
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
        sheaf.val.presheaf x')) ≅ 0)

private lemma module_eqToHom_smul {R : Type*} [Semiring R]
    {M N : AddCommGrpCat} (h : M = N) (inst : Module R (↑N))
    (r : R) (m : ↑M) :
    (letI : Module R (↑N) := inst
     letI : Module R (↑M) := by rw [h]; exact inst
     r • m) =
      (ConcreteCategory.hom (eqToHom h.symm))
        (r • (ConcreteCategory.hom (eqToHom h) m)) := by
  cases h
  simp
  rfl

/-- Existence of the module-valued skyscraper construction. -/
theorem exists_moduleSkyscraperSheaf {X : TopCat.{v}}
    (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    Nonempty (ModuleSkyscraperData O x A) := by
  classical
  let hDec : ∀ U : Opens X, Decidable (x ∈ U) := fun U => Classical.propDecidable _
  let : ∀ U : Opens X, Decidable (x ∈ U) := hDec
  let (U : (Opens X)ᵒᵖ) : Module (O.obj.obj U)
      ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj U) := by
    by_cases h : x ∈ U.unop
    · change Module (O.obj.obj U)
        (↑(if h : x ∈ U.unop then AddCommGrpCat.of (↑A) else ⊤_ AddCommGrpCat))
      rw [dif_pos h]
      exact Module.compHom (↑A)
        (TopCat.Presheaf.germ (C := RingCat.{v}) O.obj U.unop x h).hom
    · change Module (O.obj.obj U)
        (↑(if h : x ∈ U.unop then AddCommGrpCat.of (↑A) else ⊤_ AddCommGrpCat))
      rw [dif_neg h]
      let : Subsingleton (↑(⊤_ AddCommGrpCat)) :=
        AddCommGrpCat.subsingleton_of_isZero
          ((isZero_zero AddCommGrpCat).of_iso
            (HasZeroObject.zeroIsoTerminal :
              (0 : AddCommGrpCat) ≅ ⊤_ AddCommGrpCat).symm)
      letI : SMul (O.obj.obj U) (↑(⊤_ AddCommGrpCat)) :=
        ⟨fun _ _ => 0⟩
      exact Module.ofMinimalAxioms (M := ↑(⊤_ AddCommGrpCat))
        (fun _ _ _ => Subsingleton.elim _ _)
        (fun _ _ _ => Subsingleton.elim _ _)
        (fun _ _ _ => Subsingleton.elim _ _)
        (fun _ => Subsingleton.elim _ _)
  let M : PresheafOfModules O.obj := PresheafOfModules.ofPresheaf
      (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) (by
    intro U V f
    by_cases hV : x ∈ V.unop
    · have hU : x ∈ U.unop := leOfHom f.unop hV
      intro r m
      have hUobj :
          (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj U =
            AddCommGrpCat.of (↑A) := by
        simp [skyscraperPresheaf_obj, hU]
      have hVobj :
          (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj V =
            AddCommGrpCat.of (↑A) := by
        simp [skyscraperPresheaf_obj, hV]
      let eU :
          (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj U ⟶
            AddCommGrpCat.of (↑A) := eqToHom hUobj
      let eV :
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj V ⟶
            AddCommGrpCat.of (↑A) := eqToHom hVobj
      let eUinv :
          AddCommGrpCat.of (↑A) ⟶
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj U := eqToHom hUobj.symm
      let eVinv :
          AddCommGrpCat.of (↑A) ⟶
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj V := eqToHom hVobj.symm
      let transported : Module (O.obj.obj U)
          (↑((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj U)) := by
        rw [hUobj]
        exact Module.compHom (↑A)
          (TopCat.Presheaf.germ (C := RingCat.{v}) O.obj U.unop x hU).hom
      have hinst : this U = transported := by
        apply Module.ext' _ _
        intro r' m'
        change @SMul.smul _ _ ((this U).toSMul) r' m' =
          @SMul.smul _ _ (transported.toSMul) r' m'
        unfold this
        rw [dif_pos hU]
        rfl
      have hsource :
          (letI := this U; r • m) =
            (ConcreteCategory.hom eUinv)
              ((TopCat.Presheaf.germ (C := RingCat.{v}) O.obj U.unop x hU).hom r •
                (ConcreteCategory.hom eU) m) := by
        have ha :
            (letI := this U; r • m) =
              (letI := transported; r • m) := by
          rw [hinst]
        have hb :
            (letI := transported; r • m) =
              (ConcreteCategory.hom eUinv)
                ((TopCat.Presheaf.germ (C := RingCat.{v}) O.obj U.unop x hU).hom r •
                  (ConcreteCategory.hom eU) m) := by
          exact module_eqToHom_smul hUobj
            (Module.compHom (↑A)
              (TopCat.Presheaf.germ (C := RingCat.{v}) O.obj U.unop x hU).hom) r m
        exact ha.trans hb
      have hmap : (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f ≫ eV = eU := by
        have hUobj' :
            (if h : x ∈ U.unop then AddCommGrpCat.of (↑A) else ⊤_ AddCommGrpCat) =
              AddCommGrpCat.of (↑A) := by
          change (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj U =
            AddCommGrpCat.of (↑A)
          exact hUobj
        have hVobj' :
            (if h : x ∈ V.unop then AddCommGrpCat.of (↑A) else ⊤_ AddCommGrpCat) =
              AddCommGrpCat.of (↑A) := by
          change (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj V =
            AddCommGrpCat.of (↑A)
          exact hVobj
        have hmap' :
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f ≫
                eqToHom hVobj' = eqToHom hUobj' := by
          dsimp [skyscraperPresheaf]
          rw [dif_pos hV]
          simp only [eqToHom_trans]
        have hUeq : hUobj' = hUobj := Subsingleton.elim _ _
        have hVeq : hVobj' = hVobj := Subsingleton.elim _ _
        change (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f ≫
            eqToHom hVobj = eqToHom hUobj
        rw [← hVeq, ← hUeq]
        exact hmap'
      let transportedV : Module (O.obj.obj V)
          (↑((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj V)) := by
        rw [hVobj]
        exact Module.compHom (↑A)
          (TopCat.Presheaf.germ (C := RingCat.{v}) O.obj V.unop x hV).hom
      have hinstV : this V = transportedV := by
        apply Module.ext' _ _
        intro r' m'
        change @SMul.smul _ _ ((this V).toSMul) r' m' =
          @SMul.smul _ _ (transportedV.toSMul) r' m'
        unfold this
        rw [dif_pos hV]
        rfl
      have hVsource :
          (letI := this V
           (ConcreteCategory.hom (O.obj.map f)) r •
              (ConcreteCategory.hom
                ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f)) m) =
            (ConcreteCategory.hom eVinv)
              ((TopCat.Presheaf.germ (C := RingCat.{v}) O.obj V.unop x hV).hom
                ((ConcreteCategory.hom (O.obj.map f)) r) •
                (ConcreteCategory.hom eV)
                  ((ConcreteCategory.hom
                    ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f)) m)) := by
        have haV :
            (letI := this V
             (ConcreteCategory.hom (O.obj.map f)) r •
                (ConcreteCategory.hom
                  ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f)) m) =
              (letI := transportedV
               (ConcreteCategory.hom (O.obj.map f)) r •
                (ConcreteCategory.hom
                  ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f)) m) := by
          rw [hinstV]
        have hbV :
            (letI := transportedV
             (ConcreteCategory.hom (O.obj.map f)) r •
                (ConcreteCategory.hom
                  ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f)) m) =
              (ConcreteCategory.hom eVinv)
                ((TopCat.Presheaf.germ (C := RingCat.{v}) O.obj V.unop x hV).hom
                  ((ConcreteCategory.hom (O.obj.map f)) r) •
                  (ConcreteCategory.hom eV)
                    ((ConcreteCategory.hom
                      ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f)) m)) := by
          exact module_eqToHom_smul hVobj
            (Module.compHom (↑A)
              (TopCat.Presheaf.germ (C := RingCat.{v}) O.obj V.unop x hV).hom)
            ((ConcreteCategory.hom (O.obj.map f)) r)
            ((ConcreteCategory.hom
              ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f)) m)
        exact haV.trans hbV
      have hcomp : eUinv ≫
          (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f = eVinv := by
        apply (cancel_mono eV).1
        rw [Category.assoc, hmap]
        dsimp [eU, eUinv, eV, eVinv]
        simp
      have hmap_apply
          (z : ↑((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj U)) :
          (ConcreteCategory.hom eV)
              ((ConcreteCategory.hom
                ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f)) z) =
            (ConcreteCategory.hom eU) z := by
        have hz := congrArg (fun k => (ConcreteCategory.hom k) z) hmap
        simpa only [ConcreteCategory.comp_apply] using hz
      have hcomp_apply (a : ↑A) :
          (ConcreteCategory.hom
            ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f))
              ((ConcreteCategory.hom eUinv) a) =
            (ConcreteCategory.hom eVinv) a := by
        have ha := congrArg (fun k => (ConcreteCategory.hom k) a) hcomp
        simpa only [ConcreteCategory.comp_apply] using ha
      have hscalar :
          (TopCat.Presheaf.germ (C := RingCat.{v}) O.obj V.unop x hV).hom
              ((ConcreteCategory.hom (O.obj.map f)) r) =
            (TopCat.Presheaf.germ (C := RingCat.{v}) O.obj U.unop x hU).hom r := by
        simpa using (TopCat.Presheaf.germ_res_apply' O.obj f x hV r)
      have hsource_eU :
          (ConcreteCategory.hom eU) (letI := this U; r • m) =
            (TopCat.Presheaf.germ (C := RingCat.{v}) O.obj U.unop x hU).hom r •
              (ConcreteCategory.hom eU) m := by
        have hcancelU : eUinv ≫ eU = 𝟙 _ := by
          dsimp [eU, eUinv]
          simp
        have hcU (z : ↑A) :
            (ConcreteCategory.hom eU) ((ConcreteCategory.hom eUinv) z) = z := by
          have hz := congrArg (fun k => (ConcreteCategory.hom k) z) hcancelU
          simpa using hz
        have hh := congrArg (fun z => (ConcreteCategory.hom eU) z) hsource
        calc
          (ConcreteCategory.hom eU) (letI := this U; r • m) =
              (ConcreteCategory.hom eU)
                ((ConcreteCategory.hom eUinv)
                  ((TopCat.Presheaf.germ (C := RingCat.{v}) O.obj U.unop x hU).hom r •
                    (ConcreteCategory.hom eU) m)) := hh
          _ = _ := hcU _
      have hVsource_eV :
          (ConcreteCategory.hom eV)
              (letI := this V
               (ConcreteCategory.hom (O.obj.map f)) r •
                (ConcreteCategory.hom
                  ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f)) m) =
            (TopCat.Presheaf.germ (C := RingCat.{v}) O.obj V.unop x hV).hom
                ((ConcreteCategory.hom (O.obj.map f)) r) •
              (ConcreteCategory.hom eV)
                ((ConcreteCategory.hom
                  ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f)) m) := by
        have hcancelV : eVinv ≫ eV = 𝟙 _ := by
          dsimp [eV, eVinv]
          simp
        have hcV (z : ↑A) :
            (ConcreteCategory.hom eV) ((ConcreteCategory.hom eVinv) z) = z := by
          have hz := congrArg (fun k => (ConcreteCategory.hom k) z) hcancelV
          simpa using hz
        have hh := congrArg (fun z => (ConcreteCategory.hom eV) z) hVsource
        calc
          (ConcreteCategory.hom eV)
                (letI := this V
                 (ConcreteCategory.hom (O.obj.map f)) r •
                  (ConcreteCategory.hom
                    ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f)) m) =
              (ConcreteCategory.hom eV)
                ((ConcreteCategory.hom eVinv)
                  ((TopCat.Presheaf.germ (C := RingCat.{v}) O.obj V.unop x hV).hom
                    ((ConcreteCategory.hom (O.obj.map f)) r) •
                    (ConcreteCategory.hom eV)
                      ((ConcreteCategory.hom
                        ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map f)) m))) := hh
          _ = _ := hcV _
      have heV_inj : Function.Injective (ConcreteCategory.hom eV) := by
        intro a b hab
        have hcancelV : eV ≫ eVinv = 𝟙 _ := by
          dsimp [eV, eVinv]
          simp
        calc
          a = (ConcreteCategory.hom eVinv) ((ConcreteCategory.hom eV) a) := by
            have hca := congrArg (fun k => (ConcreteCategory.hom k) a) hcancelV
            simpa using hca.symm
          _ = (ConcreteCategory.hom eVinv) ((ConcreteCategory.hom eV) b) :=
            congrArg (fun z => (ConcreteCategory.hom eVinv) z) hab
          _ = b := by
            have hcb := congrArg (fun k => (ConcreteCategory.hom k) b) hcancelV
            simpa using hcb
      apply heV_inj
      rw [hmap_apply, hsource_eU, hVsource_eV, hmap_apply, hscalar]
    · by_cases hU : x ∈ U.unop
      · have hVobj :
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj V =
              ⊤_ AddCommGrpCat := by
          simp [skyscraperPresheaf_obj, hV]
        intro r m
        let : Subsingleton
            (↑((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj V)) := by
          rw [hVobj]
          exact AddCommGrpCat.subsingleton_of_isZero
            ((isZero_zero AddCommGrpCat).of_iso
              (HasZeroObject.zeroIsoTerminal :
                (0 : AddCommGrpCat) ≅ ⊤_ AddCommGrpCat).symm)
        exact Subsingleton.elim _ _
      · have hVobj :
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj V =
              ⊤_ AddCommGrpCat := by
          simp [skyscraperPresheaf_obj, hV]
        intro r m
        let : Subsingleton
            (↑((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj V)) := by
          rw [hVobj]
          exact AddCommGrpCat.subsingleton_of_isZero
            ((isZero_zero AddCommGrpCat).of_iso
              (HasZeroObject.zeroIsoTerminal :
                (0 : AddCommGrpCat) ≅ ⊤_ AddCommGrpCat).symm)
        exact Subsingleton.elim _ _)
  let S : Mod O :=
    { val := M
      isSheaf := by
        change (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).IsSheaf
        exact (skyscraperSheaf x (AddCommGrpCat.of (↑A))).property }
  refine ⟨S, ⟨Iso.refl _⟩, ?_, ?_⟩
  · let eAdd :=
      skyscraperPresheafStalkOfSpecializes x
        (AddCommGrpCat.of (↑A)) (specializes_refl x)
    refine ⟨ModuleCat.isoMk eAdd ?_⟩
    intro r
    apply TopCat.Presheaf.stalk_hom_ext
      (skyscraperPresheaf x (AddCommGrpCat.of (↑A)))
    intro U hxU
    apply ConcreteCategory.hom_ext
    intro s
    change (ConcreteCategory.hom (A.smul r))
          ((ConcreteCategory.hom eAdd.hom)
            ((TopCat.Presheaf.germ (skyscraperPresheaf x (AddCommGrpCat.of (↑A)))
              U x hxU) s)) =
      (ConcreteCategory.hom eAdd.hom)
        ((ConcreteCategory.hom
          ((ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
            (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) S.val.presheaf x))).smul r))
          ((TopCat.Presheaf.germ
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) U x hxU) s))
    obtain ⟨V, hxV, rV, hrV⟩ :=
      TopCat.Presheaf.exists_germ_eq O.obj r
    let W : Opens X := U ⊓ V
    let hxW : x ∈ W := ⟨hxU, hxV⟩
    let rW : O.obj.obj (Opposite.op W) :=
      O.obj.map (homOfLE (show W ≤ V from inf_le_right)).op rV
    let sW : (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj
        (Opposite.op W) :=
      (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).map
        (homOfLE (show W ≤ U from inf_le_left)).op s
    let sW' : S.val.presheaf.obj (Opposite.op W) := sW
    have hrW :
        TopCat.Presheaf.germ O.obj W x hxW rW = r := by
      dsimp [rW]
      rw [TopCat.Presheaf.germ_res_apply]
      simpa using hrV
    have hsW :
        TopCat.Presheaf.germ
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) W x hxW sW =
          TopCat.Presheaf.germ
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) U x hxU s := by
      dsimp [sW]
      rw [TopCat.Presheaf.germ_res_apply]
    rw [← hrW, ← hsW]
    have hWobj :
        (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj (Opposite.op W) =
          AddCommGrpCat.of (↑A) := by
      simp [skyscraperPresheaf_obj, hxW]
    let eW :
        (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj (Opposite.op W) ⟶
          AddCommGrpCat.of (↑A) := eqToHom hWobj
    have hWobjS : S.val.presheaf.obj (Opposite.op W) = AddCommGrpCat.of (↑A) := by
      change (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj
          (Opposite.op W) = AddCommGrpCat.of (↑A)
      exact hWobj
    let eWS : S.val.presheaf.obj (Opposite.op W) ⟶ AddCommGrpCat.of (↑A) :=
      eqToHom hWobjS
    have heW :
        (TopCat.Presheaf.germ
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) W x hxW) ≫
            eAdd.hom = eW := by
      have hcat :=
        germ_skyscraperPresheafStalkOfSpecializes_hom
          (p₀ := x) (A := AddCommGrpCat.of (↑A))
          (h := specializes_refl x) W hxW
      rw [hcat]
      rfl
    have heWS :
        (TopCat.Presheaf.germ S.val.presheaf W x hxW) ≫ eAdd.hom = eWS := by
      change
        (TopCat.Presheaf.germ
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) W x hxW) ≫
              eAdd.hom = eW
      exact heW
    let transportedW : Module (O.obj.obj (Opposite.op W))
      (↑((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj
          (Opposite.op W))) := by
      rw [hWobj]
      exact Module.compHom (↑A)
        (TopCat.Presheaf.germ (C := RingCat.{v}) O.obj W x hxW).hom
    have hinstW : this (Opposite.op W) = transportedW := by
      apply Module.ext' _ _
      intro r' m'
      change @SMul.smul _ _ ((this (Opposite.op W)).toSMul) r' m' =
        @SMul.smul _ _ (transportedW.toSMul) r' m'
      unfold this
      rw [dif_pos hxW]
      rfl
    have hsourceW :
        (letI := transportedW; rW • sW) =
          (ConcreteCategory.hom (eqToHom hWobj.symm))
            ((TopCat.Presheaf.germ (C := RingCat.{v}) O.obj W x hxW).hom rW •
              (ConcreteCategory.hom eW) sW) := by
      exact module_eqToHom_smul hWobj
        (Module.compHom (↑A)
          (TopCat.Presheaf.germ (C := RingCat.{v}) O.obj W x hxW).hom) rW sW
    have hsmulW :
        TopCat.Presheaf.germ S.val.presheaf W x hxW
            (letI := this (Opposite.op W); rW • sW') =
          (TopCat.Presheaf.germ O.obj W x hxW rW) •
            TopCat.Presheaf.germ S.val.presheaf W x hxW sW' := by
      exact PresheafOfModules.germ_ringCat_smul S.val x W hxW rW sW'
    have hsourceW' :
        (letI := this (Opposite.op W); rW • sW) =
          (ConcreteCategory.hom (eqToHom hWobj.symm))
            ((TopCat.Presheaf.germ (C := RingCat.{v}) O.obj W x hxW).hom rW •
              (ConcreteCategory.hom eW) sW) := by
      rw [hinstW]
      exact hsourceW
    have hsourceWS :
        (letI := this (Opposite.op W); rW • sW') =
          (ConcreteCategory.hom (eqToHom hWobjS.symm))
            ((TopCat.Presheaf.germ (C := RingCat.{v}) O.obj W x hxW).hom rW •
              (ConcreteCategory.hom eWS) sW') := by
      change
        (letI := this (Opposite.op W); rW • sW) =
          (ConcreteCategory.hom (eqToHom hWobj.symm))
            ((TopCat.Presheaf.germ (C := RingCat.{v}) O.obj W x hxW).hom rW •
              (ConcreteCategory.hom eW) sW)
      exact hsourceW'
    have heW_apply (n :
        ↑((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj
          (Opposite.op W))) :
        (ConcreteCategory.hom eAdd.hom)
            ((ConcreteCategory.hom
              ((skyscraperPresheaf x (AddCommGrpCat.of (↑A))).germ W x hxW)) n) =
          (ConcreteCategory.hom eW) n := by
      have hn := congrArg (fun k => (ConcreteCategory.hom k) n) heW
      simpa only [ConcreteCategory.comp_apply] using hn
    have heWS_apply (n : S.val.presheaf.obj (Opposite.op W)) :
        (ConcreteCategory.hom eAdd.hom)
            ((ConcreteCategory.hom
              (TopCat.Presheaf.germ S.val.presheaf W x hxW)) n) =
          (ConcreteCategory.hom eWS) n := by
      have hn := congrArg (fun k => (ConcreteCategory.hom k) n) heWS
      change (ConcreteCategory.hom
          (TopCat.Presheaf.germ S.val.presheaf W x hxW ≫ eAdd.hom)) n =
        (ConcreteCategory.hom eWS) n
      simpa only [ConcreteCategory.comp_apply] using hn
    have hsmul_apply :
        (ConcreteCategory.hom
          ((ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
            (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) S.val.presheaf x))).smul
              ((ConcreteCategory.hom (TopCat.Presheaf.germ O.obj W x hxW)) rW)))
          ((ConcreteCategory.hom
            (TopCat.Presheaf.germ S.val.presheaf W x hxW)) sW') =
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ S.val.presheaf W x hxW))
            (letI := this (Opposite.op W); rW • sW') := by
      change
        (ConcreteCategory.hom (TopCat.Presheaf.germ O.obj W x hxW)) rW •
            (ConcreteCategory.hom
              (TopCat.Presheaf.germ S.val.presheaf W x hxW)) sW' =
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ S.val.presheaf W x hxW))
            (letI := this (Opposite.op W); rW • sW')
      exact hsmulW.symm
    rw [heW_apply sW]
    change (ConcreteCategory.hom (A.smul
      ((ConcreteCategory.hom (TopCat.Presheaf.germ O.obj W x hxW)) rW)))
        ((ConcreteCategory.hom eWS) sW') =
      (ConcreteCategory.hom eAdd.hom)
        ((ConcreteCategory.hom
          ((ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
            (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) S.val.presheaf x))).smul
              ((ConcreteCategory.hom (TopCat.Presheaf.germ O.obj W x hxW)) rW)))
          ((ConcreteCategory.hom
            (TopCat.Presheaf.germ S.val.presheaf W x hxW)) sW'))
    rw [hsmul_apply]
    rw [heWS_apply (letI := this (Opposite.op W); rW • sW')]
    have hcancelWS : eqToHom hWobjS.symm ≫ eWS = 𝟙 _ := by
      dsimp [eWS]
      simp
    have hcancelWS_apply (z : ↑A) :
        (ConcreteCategory.hom eWS)
            ((ConcreteCategory.hom (eqToHom hWobjS.symm)) z) = z := by
      have hz := congrArg (fun k => (ConcreteCategory.hom k) z) hcancelWS
      change (ConcreteCategory.hom eWS)
          ((ConcreteCategory.hom (eqToHom hWobjS.symm)) z) = z at hz
      exact hz
    have hsourceWS_eWS :
        (ConcreteCategory.hom eWS)
            (letI := this (Opposite.op W); rW • sW') =
          (ConcreteCategory.hom (A.smul
            ((ConcreteCategory.hom (TopCat.Presheaf.germ O.obj W x hxW)) rW)))
            ((ConcreteCategory.hom eWS) sW') := by
      have hz := congrArg (fun z => (ConcreteCategory.hom eWS) z) hsourceWS
      calc
        (ConcreteCategory.hom eWS)
              (letI := this (Opposite.op W); rW • sW') =
            (ConcreteCategory.hom eWS)
              ((ConcreteCategory.hom (eqToHom hWobjS.symm))
                ((TopCat.Presheaf.germ (C := RingCat.{v}) O.obj W x hxW).hom rW •
                  (ConcreteCategory.hom eWS) sW')) := hz
        _ = _ := hcancelWS_apply _
    exact hsourceWS_eWS.symm
  · intro x' h
    let eAdd :=
      skyscraperPresheafStalkOfNotSpecializes x
        (AddCommGrpCat.of (↑A)) h
    let : Subsingleton (↑(0 : ModuleCat
        (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x'))) :=
      ModuleCat.subsingleton_of_isZero (isZero_zero _)
    let zM : (⊤_ Ab) ≅
        (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x'))
          Ab).obj (0 : ModuleCat
            (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x')) :=
      { hom := 0
        inv := terminalIsTerminal.from _
        hom_inv_id := by
          apply terminalIsTerminal.hom_ext
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro m
          exact Subsingleton.elim _ _ }
    refine ⟨ModuleCat.isoMk (eAdd ≪≫ zM) ?_⟩
    intro r
    apply ConcreteCategory.hom_ext
    intro m
    exact Subsingleton.elim _ _

/-- A chosen sheaf of `O`-modules representing the skyscraper with value `A`.
-/
noncomputable def moduleSkyscraperSheaf {X : TopCat.{v}}
    (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    Mod O := by
  exact (Classical.choice (exists_moduleSkyscraperSheaf O x A)).sheaf

/-- The underlying additive morphism on module stalks. -/
noncomputable def moduleStalkAddMap {X : TopCat.{v}} {O : RingSheaf X}
    {F G : Mod O} (φ : F ⟶ G) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
    ((PresheafOfModules.toPresheaf O.obj).map φ.val)

/-- The stalk map is linear over the stalk of the scalar sheaf. -/
theorem moduleStalkAddMap_smul {X : TopCat.{v}} {O : RingSheaf X}
    {F G : Mod O} (φ : F ⟶ G) (x : X)
    (r : TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) :
    moduleStalkAddMap φ x ≫
        (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
          (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf x))).smul r =
        (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
          (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x))).smul r ≫
        moduleStalkAddMap φ x := by
  classical
  apply TopCat.Presheaf.stalk_hom_ext F.val.presheaf
  intro U hxU
  apply ConcreteCategory.hom_ext
  intro m
  obtain ⟨V, hxV, rV, hr⟩ :=
    TopCat.Presheaf.exists_germ_eq O.obj r
  let W : Opens X := U ⊓ V
  let hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW : O.obj.obj (Opposite.op W) :=
    O.obj.map (homOfLE (show W ≤ V from inf_le_right)).op rV
  have hrW :
      TopCat.Presheaf.germ O.obj W x hxW rW = r := by
    dsimp [rW]
    rw [TopCat.Presheaf.germ_res_apply]
    simpa using hr
  let mU : F.val.obj (Opposite.op U) := m
  let mW : F.val.obj (Opposite.op W) :=
    F.val.map (homOfLE (show W ≤ U from inf_le_left)).op mU
  let mW0 : F.val.presheaf.obj (Opposite.op W) :=
    F.val.presheaf.map (homOfLE (show W ≤ U from inf_le_left)).op m
  have hmW0 : mW0 = mW := by
    dsimp [mW0, mW, mU]
    rfl
  have hmW :
      TopCat.Presheaf.germ F.val.presheaf W x hxW mW0 =
        TopCat.Presheaf.germ F.val.presheaf U x hxU m := by
    simpa only [mW0] using
      (TopCat.Presheaf.germ_res_apply F.val.presheaf
        (homOfLE (show W ≤ U from inf_le_left)) x hxW m)
  rw [← hrW]
  simp only [ConcreteCategory.comp_apply]
  rw [← hmW]
  rw [hmW0]
  change
    (TopCat.Presheaf.germ O.obj W x hxW rW) •
        moduleStalkAddMap φ x
          (TopCat.Presheaf.germ F.val.presheaf W x hxW mW) =
      moduleStalkAddMap φ x
        ((TopCat.Presheaf.germ O.obj W x hxW rW) •
          TopCat.Presheaf.germ F.val.presheaf W x hxW mW)
  let φAdd : F.val.presheaf ⟶ G.val.presheaf :=
    (PresheafOfModules.toPresheaf O.obj).map φ.val
  have hmap_section (n : F.val.obj (Opposite.op W)) :
      moduleStalkAddMap φ x
          (TopCat.Presheaf.germ F.val.presheaf W x hxW n) =
        TopCat.Presheaf.germ G.val.presheaf W x hxW
          (φ.val.app (Opposite.op W) n) := by
    let n0 : F.val.presheaf.obj (Opposite.op W) := n
    let p0 : G.val.presheaf.obj (Opposite.op W) :=
      φ.val.app (Opposite.op W) n
    change
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φAdd
          (TopCat.Presheaf.germ F.val.presheaf W x hxW n0) =
        TopCat.Presheaf.germ G.val.presheaf W x hxW p0
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl
  have hsmulF :
      (TopCat.Presheaf.germ O.obj W x hxW rW) •
          TopCat.Presheaf.germ F.val.presheaf W x hxW mW =
        TopCat.Presheaf.germ F.val.presheaf W x hxW (rW • mW) := by
    exact (PresheafOfModules.germ_ringCat_smul F.val x W hxW rW mW).symm
  have hsmulG :
      (TopCat.Presheaf.germ O.obj W x hxW rW) •
          TopCat.Presheaf.germ G.val.presheaf W x hxW
            (φ.val.app (Opposite.op W) mW) =
        TopCat.Presheaf.germ G.val.presheaf W x hxW
          (rW • φ.val.app (Opposite.op W) mW) := by
    exact (PresheafOfModules.germ_ringCat_smul G.val x W hxW rW
      (φ.val.app (Opposite.op W) mW)).symm
  rw [hmap_section mW, hsmulF, hmap_section (rW • mW)]
  rw [(φ.val.app (Opposite.op W)).hom.map_smul]
  rw [← hsmulG]
  

/-- The stalk functor on sheaves of `O`-modules, with its canonical stalk
module structure. -/
noncomputable def moduleStalkFunctor {X : TopCat.{v}} (O : RingSheaf X)
    (x : X) :
    Mod O ⥤ ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) where
  obj F :=
    ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x))
  map φ := ModuleCat.homMk (moduleStalkAddMap φ x) (moduleStalkAddMap_smul φ x)
  map_id := by
    intro F
    apply (forget₂ _ AddCommGrpCat).map_injective
    change moduleStalkAddMap (𝟙 F) x = 𝟙 _
    dsimp [moduleStalkAddMap]
    have h_id :
        (PresheafOfModules.toPresheaf O.obj).map (𝟙 F.val) =
          𝟙 F.val.presheaf := by
      ext U s
      rfl
    have h_stalk :=
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_id F.val.presheaf
    rw [h_id, h_stalk]
    rfl
  map_comp := by
    intro F G H φ ψ
    apply (forget₂ _ AddCommGrpCat).map_injective
    change moduleStalkAddMap (φ ≫ ψ) x =
      moduleStalkAddMap φ x ≫ moduleStalkAddMap ψ x
    dsimp [moduleStalkAddMap]
    let φAdd : F.val.presheaf ⟶ G.val.presheaf :=
      (PresheafOfModules.toPresheaf O.obj).map φ.val
    let ψAdd : G.val.presheaf ⟶ H.val.presheaf :=
      (PresheafOfModules.toPresheaf O.obj).map ψ.val
    have hφ :
        (PresheafOfModules.toPresheaf O.obj).map φ.val = φAdd := by
      rfl
    have hψ :
        (PresheafOfModules.toPresheaf O.obj).map ψ.val = ψAdd := by
      rfl
    rw [Functor.map_comp, hφ, hψ]
    exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_comp φAdd ψAdd

/-- Data expressing functoriality of the module-valued skyscraper. -/
structure ModuleSkyscraperFunctorData {X : TopCat.{v}} (O : RingSheaf X)
    (x : X) where
  functor : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) ⥤ Mod O
  obj_iso : ∀ A,
    Nonempty (functor.obj A ≅ moduleSkyscraperSheaf O x A)

/-- Existence of the module-valued skyscraper functor. -/
theorem exists_moduleSkyscraperSheafFunctor {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    Nonempty (ModuleSkyscraperFunctorData O x) := by
  classical
  let D := fun A : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) =>
    Classical.choice (exists_moduleSkyscraperSheaf O x A)
  let e := fun A => Classical.choice (D A).underlying_iso
  let p := fun A => Classical.choice (D A).stalk_at_support
  let c := fun A : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) =>
    skyscraperPresheafStalkOfSpecializes x
      (AddCommGrpCat.of (↑A)) (specializes_refl x)
  let e' : ∀ A : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x),
      (D A).sheaf.val.presheaf ≅
        skyscraperPresheaf x (AddCommGrpCat.of (↑A)) := fun A => by
    simpa [abelianSkyscraperSheaf, skyscraperSheaf] using e A
  let S : AddCommGrpCat ⥤ TopCat.Presheaf AddCommGrpCat X :=
    skyscraperPresheafFunctor x
  let eS : ∀ A : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x),
      (D A).sheaf.val.presheaf ≅ S.obj (AddCommGrpCat.of (↑A)) := fun A => by
    simpa [S] using e' A
  let cS : ∀ A : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x),
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj
          (S.obj (AddCommGrpCat.of (↑A))) ≅ AddCommGrpCat.of (↑A) :=
    fun A => by
      simpa [S, TopCat.Presheaf.stalkFunctor_obj] using c A
  let p' := fun A =>
    (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
      AddCommGrpCat).mapIso (p A)
  let pF : ∀ A : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x),
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj
          (D A).sheaf.val.presheaf ≅ AddCommGrpCat.of (↑A) := fun A => by
    change
      AddCommGrpCat.of
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
          (D A).sheaf.val.presheaf x) ≅
        AddCommGrpCat.of (↑A)
    exact p' A
  let q := fun A =>
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapIso (eS A) ≪≫ cS A
  have htypes (A : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
      (D A).sheaf = moduleSkyscraperSheaf O x A := by
    rfl
  let k := fun (A B : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
      (f : A ⟶ B) =>
    (q A).inv ≫ (pF A).hom ≫
      (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
        AddCommGrpCat).map f ≫ (pF B).inv ≫ (q B).hom
  let alpha := fun (A B : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
      (f : A ⟶ B) =>
    (eS A).hom ≫ S.map (k A B f) ≫ (eS B).inv
  have germ_injective (B : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
      (U : Opens X) (hxU : x ∈ U) :
      Function.Injective (ConcreteCategory.hom
        (TopCat.Presheaf.germ (D B).sheaf.val.presheaf U x hxU)) := by
    intro s t hst
    let eU :
      (skyscraperPresheaf x (AddCommGrpCat.of (↑B))).obj
            (Opposite.op U) ≅ AddCommGrpCat.of (↑B) :=
      { hom := eqToHom (by
          simp [skyscraperPresheaf_obj, hxU])
        inv := eqToHom (by
          simp [skyscraperPresheaf_obj, hxU])
        hom_inv_id := by simp
        inv_hom_id := by simp }
    have hst'' :
        (ConcreteCategory.hom
            (TopCat.Presheaf.germ
              (skyscraperPresheaf x (AddCommGrpCat.of (↑B))) U x hxU))
            ((ConcreteCategory.hom ((e' B).hom.app (Opposite.op U))) s) =
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ
              (skyscraperPresheaf x (AddCommGrpCat.of (↑B))) U x hxU))
            ((ConcreteCategory.hom ((e' B).hom.app (Opposite.op U))) t) := by
      calc
        _ = (ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (e' B).hom))
              ((ConcreteCategory.hom
                (TopCat.Presheaf.germ (D B).sheaf.val.presheaf U x hxU)) s) := by
          exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
            (e' B).hom s).symm
        _ = (ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (e' B).hom))
              ((ConcreteCategory.hom
                (TopCat.Presheaf.germ (D B).sheaf.val.presheaf U x hxU)) t) := by
          exact congrArg (fun z =>
            (ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (e' B).hom)) z) hst
        _ = _ := by
          exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
            (e' B).hom t
    have hcU :
        TopCat.Presheaf.germ
            (skyscraperPresheaf x (AddCommGrpCat.of (↑B)))
            U x hxU ≫ (c B).hom =
          eU.hom := by
      change
        TopCat.Presheaf.germ
            (skyscraperPresheaf x (AddCommGrpCat.of (↑B))) U x hxU ≫
          (skyscraperPresheafStalkOfSpecializes x
            (AddCommGrpCat.of (↑B)) (specializes_refl x)).hom =
          eqToHom (if_pos hxU)
      have hh :=
        (germ_skyscraperPresheafStalkOfSpecializes_hom
          (p₀ := x) (A := AddCommGrpCat.of (↑B))
          (specializes_refl x) U hxU)
      simpa [eU, c, skyscraperPresheaf_obj, hxU] using hh
    have hst''' := congrArg (fun z => (ConcreteCategory.hom (c B).hom) z) hst''
    have hst'''' :
        (ConcreteCategory.hom eU.hom)
            ((ConcreteCategory.hom ((e' B).hom.app (Opposite.op U))) s) =
          (ConcreteCategory.hom eU.hom)
            ((ConcreteCategory.hom ((e' B).hom.app (Opposite.op U))) t) := by
      calc
        _ = (ConcreteCategory.hom (c B).hom)
              ((ConcreteCategory.hom
                (TopCat.Presheaf.germ
                  (skyscraperPresheaf x (AddCommGrpCat.of (↑B)))
                  U x hxU))
                ((ConcreteCategory.hom ((e' B).hom.app (Opposite.op U))) s)) := by
          change
            (ConcreteCategory.hom
              ((e' B).hom.app (Opposite.op U) ≫ eU.hom)) s =
              (ConcreteCategory.hom
                ((e' B).hom.app (Opposite.op U) ≫
                  (TopCat.Presheaf.germ
                    (skyscraperPresheaf x (AddCommGrpCat.of (↑B)))
                    U x hxU) ≫ (c B).hom)) s
          have hhcomp := congrArg (fun z =>
            (e' B).hom.app (Opposite.op U) ≫ z) hcU
          simpa only [ConcreteCategory.comp_apply] using
            congrArg (fun z => (ConcreteCategory.hom z) s) hhcomp.symm
        _ = _ := by
          simpa only [ConcreteCategory.comp_apply] using hst'''
        _ = (ConcreteCategory.hom eU.hom)
                ((ConcreteCategory.hom ((e' B).hom.app (Opposite.op U))) t) := by
          change
            (ConcreteCategory.hom
              ((e' B).hom.app (Opposite.op U) ≫
                (TopCat.Presheaf.germ
                  (skyscraperPresheaf x (AddCommGrpCat.of (↑B)))
                  U x hxU) ≫ (c B).hom)) t =
              (ConcreteCategory.hom (eU.hom))
                ((ConcreteCategory.hom ((e' B).hom.app (Opposite.op U))) t)
          have hhcomp := congrArg (fun z =>
            (e' B).hom.app (Opposite.op U) ≫ z) hcU
          simpa only [ConcreteCategory.comp_apply] using
            congrArg (fun z => (ConcreteCategory.hom z) t) hhcomp
    have hst''''' :
        (ConcreteCategory.hom ((e' B).hom.app (Opposite.op U))) s =
          (ConcreteCategory.hom ((e' B).hom.app (Opposite.op U))) t := by
      have hz := congrArg
        (fun z => (ConcreteCategory.hom eU.inv) z) hst''''
      change
        (ConcreteCategory.hom (eU.hom ≫ eU.inv))
            ((ConcreteCategory.hom ((e' B).hom.app (Opposite.op U))) s) =
        (ConcreteCategory.hom (eU.hom ≫ eU.inv))
            ((ConcreteCategory.hom ((e' B).hom.app (Opposite.op U))) t) at hz
      rw [Iso.hom_inv_id] at hz
      exact hz
    have hz := congrArg
      (fun z => (ConcreteCategory.hom ((e' B).app (Opposite.op U)).inv) z)
      hst'''''
    change
      (ConcreteCategory.hom
        ((e' B).hom.app (Opposite.op U) ≫
          (e' B).inv.app (Opposite.op U))) s =
        (ConcreteCategory.hom
          ((e' B).hom.app (Opposite.op U) ≫
            (e' B).inv.app (Opposite.op U))) t at hz
    rw [(e' B).hom_inv_id_app (Opposite.op U)] at hz
    exact hz
  have hcMap (A B : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
      (g : AddCommGrpCat.of (↑A) ⟶ AddCommGrpCat.of (↑B)) :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (S.map g) = (cS A).hom ≫ g ≫ (cS B).inv := by
    let : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
    apply (cancel_mono (cS B).hom).1
    have hnat :=
      (skyscraperPresheafStalkAdjunction (p₀ := x)).counit.naturality g
    change
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (S.map g) ≫ (cS B).hom = (cS A).hom ≫ g at hnat
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hnat
  have hαStalk (A B : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) (f : A ⟶ B) :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (alpha A B f) =
        (pF A).hom ≫
          (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
            AddCommGrpCat).map f ≫ (pF B).inv := by
    dsimp only [alpha]
    rw [(TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_comp
          ((eS A).hom) (S.map (k A B f) ≫ (eS B).inv),
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_comp
          (S.map (k A B f)) ((eS B).inv), hcMap]
    have hqA :
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (eS A).hom ≫
            (cS A).hom = (q A).hom := by
      change
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (eS A).hom ≫
            (cS A).hom =
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapIso (eS A) ≪≫
            cS A).hom
      rfl
    have hqB :
        (cS B).inv ≫
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (eS B).inv =
          (q B).inv := by
      change
        (cS B).inv ≫
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (eS B).inv =
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapIso (eS B) ≪≫
            cS B).inv
      rfl
    calc
      _ =
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (eS A).hom ≫
            (cS A).hom) ≫ k A B f ≫ (cS B).inv ≫
              (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (eS B).inv := by
        simp only [Category.assoc]
      _ = (q A).hom ≫ k A B f ≫ (cS B).inv ≫
              (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (eS B).inv := by
        rw [hqA]
      _ = (q A).hom ≫ k A B f ≫ (q B).inv := by
        rw [hqB]
      _ = _ := by
        simp only [k, Category.assoc]
        rw [(q A).hom_inv_id_assoc]
        change
          ((pF A).hom ≫
              (forget₂ (ModuleCat
                (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
                AddCommGrpCat).map f ≫ (pF B).inv ≫ (q B).hom) ≫
            (q B).inv =
          (pF A).hom ≫
            (forget₂ (ModuleCat
              (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
              AddCommGrpCat).map f ≫ (pF B).inv
        calc
          _ = (pF A).hom ≫
                ((forget₂ (ModuleCat
                  (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
                  AddCommGrpCat).map f ≫ (pF B).inv) ≫
                  ((q B).hom ≫ (q B).inv) := by
            simp only [Category.assoc]
          _ = _ := by
            rw [(q B).hom_inv_id, Category.comp_id]
  have hk_id (A : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
      k A A (𝟙 A) = 𝟙 (AddCommGrpCat.of (↑A)) := by
    simp only [k]
    rw [(forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) O.obj x))
      AddCommGrpCat).map_id]
    change (q A).inv ≫ (pF A).hom ≫
      (𝟙 (AddCommGrpCat.of ↑A)) ≫ (pF A).inv ≫ (q A).hom = _
    simp only [← Category.assoc, Category.comp_id,
      Iso.hom_inv_id, Iso.inv_hom_id]
  have hk_comp (A B C : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
      (f : A ⟶ B) (g : B ⟶ C) :
      k A C (f ≫ g) = k A B f ≫ k B C g := by
    simp only [k, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  have hα_id (A : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
      alpha A A (𝟙 A) = 𝟙 _ := by
    dsimp [alpha]
    rw [hk_id A, S.map_id]
    simp
  have hα_comp (A B C : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
      (f : A ⟶ B) (g : B ⟶ C) :
      alpha A C (f ≫ g) = alpha A B f ≫ alpha B C g := by
    dsimp [alpha]
    rw [hk_comp A B C f g, S.map_comp]
    simp [Category.assoc]
  let F : ModuleCat.{v}
      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) ⥤ Mod O :=
    { obj := fun A => (D A).sheaf
      map := fun {A B} f =>
        ⟨PresheafOfModules.homMk (alpha A B f) (by
          intro U r m
          by_cases hxU : x ∈ U.unop
          · apply germ_injective B U.unop hxU
            let μ := (p A).hom ≫ f ≫ (p B).inv
            let s : ↑(TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) :=
              (ConcreteCategory.hom
                (TopCat.Presheaf.germ O.obj U.unop x hxU)) r
            let ma : ↑(ModuleCat.of
                (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
                (TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
                  (D A).sheaf.val.presheaf x)) :=
              (ConcreteCategory.hom
                (TopCat.Presheaf.germ
                  (D A).sheaf.val.presheaf U.unop x hxU)) m
            have hμ :
                (pF A).hom ≫
                    (forget₂ (ModuleCat
                      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
                      AddCommGrpCat).map f ≫ (pF B).inv =
                  (forget₂ (ModuleCat
                    (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
                    AddCommGrpCat).map μ := by
              rfl
            calc
              _ = (show ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
                    (D B).sheaf.val.presheaf x) from
                  (ConcreteCategory.hom
                    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
                      (alpha A B f)))
                    ((ConcreteCategory.hom
                      (TopCat.Presheaf.germ
                        (D A).sheaf.val.presheaf U.unop x hxU)) (r • m))) := by
                symm
                exact TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop x hxU
                  (alpha A B f) (r • m)
              _ = (show ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
                    (D B).sheaf.val.presheaf x) from
                  (ConcreteCategory.hom
                    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
                      (alpha A B f)))
                    (s • ma)) := by
                rw [PresheafOfModules.germ_ringCat_smul]
              _ = (show ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
                    (D B).sheaf.val.presheaf x) from
                  (ConcreteCategory.hom
                    ((pF A).hom ≫
                      (forget₂ (ModuleCat
                        (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
                        AddCommGrpCat).map f ≫ (pF B).inv))
                    (s • ma)) := by
                rw [hαStalk A B f]
              _ = (show ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
                    (D B).sheaf.val.presheaf x) from
                  (ConcreteCategory.hom
                    ((forget₂ (ModuleCat
                      (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
                      AddCommGrpCat).map μ)) (s • ma)) := by
                rfl
              _ = s •
                  (show ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
                      (D B).sheaf.val.presheaf x) from
                    (ConcreteCategory.hom
                      ((forget₂ (ModuleCat
                        (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
                        AddCommGrpCat).map μ)) ma) := by
                change μ.hom (s • ma) = s • μ.hom ma
                exact μ.hom.map_smul s ma
              _ = s •
                  (show ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
                      (D B).sheaf.val.presheaf x) from
                    (ConcreteCategory.hom
                      ((pF A).hom ≫
                        (forget₂ (ModuleCat
                          (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
                          AddCommGrpCat).map f ≫ (pF B).inv)) ma) := by
                rfl
              _ = s •
                  (show ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
                      (D B).sheaf.val.presheaf x) from
                    (ConcreteCategory.hom
                      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
                        (alpha A B f))) ma) := by
                have hα_apply := congrArg
                  (fun h => (ConcreteCategory.hom h) ma) (hαStalk A B f)
                exact congrArg (fun z => s • z) hα_apply.symm
              _ = (ConcreteCategory.hom
                    (TopCat.Presheaf.germ
                      (D B).sheaf.val.presheaf U.unop x hxU))
                    (r • (ConcreteCategory.hom ((alpha A B f).app U)) m) := by
                dsimp [s, ma]
                have hstalk :
                    (show ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
                        (D B).sheaf.val.presheaf x) from
                      (ConcreteCategory.hom
                        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
                          (alpha A B f)))
                        ((ConcreteCategory.hom
                          (TopCat.Presheaf.germ
                            (D A).sheaf.val.presheaf U.unop x hxU)) m)) =
                      (ConcreteCategory.hom
                        (TopCat.Presheaf.germ
                          (D B).sheaf.val.presheaf U.unop x hxU))
                        ((alpha A B f).app U m) := by
                  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop x hxU
                    (alpha A B f) m
                calc
                  _ = (ConcreteCategory.hom
                      (TopCat.Presheaf.germ O.obj U.unop x hxU)) r •
                      (ConcreteCategory.hom
                        (TopCat.Presheaf.germ
                          (D B).sheaf.val.presheaf U.unop x hxU))
                        ((alpha A B f).app U m) := by
                    congr 1
                  _ = _ := PresheafOfModules.germ_ringCat_smul
                    (D B).sheaf.val x U.unop hxU r
                      ((alpha A B f).app U m) |>.symm
          · let eTop :
                (D B).sheaf.val.presheaf.obj U ≅ ⊤_ AddCommGrpCat :=
              (e' B).app U ≪≫ eqToIso (by
                simp [skyscraperPresheaf_obj, hxU])
            let : Subsingleton
                (↑((D B).sheaf.val.presheaf.obj U)) := by
              exact AddCommGrpCat.subsingleton_of_isZero
                ((isZero_zero AddCommGrpCat).of_iso
                  (eTop ≪≫ (HasZeroObject.zeroIsoTerminal :
                    (0 : AddCommGrpCat) ≅ ⊤_ AddCommGrpCat).symm))
            exact Subsingleton.elim _ _)⟩
      map_id := by
        intro A
        apply SheafOfModules.hom_ext
        apply (PresheafOfModules.toPresheaf O.obj).map_injective
        ext U m
        change (ConcreteCategory.hom ((alpha A A (𝟙 A)).app U)) m = m
        rw [hα_id A]
        rfl
      map_comp := by
        intro A B C f g
        apply SheafOfModules.hom_ext
        apply (PresheafOfModules.toPresheaf O.obj).map_injective
        ext U m
        change (ConcreteCategory.hom ((alpha A C (f ≫ g)).app U)) m =
          (ConcreteCategory.hom ((alpha B C g).app U))
            ((ConcreteCategory.hom ((alpha A B f).app U)) m)
        rw [hα_comp A B C f g]
        rfl }
  refine ⟨{ functor := F, obj_iso := ?_ }⟩
  intro A
  refine ⟨?_⟩
  change (D A).sheaf ≅ moduleSkyscraperSheaf O x A
  exact eqToIso (htypes A)

/-- A chosen functor from support-stalk modules to module skyscraper sheaves. -/
noncomputable def moduleSkyscraperSheafFunctor {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) ⥤ Mod O :=
  (Classical.choice (exists_moduleSkyscraperSheafFunctor O x)).functor

/-- The chosen module skyscraper functor has the prescribed stalk naturally in
its support-module argument.  This is the module-valued compatibility needed
to lift the additive skyscraper adjunction. -/
theorem exists_moduleSkyscraperSheafFunctor_stalkIso {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    Nonempty (moduleSkyscraperSheafFunctor O x ⋙ moduleStalkFunctor O x ≅ 𝟭 _) := by
  sorry

/-- A sheaf of `O`-modules is a skyscraper sheaf when it is isomorphic to one
with value a module over a support stalk. -/
def IsModuleSkyscraperSheaf {X : TopCat.{v}} (O : RingSheaf X)
    (F : Mod O) : Prop :=
  ∃ x : X,
    ∃ A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x),
      Nonempty (F ≅ moduleSkyscraperSheaf O x A)

/-! ## The stalk calculation -/

/-- Specialization is equivalent to membership in the closure of the support.
-/
theorem skyscraper_specializes_iff_mem_closure {X : TopCat.{v}}
    (x x' : X) : x ⤳ x' ↔ x' ∈ closure ({x} : Set X) :=
  specializes_iff_mem_closure

/-- The generic stalk calculation at a specialization of the support. -/
noncomputable def algebraicSkyscraperStalkOfSpecializes
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (A : C) {x' : X} (h : x ⤳ x') :
    (algebraicSkyscraperPresheaf x A).stalk x' ≅ A := by
  classical
  exact skyscraperPresheafStalkOfSpecializes x A h

/-- The generic stalk calculation away from the closure of the support. -/
noncomputable def algebraicSkyscraperStalkOfNotSpecializes
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (A : C) {x' : X} (h : ¬x ⤳ x') :
    (algebraicSkyscraperPresheaf x A).stalk x' ≅ terminal C := by
  classical
  exact skyscraperPresheafStalkOfNotSpecializes x A h

/-- The generic stalk is the prescribed value at every point in the closure of
the support. -/
noncomputable def algebraicSkyscraperStalkOfMemClosure
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (A : C) {x' : X}
    (h : x' ∈ closure ({x} : Set X)) :
    (algebraicSkyscraperSheaf x A).presheaf.stalk x' ≅ A := by
  exact algebraicSkyscraperStalkOfSpecializes x A
    ((skyscraper_specializes_iff_mem_closure x x').2 h)

/-- The generic stalk is terminal at every point outside the closure of the
support. -/
noncomputable def algebraicSkyscraperStalkOfNotMemClosure
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (A : C) {x' : X}
    (h : x' ∉ closure ({x} : Set X)) :
    (algebraicSkyscraperSheaf x A).presheaf.stalk x' ≅ terminal C := by
  apply algebraicSkyscraperStalkOfNotSpecializes x A
  intro hs
  exact h ((skyscraper_specializes_iff_mem_closure x x').1 hs)

/-- The set-valued stalk calculation at and away from the closure. -/
noncomputable def setSkyscraperStalkOfSpecializes
    {X : TopCat.{v}} (x : X) (A : Type v) {x' : X} (h : x ⤳ x') :
    (setSkyscraperPresheaf x A).stalk x' ≅ A := by
  classical
  exact skyscraperPresheafStalkOfSpecializes x A h

noncomputable def setSkyscraperStalkOfNotSpecializes
    {X : TopCat.{v}} (x : X) (A : Type v) {x' : X} (h : ¬x ⤳ x') :
    (setSkyscraperPresheaf x A).stalk x' ≅ terminal (Type v) := by
  classical
  exact skyscraperPresheafStalkOfNotSpecializes x A h

noncomputable def setSkyscraperStalkOfMemClosure
    {X : TopCat.{v}} (x : X) (A : Type v) {x' : X}
    (h : x' ∈ closure ({x} : Set X)) :
    (setSkyscraperSheaf x A).presheaf.stalk x' ≅ A := by
  exact setSkyscraperStalkOfSpecializes x A
    ((skyscraper_specializes_iff_mem_closure x x').2 h)

noncomputable def setSkyscraperStalkOfNotMemClosure
    {X : TopCat.{v}} (x : X) (A : Type v) {x' : X}
    (h : x' ∉ closure ({x} : Set X)) :
    (setSkyscraperSheaf x A).presheaf.stalk x' ≅ terminal (Type v) := by
  apply setSkyscraperStalkOfNotSpecializes x A
  intro hs
  exact h ((skyscraper_specializes_iff_mem_closure x x').1 hs)

/-- The abelian-group stalk calculation at and away from the closure. -/
noncomputable def abelianSkyscraperStalkOfSpecializes
    {X : TopCat.{v}} (x : X) (A : AddCommGrpCat.{v}) {x' : X}
    (h : x ⤳ x') :
    (abelianSkyscraperPresheaf x A).stalk x' ≅ A := by
  classical
  exact skyscraperPresheafStalkOfSpecializes x A h

noncomputable def abelianSkyscraperStalkOfNotSpecializes
    {X : TopCat.{v}} (x : X) (A : AddCommGrpCat.{v}) {x' : X}
    (h : ¬x ⤳ x') :
    (abelianSkyscraperPresheaf x A).stalk x' ≅ terminal AddCommGrpCat := by
  classical
  exact skyscraperPresheafStalkOfNotSpecializes x A h

noncomputable def abelianSkyscraperStalkOfMemClosure
    {X : TopCat.{v}} (x : X) (A : AddCommGrpCat.{v}) {x' : X}
    (h : x' ∈ closure ({x} : Set X)) :
    (abelianSkyscraperSheaf x A).presheaf.stalk x' ≅ A := by
  exact abelianSkyscraperStalkOfSpecializes x A
    ((skyscraper_specializes_iff_mem_closure x x').2 h)

noncomputable def abelianSkyscraperStalkOfNotMemClosure
    {X : TopCat.{v}} (x : X) (A : AddCommGrpCat.{v}) {x' : X}
    (h : x' ∉ closure ({x} : Set X)) :
    (abelianSkyscraperSheaf x A).presheaf.stalk x' ≅ terminal AddCommGrpCat := by
  apply abelianSkyscraperStalkOfNotSpecializes x A
  intro hs
  exact h ((skyscraper_specializes_iff_mem_closure x x').1 hs)

/-- At the support, a module skyscraper has its prescribed stalk module. -/
theorem moduleSkyscraperStalkAtSupport
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    Nonempty ((moduleStalkFunctor O x).obj
      (moduleSkyscraperSheaf O x A) ≅ A) := by
  exact (Classical.choice (exists_moduleSkyscraperSheaf O x A)).stalk_at_support

/-- At a specialization of the support, the module stalk is the prescribed
module with scalars restricted along the canonical stalk specialization map.
-/
theorem moduleSkyscraperStalkAtSpecialization
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
    {x' : X} (h : x ⤳ x') :
    Nonempty ((moduleStalkFunctor O x').obj
      (moduleSkyscraperSheaf O x A) ≅
      (ModuleCat.restrictScalars
        (TopCat.Presheaf.stalkSpecializes O.obj h).hom).obj A) := by
  let D := Classical.choice (exists_moduleSkyscraperSheaf O x A)
  let fR := (TopCat.Presheaf.stalkSpecializes O.obj h).hom
  let φAdd := TopCat.Presheaf.stalkSpecializes D.sheaf.val.presheaf h
  let φAdd' :
      (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x'))
        AddCommGrpCat).obj ((moduleStalkFunctor O x').obj D.sheaf) ⟶
      (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x'))
        AddCommGrpCat).obj
        ((ModuleCat.restrictScalars fR).obj ((moduleStalkFunctor O x).obj D.sheaf)) :=
    φAdd
  let φ : (moduleStalkFunctor O x').obj D.sheaf ⟶
      (ModuleCat.restrictScalars fR).obj ((moduleStalkFunctor O x).obj D.sheaf) :=
    ModuleCat.homMk φAdd' (by
      intro r
      apply ConcreteCategory.hom_ext
      intro m
      dsimp [φAdd', moduleStalkFunctor]
      change (ConcreteCategory.hom
          (((ModuleCat.restrictScalars fR).obj ((moduleStalkFunctor O x).obj D.sheaf)).smul r))
          (φAdd m) =
        φAdd (ConcreteCategory.hom (((moduleStalkFunctor O x').obj D.sheaf).smul r) m)
      obtain ⟨U, hyU, rU, hrU⟩ :=
        TopCat.Presheaf.exists_germ_eq O.obj r
      obtain ⟨V, hyV, mV, hmV⟩ :=
        TopCat.Presheaf.exists_germ_eq D.sheaf.val.presheaf m
      let W : Opens X := U ⊓ V
      let hyW : x' ∈ W := ⟨hyU, hyV⟩
      let hxW : x ∈ W := ⟨h.mem_open U.isOpen hyU, h.mem_open V.isOpen hyV⟩
      let rW : O.obj.obj (Opposite.op W) :=
        O.obj.map (homOfLE (show W ≤ U from inf_le_left)).op rU
      let mW : D.sheaf.val.obj (Opposite.op W) :=
        D.sheaf.val.map (homOfLE (show W ≤ V from inf_le_right)).op mV
      let mW0 : D.sheaf.val.presheaf.obj (Opposite.op W) :=
        D.sheaf.val.presheaf.map
          (homOfLE (show W ≤ V from inf_le_right)).op mV
      have hmW0 : mW0 = mW := by
        dsimp [mW0, mW]
        rfl
      have hrW :
          TopCat.Presheaf.germ O.obj W x' hyW rW = r := by
        dsimp [rW]
        rw [TopCat.Presheaf.germ_res_apply]
        simpa using hrU
      have hmW :
          TopCat.Presheaf.germ D.sheaf.val.presheaf W x' hyW mW0 = m := by
        rw [TopCat.Presheaf.germ_res_apply]
        simpa using hmV
      rw [← hrW, ← hmW]
      have hφm :
          (ConcreteCategory.hom φAdd)
              ((ConcreteCategory.hom
                (TopCat.Presheaf.germ D.sheaf.val.presheaf W x' hyW)) mW0) =
            (ConcreteCategory.hom
              (TopCat.Presheaf.germ D.sheaf.val.presheaf W x hxW)) mW0 := by
        have hh := congrArg (fun k => (ConcreteCategory.hom k) mW0)
          (TopCat.Presheaf.germ_stalkSpecializes
            D.sheaf.val.presheaf hyW h)
        simpa only [φAdd, ConcreteCategory.comp_apply] using hh
      have hfr :
          fR ((ConcreteCategory.hom
            (TopCat.Presheaf.germ O.obj W x' hyW)) rW) =
            (ConcreteCategory.hom
              (TopCat.Presheaf.germ O.obj W x hxW)) rW := by
        have hh := congrArg (fun k => (ConcreteCategory.hom k) rW)
          (TopCat.Presheaf.germ_stalkSpecializes O.obj hyW h)
        simpa only [fR, ConcreteCategory.comp_apply] using hh
      have hsmul' :
          (ConcreteCategory.hom
            (((moduleStalkFunctor O x').obj D.sheaf).smul
              ((ConcreteCategory.hom
                (TopCat.Presheaf.germ O.obj W x' hyW)) rW)))
            ((ConcreteCategory.hom
              (TopCat.Presheaf.germ D.sheaf.val.presheaf W x' hyW)) mW0) =
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ D.sheaf.val.presheaf W x' hyW))
            (rW • mW) := by
        rw [hmW0]
        exact (PresheafOfModules.germ_ringCat_smul D.sheaf.val x' W hyW rW mW).symm
      rw [hφm]
      dsimp [moduleStalkFunctor]
      change
        (ConcreteCategory.hom
          (((moduleStalkFunctor O x).obj D.sheaf).smul
            (fR ((ConcreteCategory.hom
              (TopCat.Presheaf.germ O.obj W x' hyW)) rW))))
          ((ConcreteCategory.hom
            (TopCat.Presheaf.germ D.sheaf.val.presheaf W x hxW)) mW0) =
        (ConcreteCategory.hom φAdd)
          ((ConcreteCategory.hom
            (((moduleStalkFunctor O x').obj D.sheaf).smul
              ((ConcreteCategory.hom
                (TopCat.Presheaf.germ O.obj W x' hyW)) rW)))
            ((ConcreteCategory.hom
              (TopCat.Presheaf.germ D.sheaf.val.presheaf W x' hyW)) mW0))
      rw [hfr, hsmul']
      have hφaction :
          (ConcreteCategory.hom φAdd)
              ((ConcreteCategory.hom
                (TopCat.Presheaf.germ D.sheaf.val.presheaf W x' hyW))
                (rW • mW)) =
            (ConcreteCategory.hom
              (TopCat.Presheaf.germ D.sheaf.val.presheaf W x hxW))
              (rW • mW) := by
        have hh := congrArg (fun k => (ConcreteCategory.hom k) (rW • mW))
          (TopCat.Presheaf.germ_stalkSpecializes
            D.sheaf.val.presheaf hyW h)
        change (ConcreteCategory.hom
          (TopCat.Presheaf.germ D.sheaf.val.presheaf W x' hyW ≫ φAdd))
            (rW • mW) =
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ D.sheaf.val.presheaf W x hxW))
            (rW • mW) at hh
        exact hh
      rw [hφaction]
      exact (PresheafOfModules.germ_ringCat_smul D.sheaf.val x W hxW rW mW).symm
    )
  let : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  let cY := skyscraperPresheafStalkOfSpecializes
    (p₀ := x) (A := AddCommGrpCat.of (↑A)) h
  let cX := skyscraperPresheafStalkOfSpecializes
    (p₀ := x) (A := AddCommGrpCat.of (↑A)) (specializes_refl x)
  have hSpec :
      TopCat.Presheaf.stalkSpecializes
          (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) h =
        (cY.hom ≫ cX.inv) := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hyU
    apply (cancel_mono cX.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc]
    rw [TopCat.Presheaf.germ_stalkSpecializes]
    rw [show (TopCat.Presheaf.germ
        (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) U x' hyU) ≫ cY.hom =
        eqToHom (if_pos (h.mem_open U.isOpen hyU)) by
          dsimp [cY]
          exact germ_skyscraperPresheafStalkOfSpecializes_hom
            (p₀ := x) (A := AddCommGrpCat.of (↑A)) h U hyU]
    rw [show (TopCat.Presheaf.germ
        (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) U x (h.mem_open U.isOpen hyU)) ≫
          cX.hom =
        eqToHom (if_pos ((specializes_refl x).mem_open U.isOpen
          (h.mem_open U.isOpen hyU))) by
          dsimp [cX]
          exact germ_skyscraperPresheafStalkOfSpecializes_hom
            (p₀ := x) (A := AddCommGrpCat.of (↑A)) (specializes_refl x) U _]
  have : IsIso (TopCat.Presheaf.stalkSpecializes
      (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) h) := by
    rw [hSpec]
    infer_instance
  let e : D.sheaf.val.presheaf ≅
      (skyscraperSheaf x (AddCommGrpCat.of (↑A))).presheaf := by
    simpa [abelianSkyscraperSheaf] using
      (Classical.choice D.underlying_iso)
  let eX :
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) D.sheaf.val.presheaf x ≅
        TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
          (skyscraperSheaf x (AddCommGrpCat.of (↑A))).presheaf x :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapIso e
  let eY :
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) D.sheaf.val.presheaf x' ≅
        TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
          (skyscraperSheaf x (AddCommGrpCat.of (↑A))).presheaf x' :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x').mapIso e
  let cXF :
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
          (skyscraperSheaf x (AddCommGrpCat.of (↑A))).presheaf x ≅
        AddCommGrpCat.of (↑A) := cX
  let cYF :
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
          (skyscraperSheaf x (AddCommGrpCat.of (↑A))).presheaf x' ≅
        AddCommGrpCat.of (↑A) := cY
  have hnat :
      φAdd ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map e.hom =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x').map e.hom ≫
          (skyscraperSheaf x (AddCommGrpCat.of (↑A))).presheaf.stalkSpecializes h := by
    simpa [φAdd] using
      (TopCat.Presheaf.stalkSpecializes_stalkFunctor_map
        (C := AddCommGrpCat.{v}) e.hom h)
  have hSpecF :
      (skyscraperSheaf x (AddCommGrpCat.of (↑A))).presheaf.stalkSpecializes h =
        cYF.hom ≫ cXF.inv := by
    simpa [skyscraperSheaf, cYF, cXF] using hSpec
  set_option backward.isDefEq.respectTransparency false in
  have hφIso : IsIso φAdd := by
    let q := eY ≪≫ cYF ≪≫ cXF.symm ≪≫ eX.symm
    have hq : φAdd = q.hom := by
      apply (cancel_mono eX.hom).1
      simpa [q, eX, eY, hSpecF, Iso.trans_hom, Iso.symm_hom, Category.assoc] using hnat
    have : IsIso φAdd := by
      rw [hq]
      dsimp [q]
      infer_instance
    exact inferInstance
  let := hφIso
  let φIso : (moduleStalkFunctor O x').obj D.sheaf ≅
      (ModuleCat.restrictScalars fR).obj ((moduleStalkFunctor O x).obj D.sheaf) :=
    ModuleCat.isoMk (asIso φAdd) (by
      intro r
      apply ConcreteCategory.hom_ext
      intro m
      exact (φ.hom'.map_smul' r m).symm)
  have hφIso' : φIso.hom = φ := by
    apply (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x'))
      AddCommGrpCat).map_injective
    rfl
  have : IsIso φ := by
    rw [← hφIso']
    infer_instance
  let p : (moduleStalkFunctor O x).obj D.sheaf ≅ A := by
    simpa [moduleStalkFunctor] using (Classical.choice D.stalk_at_support)
  let p' := (ModuleCat.restrictScalars fR).mapIso p
  refine ⟨asIso φ ≪≫ p'⟩

/-- Closure-form version of the module stalk calculation at the support. -/
theorem moduleSkyscraperStalkOfMemClosure
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
    {x' : X} (h : x' ∈ closure ({x} : Set X)) :
    Nonempty ((moduleStalkFunctor O x').obj
      (moduleSkyscraperSheaf O x A) ≅
      (ModuleCat.restrictScalars
        (TopCat.Presheaf.stalkSpecializes O.obj
          ((skyscraper_specializes_iff_mem_closure x x').2 h)).hom).obj A) := by
  exact moduleSkyscraperStalkAtSpecialization O x A
    ((skyscraper_specializes_iff_mem_closure x x').2 h)

/-- Away from the closure of the support, a module skyscraper has zero stalk.
-/
theorem moduleSkyscraperStalkAwayFromClosure
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
    {x' : X} (h : x' ∉ closure ({x} : Set X)) :
    Nonempty ((moduleStalkFunctor O x').obj
      (moduleSkyscraperSheaf O x A) ≅ 0) := by
  apply (Classical.choice (exists_moduleSkyscraperSheaf O x A)).stalk_away
  intro hs
  exact h ((skyscraper_specializes_iff_mem_closure x x').1 hs)

/-! ## The stalk/skyscraper adjunctions -/

/-- The set-valued stalk/skyscraper adjunction. -/
noncomputable def setStalkSkyscraperAdjunction {X : TopCat.{v}} (x : X) :
    (TopCat.Sheaf.forget (Type v) X ⋙
      TopCat.Presheaf.stalkFunctor (Type v) x) ⊣
      setSkyscraperSheafFunctor x := by
  letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  exact stalkSkyscraperSheafAdjunction x

/-- The Hom equivalence for the set-valued adjunction. -/
noncomputable abbrev setStalkSkyscraperHomEquiv {X : TopCat.{v}} (x : X)
    (F : TopCat.Sheaf (Type v) X) (A : Type v) :
    (F.presheaf.stalk x ⟶ A) ≃ (F ⟶ setSkyscraperSheaf x A) :=
  (setStalkSkyscraperAdjunction x).homEquiv F A

/-- The abelian-group stalk/skyscraper adjunction. -/
noncomputable def abelianStalkSkyscraperAdjunction {X : TopCat.{v}}
    (x : X) :
    (TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x) ⊣
      abelianSkyscraperSheafFunctor x := by
  letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  exact stalkSkyscraperSheafAdjunction x

/-- The Hom equivalence for the abelian-group adjunction. -/
noncomputable abbrev abelianStalkSkyscraperHomEquiv {X : TopCat.{v}} (x : X)
    (F : Ab X) (A : AddCommGrpCat.{v}) :
    (F.presheaf.stalk x ⟶ A) ≃
      (F ⟶ abelianSkyscraperSheaf x A) :=
  (abelianStalkSkyscraperAdjunction x).homEquiv F A

/-- The generic algebraic-structure stalk/skyscraper adjunction. -/
noncomputable def algebraicStalkSkyscraperAdjunction
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) :
    (TopCat.Sheaf.forget C X ⋙ TopCat.Presheaf.stalkFunctor C x) ⊣
      algebraicSkyscraperSheafFunctor x := by
  letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  exact stalkSkyscraperSheafAdjunction x

/-- The Hom equivalence for the algebraic-structure adjunction. -/
noncomputable abbrev algebraicStalkSkyscraperHomEquiv
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (F : TopCat.Sheaf C X) (A : C) :
    (F.presheaf.stalk x ⟶ A) ≃
      (F ⟶ algebraicSkyscraperSheaf x A) :=
  (algebraicStalkSkyscraperAdjunction x).homEquiv F A

private noncomputable def moduleHomOfStalkLinear
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    {F D : Mod O}
    {A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)}
    (eD0 : D.val.presheaf ≅
      (abelianSkyscraperSheaf x (AddCommGrpCat.of (↑A))).presheaf)
    (h : F.val.presheaf ⟶ D.val.presheaf)
    (φ : (moduleStalkFunctor O x).obj F ⟶
      (moduleStalkFunctor O x).obj D)
    (hφ : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map h =
      (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
        AddCommGrpCat).map φ) :
    F ⟶ D := by
  letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  let eD : D.val.presheaf ≅ skyscraperPresheaf x (AddCommGrpCat.of (↑A)) := by
    simpa [abelianSkyscraperSheaf, skyscraperSheaf] using eD0
  have germ_injective (U : Opens X) (hxU : x ∈ U) :
      Function.Injective (ConcreteCategory.hom
        (TopCat.Presheaf.germ D.val.presheaf U x hxU)) := by
    intro s t hst
    let eU :
        (skyscraperPresheaf x (AddCommGrpCat.of (↑A))).obj
            (Opposite.op U) ≅ AddCommGrpCat.of (↑A) :=
      { hom := eqToHom (by simp [skyscraperPresheaf_obj, hxU])
        inv := eqToHom (by simp [skyscraperPresheaf_obj, hxU])
        hom_inv_id := by simp
        inv_hom_id := by simp }
    have hst' :
        (ConcreteCategory.hom
            (TopCat.Presheaf.germ
              (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) U x hxU))
            ((ConcreteCategory.hom (eD.hom.app (Opposite.op U))) s) =
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ
              (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) U x hxU))
            ((ConcreteCategory.hom (eD.hom.app (Opposite.op U))) t) := by
      calc
        _ = (ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map eD.hom))
              ((ConcreteCategory.hom
                (TopCat.Presheaf.germ D.val.presheaf U x hxU)) s) := by
          exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
            eD.hom s).symm
        _ = (ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map eD.hom))
              ((ConcreteCategory.hom
                (TopCat.Presheaf.germ D.val.presheaf U x hxU)) t) := by
          exact congrArg (fun z =>
            (ConcreteCategory.hom
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map eD.hom)) z) hst
        _ = _ := by
          exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU eD.hom t
    have hcU :
        TopCat.Presheaf.germ
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) U x hxU ≫
          (skyscraperPresheafStalkOfSpecializes x
            (AddCommGrpCat.of (↑A)) (specializes_refl x)).hom = eU.hom := by
      change
        TopCat.Presheaf.germ
            (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) U x hxU ≫
          (skyscraperPresheafStalkOfSpecializes x
            (AddCommGrpCat.of (↑A)) (specializes_refl x)).hom =
          eqToHom (if_pos hxU)
      have hh :=
        (germ_skyscraperPresheafStalkOfSpecializes_hom
          (p₀ := x) (A := AddCommGrpCat.of (↑A))
          (specializes_refl x) U hxU)
      simpa [eU, skyscraperPresheaf_obj, hxU] using hh
    have hst'' := congrArg (fun z => (ConcreteCategory.hom
      (skyscraperPresheafStalkOfSpecializes x
        (AddCommGrpCat.of (↑A)) (specializes_refl x)).hom) z) hst'
    have hst''' :
        (ConcreteCategory.hom eU.hom)
            ((ConcreteCategory.hom (eD.hom.app (Opposite.op U))) s) =
          (ConcreteCategory.hom eU.hom)
            ((ConcreteCategory.hom (eD.hom.app (Opposite.op U))) t) := by
      calc
        _ = (ConcreteCategory.hom
              (skyscraperPresheafStalkOfSpecializes x
                (AddCommGrpCat.of (↑A)) (specializes_refl x)).hom)
              ((ConcreteCategory.hom
                (TopCat.Presheaf.germ
                  (skyscraperPresheaf x (AddCommGrpCat.of (↑A)))
                  U x hxU))
                ((ConcreteCategory.hom (eD.hom.app (Opposite.op U))) s)) := by
          change
            (ConcreteCategory.hom ((eD.hom.app (Opposite.op U)) ≫ eU.hom)) s =
              (ConcreteCategory.hom
                ((eD.hom.app (Opposite.op U)) ≫
                  TopCat.Presheaf.germ
                    (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) U x hxU ≫
                    (skyscraperPresheafStalkOfSpecializes x
                      (AddCommGrpCat.of (↑A)) (specializes_refl x)).hom)) s
          have hhcomp := congrArg
            (fun z => (eD.hom.app (Opposite.op U)) ≫ z) hcU
          simpa only [ConcreteCategory.comp_apply] using
            congrArg (fun z => (ConcreteCategory.hom z) s) hhcomp.symm
        _ = _ := by
          exact hst''
        _ = (ConcreteCategory.hom eU.hom)
                ((ConcreteCategory.hom (eD.hom.app (Opposite.op U))) t) := by
          change
            (ConcreteCategory.hom
              ((eD.hom.app (Opposite.op U)) ≫
                TopCat.Presheaf.germ
                  (skyscraperPresheaf x (AddCommGrpCat.of (↑A))) U x hxU ≫
                (skyscraperPresheafStalkOfSpecializes x
                  (AddCommGrpCat.of (↑A)) (specializes_refl x)).hom)) t =
              (ConcreteCategory.hom eU.hom)
                ((ConcreteCategory.hom (eD.hom.app (Opposite.op U))) t)
          have hhcomp := congrArg
            (fun z => (eD.hom.app (Opposite.op U)) ≫ z) hcU
          simpa only [ConcreteCategory.comp_apply] using
            congrArg (fun z => (ConcreteCategory.hom z) t) hhcomp
    have hst'''' :
        (ConcreteCategory.hom (eD.hom.app (Opposite.op U))) s =
          (ConcreteCategory.hom (eD.hom.app (Opposite.op U))) t := by
      have hz := congrArg (fun z => (ConcreteCategory.hom eU.inv) z) hst'''
      change
        (ConcreteCategory.hom (eU.hom ≫ eU.inv))
            ((ConcreteCategory.hom (eD.hom.app (Opposite.op U))) s) =
        (ConcreteCategory.hom (eU.hom ≫ eU.inv))
            ((ConcreteCategory.hom (eD.hom.app (Opposite.op U))) t) at hz
      rw [Iso.hom_inv_id] at hz
      exact hz
    have hz := congrArg
      (fun z => (ConcreteCategory.hom ((eD.app (Opposite.op U)).inv)) z)
      hst''''
    change
      (ConcreteCategory.hom
        ((eD.hom.app (Opposite.op U)) ≫ eD.inv.app (Opposite.op U))) s =
        (ConcreteCategory.hom
          ((eD.hom.app (Opposite.op U)) ≫ eD.inv.app (Opposite.op U))) t at hz
    rw [eD.hom_inv_id_app (Opposite.op U)] at hz
    exact hz
  refine ⟨PresheafOfModules.homMk h ?_⟩
  intro U r m
  by_cases hxU : x ∈ U.unop
  · apply germ_injective U.unop hxU
    let s : ↑(TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) :=
      (ConcreteCategory.hom
        (TopCat.Presheaf.germ O.obj U.unop x hxU)) r
    let ma : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
        F.val.presheaf x) :=
      (ConcreteCategory.hom
        (TopCat.Presheaf.germ F.val.presheaf U.unop x hxU)) m
    have h₁ :
        (ConcreteCategory.hom
          (TopCat.Presheaf.germ D.val.presheaf U.unop x hxU))
            (h.app U (r • m)) =
          (ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map h))
            (TopCat.Presheaf.germ F.val.presheaf U.unop x hxU (r • m)) := by
      symm
      exact TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop x hxU h
        (r • m)
    have h₂ :
        (ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map h))
            (TopCat.Presheaf.germ F.val.presheaf U.unop x hxU (r • m)) =
          (ConcreteCategory.hom φ) (s • ma) := by
      rw [hφ, PresheafOfModules.germ_ringCat_smul]
      rfl
    have h₃ :
        (ConcreteCategory.hom φ) (s • ma) =
          (ConcreteCategory.hom
            (((moduleStalkFunctor O x).obj D).smul s))
            ((ConcreteCategory.hom φ) ma) := by
      change φ.hom (s • ma) = s • φ.hom ma
      exact φ.hom.map_smul s ma
    have hφhom : ∀ z,
        (ConcreteCategory.hom φ) z =
          (ConcreteCategory.hom
            ((forget₂ (ModuleCat (TopCat.Presheaf.stalk
              (C := RingCat.{v}) O.obj x)) AddCommGrpCat).map φ)) z := by
      intro z
      rfl
    have h₄ :
        (ConcreteCategory.hom
            (((moduleStalkFunctor O x).obj D).smul s))
            ((ConcreteCategory.hom φ) ma) =
          (ConcreteCategory.hom
            (((moduleStalkFunctor O x).obj D).smul s))
            ((ConcreteCategory.hom
              (TopCat.Presheaf.germ D.val.presheaf U.unop x hxU))
              (h.app U m)) := by
      have hh := TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop x hxU h m
      rw [hφ] at hh
      have hh' := congrArg
        (fun z => (ConcreteCategory.hom
          (((moduleStalkFunctor O x).obj D).smul s)) z) hh
      change
        (ConcreteCategory.hom
          (((moduleStalkFunctor O x).obj D).smul s))
            ((ConcreteCategory.hom φ) ma) =
          (ConcreteCategory.hom
            (((moduleStalkFunctor O x).obj D).smul s))
            ((ConcreteCategory.hom
              (TopCat.Presheaf.germ D.val.presheaf U.unop x hxU))
              (h.app U m)) at hh'
      simpa [ma] using hh'
    have h₅ :
          (ConcreteCategory.hom
            (((moduleStalkFunctor O x).obj D).smul s))
            ((ConcreteCategory.hom
              (TopCat.Presheaf.germ D.val.presheaf U.unop x hxU))
              (h.app U m)) =
          (ConcreteCategory.hom
            (TopCat.Presheaf.germ D.val.presheaf U.unop x hxU))
            (r • h.app U m) := by
      symm
      let m0 : F.val.presheaf.obj U := m
      have hsmul (z : ↑((moduleStalkFunctor O x).obj D)) :
          (ConcreteCategory.hom
            (((moduleStalkFunctor O x).obj D).smul s)) z = s • z := by
        rfl
      have hs :=
        (PresheafOfModules.germ_ringCat_smul D.val x U.unop hxU r
          (h.app U m0))
      exact hs.trans (hsmul _).symm
    exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
  · let eTop : D.val.presheaf.obj U ≅ ⊤_ AddCommGrpCat :=
      eD.app U ≪≫ eqToIso (by simp [skyscraperPresheaf_obj, hxU])
    let : Subsingleton (↑(D.val.presheaf.obj U)) := by
      exact AddCommGrpCat.subsingleton_of_isZero
        ((isZero_zero AddCommGrpCat).of_iso
          (eTop ≪≫ (HasZeroObject.zeroIsoTerminal :
            (0 : AddCommGrpCat) ≅ ⊤_ AddCommGrpCat).symm))
    exact Subsingleton.elim _ _

/-- Existence of the module stalk/skyscraper adjunction. -/
theorem exists_moduleStalkSkyscraperAdjunction {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    Nonempty (moduleStalkFunctor O x ⊣ moduleSkyscraperSheafFunctor O x) := by
  sorry

/-- The module stalk/skyscraper adjunction. -/
noncomputable def moduleStalkSkyscraperAdjunction {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    moduleStalkFunctor O x ⊣ moduleSkyscraperSheafFunctor O x := by
  exact Classical.choice (exists_moduleStalkSkyscraperAdjunction O x)

/-- The Hom equivalence for the module stalk/skyscraper adjunction. -/
noncomputable abbrev moduleStalkSkyscraperHomEquiv {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) (F : Mod O)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    ((moduleStalkFunctor O x).obj F ⟶ A) ≃
      (F ⟶ (moduleSkyscraperSheafFunctor O x).obj A) :=
  (moduleStalkSkyscraperAdjunction O x).homEquiv F A

end

end Formalization.Books.Sheaves.Unit27
