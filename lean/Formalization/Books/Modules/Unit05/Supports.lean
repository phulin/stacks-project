import Formalization.Books.Modules.Unit04.Sections
import Formalization.Books.Sheaves.Unit31.Infrastructure
import Formalization.Books.Sheaves.Unit27.Infrastructure
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Data.Real.Basic

/-!
# Modules, Chapter 5: Supports of modules and sections

This file formalizes the precise definitions and statements in the section
`Supports of modules and sections`.  Supports are subsets of the ambient
space defined from the canonical stalks and germs.  The examples use the
existing additive skyscraper and open-immersion extension interfaces.
-/

namespace Formalization.Books.Modules.Unit05

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit04
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

/-! ## Supports from stalks and germs -/

/-- The support of a sheaf of modules is the set of points with a nontrivial
stalk. -/
def moduleSupport {X : TopCat.{v}} {O : RingSheaf.{v, v} X} (F : Mod O) : Set X :=
  {x | Nontrivial ((sheafModuleStalkFunctor O x).obj F)}

/-- The germ of a section on an open subset, viewed in the corresponding
stalk module. -/
noncomputable def sectionGerm {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {F : Mod O} (U : Opens X) (s : F.val.obj (op U)) (x : U) :
    (sheafModuleStalkFunctor O x.1).obj F :=
  localSectionGerm (⟨U, s⟩ : LocalSection O F) x x.property

/-- The support of a section on an open subset, as a closed subset of that
open subset. -/
def sectionSupport {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {F : Mod O} (U : Opens X) (s : F.val.obj (op U)) : Set U :=
  {x | sectionGerm U s x ≠ 0}

/-- The germ of a section of the structure sheaf in a stalk ring. -/
noncomputable def ringSectionGerm {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    (U : Opens X) (f : O.obj.obj (op U)) (x : U) :
    TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x.1 :=
  TopCat.Presheaf.germ (C := RingCat.{v}) O.obj U x.1 x.property f

/-- The support of a section of the structure sheaf. -/
def ringSectionSupport {X : TopCat.{v}} (O : RingSheaf.{v, v} X)
    (U : Opens X) (f : O.obj.obj (op U)) : Set U :=
  {x | ringSectionGerm O U f x ≠ 0}

/-- The support of a global section, written as a subset of the ambient space.
This is the source's global-section form of `sectionSupport`. -/
def globalSectionSupport {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {F : Mod O} (s : F.sections) : Set X :=
  {x | globalSectionGerm s x ≠ 0}

/-- The support of a local section, written in the ambient space. -/
def localSectionSupport {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {F : Mod O} (t : LocalSection O F) : Set X :=
  {x | ∃ hx : t.isDefinedAt x, localSectionGerm t x hx ≠ 0}

/-! ## The support lemma -/

/-- The support of a section is closed in its domain. -/
theorem sectionSupport_isClosed {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {F : Mod O} (U : Opens X) (s : F.val.obj (op U)) :
    IsClosed (sectionSupport U s) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  simp only [sectionSupport, Set.mem_compl_iff, Set.mem_ofPred_eq, not_ne_iff] at hx
  change (ConcreteCategory.hom
      (TopCat.Presheaf.germ (C := AddCommGrpCat) F.val.presheaf U x.1 x.2)) s =
        (0 : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat) F.val.presheaf x.1)) at hx
  have hx'' : (ConcreteCategory.hom
      (TopCat.Presheaf.germ (C := AddCommGrpCat) F.val.presheaf U x.1 x.2)) s =
        (ConcreteCategory.hom
          (TopCat.Presheaf.germ (C := AddCommGrpCat) F.val.presheaf U x.1 x.2)) 0 := by
    rw [map_zero]
    exact hx
  obtain ⟨W, hxW, iU, iV, hres⟩ :=
    TopCat.Presheaf.germ_eq (C := AddCommGrpCat) F.val.presheaf x.1 x.2 x.2 s 0 hx''
  let V : Set U := (Subtype.val : U → X) ⁻¹' (W : Set X)
  have hVopen : IsOpen V := by
    dsimp [V]
    exact W.isOpen.preimage continuous_subtype_val
  refine Filter.mem_of_superset (hVopen.mem_nhds ?_) ?_
  · exact hxW
  · intro y hy
    simp only [sectionSupport, Set.mem_compl_iff, Set.mem_ofPred_eq, not_ne_iff]
    have hyW : y.1 ∈ W := hy
    have hgy := TopCat.Presheaf.germ_ext (C := AddCommGrpCat)
      F.val.presheaf (x := y.1) (hxU := y.2) (hxV := y.2)
        W hyW iU iV hres
    rw [map_zero] at hgy
    exact hgy

/-- The support of a scalar multiple is contained in the intersection of the
supports of the scalar and the section. -/
theorem smul_sectionSupport_subset {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {F : Mod O} (U : Opens X) (f : O.obj.obj (op U))
    (s : F.val.obj (op U)) :
    sectionSupport U (f • s) ⊆ ringSectionSupport O U f ∩ sectionSupport U s := by
  intro x hx
  change (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
    F.val.presheaf U x.1 x.2)) (f • s) ≠ 0 at hx
  have hsmul := PresheafOfModules.germ_ringCat_smul F.val x.1 U x.2 f s
  refine ⟨?_, ?_⟩
  · change (ConcreteCategory.hom (TopCat.Presheaf.germ (C := RingCat)
        O.obj U x.1 x.2)) f ≠ 0
    intro hrf
    apply hx
    rw [hsmul, hrf, zero_smul]
  · change (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
        F.val.presheaf U x.1 x.2)) s ≠ 0
    intro hrs
    apply hx
    rw [hsmul, hrs, smul_zero]

/-- The support of a sum is contained in the union of the two supports. -/
theorem add_sectionSupport_subset {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {F : Mod O} (U : Opens X) (s s' : F.val.obj (op U)) :
    sectionSupport U (s + s') ⊆ sectionSupport U s ∪ sectionSupport U s' := by
  intro x hx
  change (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
    F.val.presheaf U x.1 x.2)) (s + s') ≠ 0 at hx
  change sectionGerm U s x ≠ 0 ∨ sectionGerm U s' x ≠ 0
  by_cases hs : sectionGerm U s x ≠ 0
  · exact Or.inl hs
  by_cases hs' : sectionGerm U s' x ≠ 0
  · exact Or.inr hs'
  exfalso
  apply hx
  have hs0 : sectionGerm U s x = 0 := not_ne_iff.mp hs
  have hs'0 : sectionGerm U s' x = 0 := not_ne_iff.mp hs'
  change (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
    F.val.presheaf U x.1 x.2)) s = 0 at hs0
  change (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
    F.val.presheaf U x.1 x.2)) s' = 0 at hs'0
  have hadd :
      (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
        F.val.presheaf U x.1 x.2)) (s + s') =
        (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
          F.val.presheaf U x.1 x.2)) s +
          (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
            F.val.presheaf U x.1 x.2)) s' := by
    exact map_add _ s s'
  rw [hadd, hs0, hs'0, add_zero]

/-- The support of a sheaf is the union of the supports of all its local
sections. -/
theorem moduleSupport_eq_iUnion_localSectionSupport
    {X : TopCat.{v}} {O : RingSheaf.{v, v} X} (F : Mod O) :
    moduleSupport F = ⋃ t : LocalSection O F, localSectionSupport t := by
  ext x
  constructor
  · intro hx
    change Nontrivial ((sheafModuleStalkFunctor O x).obj F) at hx
    simp only [Set.mem_iUnion]
    have hx' : Nontrivial (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
        F.val.presheaf x)) := by
      simpa only [sheafModuleStalkFunctor,
        Formalization.Books.Sheaves.Unit22.moduleStalkFunctor] using hx
    obtain ⟨a, ha⟩ := @exists_ne
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat) F.val.presheaf x))
      hx' 0
    obtain ⟨U, hxU, s, hs⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat)
        F.val.presheaf a
    refine ⟨⟨U, s⟩, ⟨hxU, ?_⟩⟩
    change (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
      F.val.presheaf U x hxU)) s ≠ 0
    rw [hs]
    exact ha
  · intro hx
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨t, ht⟩
    change ∃ hx : t.isDefinedAt x, localSectionGerm t x hx ≠ 0 at ht
    rcases ht with ⟨hxdef, hg⟩
    have hg' : (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
        F.val.presheaf t.U x hxdef)) t.s ≠ 0 := by
      exact hg
    change Nontrivial ((sheafModuleStalkFunctor O x).obj F)
    have hnon : Nontrivial (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
        F.val.presheaf x)) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      exact hg' (hsub.elim _ _)
    simpa only [sheafModuleStalkFunctor,
      Formalization.Books.Sheaves.Unit22.moduleStalkFunctor] using hnon

/-- A morphism of sheaves of modules cannot enlarge the support of a local
section. -/
theorem map_sectionSupport_subset {X : TopCat.{v}} {O : RingSheaf.{v, v} X}
    {F G : Mod O} (φ : F ⟶ G) (U : Opens X) (s : F.val.obj (op U)) :
    sectionSupport U (φ.val.app (op U) s) ⊆ sectionSupport U s := by
  intro x hx
  change (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
    G.val.presheaf U x.1 x.2)) (φ.val.app (op U) s) ≠ 0 at hx
  change (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
    F.val.presheaf U x.1 x.2)) s ≠ 0
  intro hs
  apply hx
  let s' : ((PresheafOfModules.toPresheaf O.obj).obj F.val).obj (op U) := s
  have hs' : (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
      ((PresheafOfModules.toPresheaf O.obj).obj F.val) U x.1 x.2)) s' = 0 := by
    exact hs
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply U x.1 x.2
    ((PresheafOfModules.toPresheaf O.obj).map φ.val) s'
  rw [hs'] at h
  have hz : (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x.1).map
        ((PresheafOfModules.toPresheaf O.obj).map φ.val)))
      (0 : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
        ((PresheafOfModules.toPresheaf O.obj).obj F.val) x.1)) = 0 := by
    exact map_zero _
  change (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat)
      ((PresheafOfModules.toPresheaf O.obj).obj G.val) U x.1 x.2))
      (((PresheafOfModules.toPresheaf O.obj).map φ.val).app (op U) s') = 0
  exact h.symm.trans hz

/-! ## Non-closed-support examples -/

/-- The support of an additive sheaf, used for the abelian-sheaf examples in
the source. -/
def additiveSheafSupport {X : TopCat.{v}}
    (F : TopCat.Sheaf (AddCommGrpCat.{v}) X) : Set X :=
  {x | Nontrivial (F.presheaf.stalk x)}

/-- A nonzero additive skyscraper sheaf supported at a specified point. -/
def IsNonzeroAbelianSkyscraperAt {X : TopCat.{v}} (x : X)
    (F : TopCat.Sheaf (AddCommGrpCat.{v}) X) : Prop :=
  ∃ A : AddCommGrpCat.{v}, Nontrivial (A : Type v) ∧
    Nonempty (F ≅ abelianSkyscraperSheaf x A)

/-- The source's direct-sum/skyscraper warning: a family of nonzero
skyscrapers has a direct sum whose support is a nonclosed set of points. -/
def IsNonClosedSkyscraperDirectSum {X : TopCat.{v}}
    (F : TopCat.Sheaf (AddCommGrpCat.{v}) X) : Prop :=
  ∃ (I : Type v), Infinite I ∧
    ∃ (p : I → X) (G : I → TopCat.Sheaf (AddCommGrpCat.{v}) X),
      (∀ i, IsNonzeroAbelianSkyscraperAt (p i) (G i)) ∧
        Nonempty (F ≅ colimit (Discrete.functor G)) ∧
          additiveSheafSupport F = Set.range p ∧
            ¬ IsClosed (Set.range p)

private theorem additiveSkyscraperColimit_support_eq_range
    {X : TopCat.{v}} [T1Space X] (I : Type v) (p : I → X)
    (hp : Function.Injective p) (A : AddCommGrpCat.{v})
    (hA : Nontrivial (A : Type v)) :
    additiveSheafSupport
        (colimit (Discrete.functor (fun i => abelianSkyscraperSheaf (p i) A))) =
      Set.range p := by
  classical
  let D : Discrete I ⥤ TopCat.Sheaf (AddCommGrpCat.{v}) X :=
    Discrete.functor (fun i => abelianSkyscraperSheaf (p i) A)
  apply Set.ext
  intro x
  by_cases hx : x ∈ Set.range p
  · rcases hx with ⟨i, rfl⟩
    constructor
    · intro _
      exact ⟨i, rfl⟩
    · intro _
      change Nontrivial
        (((TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} (p i)).obj (colimit D)))
      let H := TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} (p i)
      let e := preservesColimitIso H D
      have hAi : Nontrivial (↑((D ⋙ H).obj ⟨i⟩)) := by
        change Nontrivial
          ((abelianSkyscraperSheaf (p i) A).presheaf.stalk (p i))
        let eA := algebraicSkyscraperStalkOfSpecializes
          (C := AddCommGrpCat.{v}) (p i) A (specializes_refl (p i))
        rw [← not_subsingleton_iff_nontrivial]
        intro hs
        apply not_subsingleton_iff_nontrivial.mpr hA
        refine ⟨?_⟩
        intro a b
        have h := congrArg (fun z => (ConcreteCategory.hom eA.hom) z)
          (hs.elim (ConcreteCategory.hom eA.inv a) (ConcreteCategory.hom eA.inv b))
        simpa using h
      have hcol : Nontrivial (↑(colimit (D ⋙ H))) := by
        let K := D ⋙ H
        let c : Cocone K :=
          { pt := K.obj ⟨i⟩
            ι :=
              { app := fun j => if h : j = ⟨i⟩ then h ▸ 𝟙 _ else 0
                naturality := by
                  intro j k f
                  cases f
                  rename_i h
                  have hjk : j = k := Discrete.ext h.down
                  subst k
                  simp } }
        let t : colimit K ⟶ K.obj ⟨i⟩ := colimit.desc K c
        have hct : colimit.ι K ⟨i⟩ ≫ t = 𝟙 _ := by
          dsimp [t]
          simp [c]
        have htc : t ≫ colimit.ι K ⟨i⟩ = 𝟙 _ := by
          apply (colimit.isColimit K).hom_ext
          intro j
          by_cases hji : j = ⟨i⟩
          · subst j
            simp [t, c]
          · have hzero : IsZero (K.obj j) := by
              change IsZero ((abelianSkyscraperSheaf (p j.as) A).presheaf.stalk (p i))
              have hspec : ¬p j.as ⤳ p i := by
                intro h
                apply hji
                exact Discrete.ext (hp (specializes_iff_eq.mp h))
              let eA := algebraicSkyscraperStalkOfNotSpecializes
                (C := AddCommGrpCat.{v}) (p j.as) A hspec
              exact (isZero_zero AddCommGrpCat.{v}).of_iso
                (eA ≪≫ HasZeroObject.zeroIsoTerminal.symm)
            exact hzero.eq_of_src _ _
        let eK : K.obj ⟨i⟩ ≅ colimit K :=
          { hom := colimit.ι K ⟨i⟩
            inv := t
            hom_inv_id := hct
            inv_hom_id := htc }
        rw [← not_subsingleton_iff_nontrivial]
        intro hs
        apply not_subsingleton_iff_nontrivial.mpr hAi
        refine ⟨?_⟩
        intro a b
        have h := congrArg (fun z => (ConcreteCategory.hom eK.inv) z)
          (hs.elim (ConcreteCategory.hom eK.hom a) (ConcreteCategory.hom eK.hom b))
        simpa using h
      rw [← not_subsingleton_iff_nontrivial]
      intro hs
      apply not_subsingleton_iff_nontrivial.mpr hcol
      refine ⟨?_⟩
      intro a b
      have h := congrArg (fun z => (ConcreteCategory.hom e.hom) z)
        (hs.elim (ConcreteCategory.hom e.inv a) (ConcreteCategory.hom e.inv b))
      simpa using h
  · constructor
    · intro hs
      change Nontrivial
        (((TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).obj (colimit D))) at hs
      let H := TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x
      change Nontrivial (↑(H.obj (colimit D))) at hs
      let e := preservesColimitIso H D
      have hD : ∀ i : I, IsZero ((D ⋙ H).obj ⟨i⟩) := by
        intro i
        change IsZero ((abelianSkyscraperSheaf (p i) A).presheaf.stalk x)
        have hspec : ¬p i ⤳ x := by
          intro h
          apply hx
          exact ⟨i, specializes_iff_eq.mp h⟩
        let eA := algebraicSkyscraperStalkOfNotSpecializes
          (C := AddCommGrpCat.{v}) (p i) A hspec
        exact (isZero_zero AddCommGrpCat.{v}).of_iso
          (eA ≪≫ HasZeroObject.zeroIsoTerminal.symm)
      have hcol : IsZero (colimit (D ⋙ H)) := by
        have hid : (𝟙 (colimit (D ⋙ H))) = 0 := by
          apply (colimit.isColimit (D ⋙ H)).hom_ext
          intro j
          simp only [comp_zero]
          exact (hD j.as).eq_of_src _ _
        refine ⟨?_, ?_⟩
        · intro Y
          refine ⟨⟨⟨0⟩, ?_⟩⟩
          intro f
          change f = 0
          rw [← Category.id_comp f, hid, zero_comp]
        · intro Y
          refine ⟨⟨⟨0⟩, ?_⟩⟩
          intro f
          change f = 0
          rw [← Category.comp_id f, hid, comp_zero]
      have hsub : Subsingleton (↑(colimit (D ⋙ H))) :=
        AddCommGrpCat.subsingleton_of_isZero hcol
      rw [← not_subsingleton_iff_nontrivial] at hs
      exfalso
      apply hs
      refine ⟨?_⟩
      intro a b
      have h := congrArg (fun z => (ConcreteCategory.hom e.inv) z)
        (hsub.elim (ConcreteCategory.hom e.hom a) (ConcreteCategory.hom e.hom b))
      simpa using h
    · intro hx'
      exact False.elim (hx hx')

/-- There is an additive sheaf with nonclosed support of the kind described by
the skyscraper/direct-sum example. -/
theorem exists_nonclosed_skyscraper_direct_sum :
    ∃ (X : TopCat.{v}) (F : TopCat.Sheaf (AddCommGrpCat.{v}) X),
      IsNonClosedSkyscraperDirectSum F := by
  let X : TopCat.{v} := TopCat.of (ULift.{v} ℝ)
  let I : Type v := ULift.{v} ℕ
  let q : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let p : I → X := fun n => ULift.up (q n.down)
  let A : AddCommGrpCat.{v} := AddCommGrpCat.of (ULift.{v} ℤ)
  let G : I → TopCat.Sheaf (AddCommGrpCat.{v}) X :=
    fun n => abelianSkyscraperSheaf (p n) A
  let F : TopCat.Sheaf (AddCommGrpCat.{v}) X :=
    colimit (Discrete.functor G)
  have hp : Function.Injective p := by
    intro m n h
    have hreal : q m.down = q n.down := ULift.up_injective h
    dsimp [q] at hreal
    field_simp at hreal
    have hmn : (m.down : ℝ) = n.down := by linarith
    cases m with
    | up m =>
      cases n with
      | up n =>
        have hmn' : m = n := by exact_mod_cast hmn
        exact congrArg (fun z : ℕ => (ULift.up z : I)) hmn'
  have hA : Nontrivial (A : Type v) := by
    dsimp [A]
    infer_instance
  have hsupport : additiveSheafSupport F = Set.range p := by
    dsimp [F, G]
    exact additiveSkyscraperColimit_support_eq_range (X := X) I p hp A hA
  have hnotclosed : ¬ IsClosed (Set.range p) := by
    intro hclosed
    have hclosed' : IsClosed (ULift.up ⁻¹' (Set.range p)) :=
      ULift.isClosed_iff.mp hclosed
    have hpre : ULift.up ⁻¹' (Set.range p) = Set.range q := by
      ext y
      constructor
      · rintro ⟨n, hn⟩
        refine ⟨n.down, ?_⟩
        exact ULift.up_injective hn
      · rintro ⟨n, hn⟩
        refine ⟨⟨n⟩, ?_⟩
        change ULift.up (q n) = ULift.up y
        rw [hn]
    rw [hpre] at hclosed'
    have hzero : (0 : ℝ) ∈ Set.range q :=
      hclosed'.mem_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
        (Filter.Eventually.of_forall fun n => ⟨n, rfl⟩)
    rcases hzero with ⟨n, hn⟩
    have hnpos : 0 < q n := by
      dsimp [q]
      exact Nat.one_div_pos_of_nat
    rw [hn] at hnpos
    exact (lt_irrefl 0) hnpos
  refine ⟨X, F, ?_⟩
  refine ⟨I, inferInstance, p, G, ?_, ?_, hsupport, hnotclosed⟩
  · intro i
    refine ⟨A, hA, ?_⟩
    exact ⟨Iso.refl _⟩
  · exact ⟨Iso.refl _⟩

/-- The source's first warning can be realized on the real line with its
usual topology. -/
theorem exists_nonclosed_skyscraper_direct_sum_on_real_line :
    ∃ F : TopCat.Sheaf (AddCommGrpCat.{0}) (TopCat.of ℝ),
      IsNonClosedSkyscraperDirectSum F := by
  let X : TopCat.{0} := TopCat.of ℝ
  let I : Type 0 := ULift.{0} ℕ
  let q : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let p : I → X := fun n => q n.down
  let A : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ
  let G : I → TopCat.Sheaf (AddCommGrpCat.{0}) X :=
    fun n => abelianSkyscraperSheaf (p n) A
  let : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0} := by
    infer_instance
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{0} := by
    infer_instance
  let : HasColimitsOfShape (Discrete I)
      (TopCat.Sheaf (AddCommGrpCat.{0}) X) := by
    exact CategoryTheory.Sheaf.instHasColimitsOfShape
  let F : TopCat.Sheaf (AddCommGrpCat.{0}) X :=
    colimit (Discrete.functor G)
  have hp : Function.Injective p := by
    intro m n h
    have hreal : q m.down = q n.down := h
    dsimp [q] at hreal
    field_simp at hreal
    have hmn : (m.down : ℝ) = n.down := by linarith
    cases m with
    | up m =>
      cases n with
      | up n =>
        have hmn' : m = n := by exact_mod_cast hmn
        exact congrArg (fun z : ℕ => (ULift.up z : I)) hmn'
  have hA : Nontrivial (A : Type 0) := by
    dsimp [A]
    infer_instance
  have hsupport : additiveSheafSupport F = Set.range p := by
    dsimp [F, G]
    exact additiveSkyscraperColimit_support_eq_range (X := X) I p hp A hA
  have hnotclosed : ¬ IsClosed (Set.range p) := by
    intro hclosed
    have hrange : Set.range p = Set.range q := by
      ext y
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n.down, hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨⟨n⟩, hn⟩
    rw [hrange] at hclosed
    have hzero : (0 : ℝ) ∈ Set.range q := by
      exact hclosed.mem_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
        (Filter.Eventually.of_forall fun n => ⟨n, rfl⟩)
    rcases hzero with ⟨n, hn⟩
    have hnpos : 0 < q n := by
      dsimp [q]
      exact Nat.one_div_pos_of_nat
    rw [hn] at hnpos
    exact (lt_irrefl 0) hnpos
  refine ⟨F, ?_⟩
  refine ⟨I, inferInstance, p, G, ?_, ?_, hsupport, hnotclosed⟩
  · intro i
    refine ⟨A, hA, ?_⟩
    exact ⟨Iso.refl _⟩
  · exact ⟨Iso.refl _⟩

/-- Extension by zero along an open immersion has support equal to the open
when the original additive sheaf has a nontrivial stalk at every point. -/
theorem openAbelianExtension_support_eq_open {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Sheaf (AddCommGrpCat.{v}) (openSubspace U))
    (hF : ∀ x : openSubspace U, Nontrivial (F.presheaf.stalk x)) :
    additiveSheafSupport ((openAbelianSheafExtensionFunctor U).obj F) =
      (U : Set X) := by
  apply Set.ext
  intro x
  by_cases hx : x ∈ U
  · constructor
    · intro _
      exact hx
    · intro _
      change Nontrivial (((openAbelianSheafExtensionFunctor U).obj F).presheaf.stalk x)
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      apply (not_subsingleton_iff_nontrivial.mpr (hF ⟨x, hx⟩))
      let e := Classical.choice (openAlgebraicSheafExtension_stalk_iso
        AddCommGrpCat U F x hx)
      refine ⟨?_⟩
      intro a b
      have h := congrArg (fun z => (ConcreteCategory.hom e.hom) z)
        (hsub.elim (ConcreteCategory.hom e.inv a) (ConcreteCategory.hom e.inv b))
      simpa using h
  · constructor
    · intro hs
      exfalso
      change Nontrivial (((openAbelianSheafExtensionFunctor U).obj F).presheaf.stalk x) at hs
      let e := Classical.choice (openAlgebraicSheafExtension_stalk_initial
        AddCommGrpCat U F x hx)
      have hzero : Subsingleton (↑(⊥_ AddCommGrpCat.{v})) := by
        exact AddCommGrpCat.subsingleton_of_isZero
          ((isZero_zero AddCommGrpCat.{v}).of_iso
            (HasZeroObject.zeroIsoInitial :
              (0 : AddCommGrpCat.{v}) ≅ (⊥_ AddCommGrpCat.{v})).symm)
      rw [← not_subsingleton_iff_nontrivial] at hs
      apply hs
      refine ⟨?_⟩
      intro a b
      have hab : (ConcreteCategory.hom e.hom) a =
          (ConcreteCategory.hom e.hom) b :=
        @Subsingleton.elim (↑(⊥_ AddCommGrpCat.{v})) hzero _ _
      have h := congrArg (fun z => (ConcreteCategory.hom e.inv) z) hab
      simpa using h
    · intro hx'
      exact False.elim (hx hx')

/-- The concrete `j_! \underline{ℤ}_U` example on the real line, with
`U = (0, ∞)`, has support exactly `U`. -/
noncomputable def integerConstantAbelianSheaf {X : TopCat.{0}} :
    TopCat.Sheaf (AddCommGrpCat.{0}) X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))

def positiveRealOpen : Opens (TopCat.of ℝ) :=
  ⟨Set.Ioi (0 : ℝ), isOpen_Ioi⟩

theorem positiveRealOpen_not_closed :
    ¬ IsClosed (positiveRealOpen : Set (TopCat.of ℝ)) := by
  sorry

theorem positiveRealOpen_extension_support :
    additiveSheafSupport
        ((openAbelianSheafExtensionFunctor positiveRealOpen).obj
          (integerConstantAbelianSheaf (X := openSubspace positiveRealOpen))) =
      (positiveRealOpen : Set (TopCat.of ℝ)) := by
  sorry

/-! ## Sheaves of rings -/

/-- The support of a sheaf of rings. -/
def ringSheafSupport {X : TopCat.{v}} (O : RingSheaf.{v, v} X) : Set X :=
  {x | Nontrivial (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)}

/-- The support of a sheaf of rings is closed. -/
theorem ringSheafSupport_isClosed {X : TopCat.{v}}
    (O : RingSheaf.{v, v} X) : IsClosed (ringSheafSupport O) := by
  sorry

end
end Formalization.Books.Modules.Unit05
