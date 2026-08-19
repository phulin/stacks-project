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
  sorry

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

/-- There is an additive sheaf with nonclosed support of the kind described by
the skyscraper/direct-sum example. -/
theorem exists_nonclosed_skyscraper_direct_sum :
    ∃ (X : TopCat.{v}) (F : TopCat.Sheaf (AddCommGrpCat.{v}) X),
      IsNonClosedSkyscraperDirectSum F := by
  sorry

/-- The source's first warning can be realized on the real line with its
usual topology. -/
theorem exists_nonclosed_skyscraper_direct_sum_on_real_line :
    ∃ F : TopCat.Sheaf (AddCommGrpCat.{0}) (TopCat.of ℝ),
      IsNonClosedSkyscraperDirectSum F := by
  sorry

/-- Extension by zero along an open immersion has support equal to the open
when the original additive sheaf has a nontrivial stalk at every point. -/
theorem openAbelianExtension_support_eq_open {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Sheaf (AddCommGrpCat.{v}) (openSubspace U))
    (hF : ∀ x : openSubspace U, Nontrivial (F.presheaf.stalk x)) :
    additiveSheafSupport ((openAbelianSheafExtensionFunctor U).obj F) =
      (U : Set X) := by
  sorry

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
