import Formalization.Books.Sheaves.Unit04.AbelianPresheaves
import Mathlib.Data.DFinsupp.Encodable
import Mathlib.Data.Int.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Sheaves on Spaces, Chapter 7: Sheaves

The source section is formalized with Mathlib's canonical sheaf condition and
the canonical sheaves of functions.  The direct-sum example reuses the
presheaf constructed in Chapter 4 rather than introducing a second version
of that presheaf.
-/

namespace Formalization.Books.Sheaves.Unit07

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit04
open scoped DirectSum

universe w v u

/-! ## The sheaf condition and the category of sheaves -/

/-- A set-valued presheaf satisfying the canonical sheaf condition. -/
abbrev SetSheaf {X : TopCat.{v}} (F : Presheaf.{w, v} X) : Prop :=
  TopCat.Presheaf.IsSheaf F

/-- The category `Sh(X)` of sheaves of sets on `X`. -/
abbrev Sh (X : TopCat.{v}) := TopCat.Sheaf (Type w) X

/-- A morphism in `Sh(X)`, whose underlying map is a presheaf morphism. -/
abbrev SetSheafMorphism {X : TopCat.{v}} (F G : Sh.{w, v} X) := F ⟶ G

/-- Compatibility of a family of sections on an open cover. -/
abbrev CompatibleSections {X : TopCat.{v}} {F : Presheaf.{w, v} X}
    {ι : Type v} (U : ι → Opens X) (s : ∀ i, Sections F (U i)) : Prop :=
  TopCat.Presheaf.IsCompatible F U s

/-- The assertion that a section glues a compatible family on an open cover. -/
abbrev IsGluingSections {X : TopCat.{v}} {F : Presheaf.{w, v} X}
    {ι : Type v} (U : ι → Opens X) (s : ∀ i, Sections F (U i))
    (t : Sections F (iSup U)) : Prop :=
  TopCat.Presheaf.IsGluing F U s t

/-- The source's elementwise sheaf condition, via Mathlib's unique-gluing API. -/
theorem setSheaf_iff_unique_gluing {X : TopCat.{v}} (F : Presheaf.{w, v} X) :
    SetSheaf F ↔
      ∀ ⦃ι : Type v⦄ (U : ι → Opens X) (s : ∀ i, Sections F (U i)),
        CompatibleSections U s →
          ∃! t : Sections F (iSup U), IsGluingSections U s t := by
  change TopCat.Presheaf.IsSheaf F ↔
    TopCat.Presheaf.IsSheafUniqueGluing F
  exact TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types F

/-! ## Empty covers and disjoint unions -/

/-- The empty-cover case makes the sections on the empty open terminal. -/
noncomputable def setSheaf_sections_empty_isTerminal {X : TopCat.{v}}
    {F : Presheaf.{w, v} X} (hF : SetSheaf F) :
    IsTerminal (F.obj (op (⊥ : Opens X))) := by
  exact TopCat.Sheaf.isTerminalOfEmpty (⟨F, hF⟩ : TopCat.Sheaf (Type w) X)

/-- In `Type`, the terminal sections on the empty open form a singleton type. -/
theorem setSheaf_sections_empty_unique {X : TopCat.{v}}
    {F : Presheaf.{w, v} X} (hF : SetSheaf F) :
    Nonempty (Sections F (⊥ : Opens X)) ∧
      Subsingleton (Sections F (⊥ : Opens X)) := by
  let hUnique : Unique (Sections F (⊥ : Opens X)) :=
    (Types.isTerminalEquivUnique _).toFun (setSheaf_sections_empty_isTerminal hF)
  exact ⟨⟨hUnique.default⟩, ⟨fun a b => (hUnique.uniq a).trans (hUnique.uniq b).symm⟩⟩

/-- Sections over disjoint opens are the product of the two section types. -/
theorem setSheaf_disjoint_union_sections_equiv {X : TopCat.{v}}
    {F : Presheaf.{w, v} X} (hF : SetSheaf F) {U V : Opens X}
    (hUV : Disjoint U V) :
    Nonempty (Sections F (U ⊔ V) ≃ Sections F U × Sections F V) := by
  classical
  let W : ULift.{v} Bool → Opens X := fun b => Bool.rec U V b.down
  have hW : iSup W = U ⊔ V := by
    apply le_antisymm
    · refine iSup_le ?_
      intro b
      cases b with
      | up b => cases b <;> simp [W]
    · refine sup_le ?_ ?_
      · exact le_iSup_of_le (ULift.up false) (by simp [W])
      · exact le_iSup_of_le (ULift.up true) (by simp [W])
  let family : (Sections F U × Sections F V) →
      ∀ b : ULift.{v} Bool, Sections F (W b) := fun p b =>
    @Bool.rec (fun b => Sections F (Bool.rec U V b)) p.1 p.2 b.down
  have compatible (p : Sections F U × Sections F V) :
      TopCat.Presheaf.IsCompatible F W (family p) := by
    intro i j
    cases i with
    | up i =>
      cases j with
      | up j =>
        cases i <;> cases j
        · change F.map (Opens.infLELeft U U).op p.1 = F.map (Opens.infLERight U U).op p.1
          rw [Subsingleton.elim (Opens.infLELeft U U) (Opens.infLERight U U)]
        · change F.map (Opens.infLELeft U V).op p.1 = F.map (Opens.infLERight U V).op p.2
          have hsub : Subsingleton (Sections F (U ⊓ V)) := by
            rw [hUV.eq_bot]
            exact ⟨fun a b =>
              (setSheaf_sections_empty_unique (F := F) hF).2.elim a b⟩
          exact @Subsingleton.elim _ hsub _ _
        · change F.map (Opens.infLELeft V U).op p.2 = F.map (Opens.infLERight V U).op p.1
          have hsub : Subsingleton (Sections F (V ⊓ U)) := by
            rw [hUV.symm.eq_bot]
            exact ⟨fun a b =>
              (setSheaf_sections_empty_unique (F := F) hF).2.elim a b⟩
          exact @Subsingleton.elim _ hsub _ _
        · change F.map (Opens.infLELeft V V).op p.2 = F.map (Opens.infLERight V V).op p.2
          rw [Subsingleton.elim (Opens.infLELeft V V) (Opens.infLERight V V)]
  let glue (p : Sections F U × Sections F V) : Sections F (iSup W) :=
    (setSheaf_iff_unique_gluing F |>.mp hF W (family p) (compatible p)).choose
  have glue_spec (p : Sections F U × Sections F V) :
      IsGluingSections W (family p) (glue p) :=
    (setSheaf_iff_unique_gluing F |>.mp hF W (family p) (compatible p)).choose_spec.1
  let e0 : Sections F (iSup W) ≃ Sections F U × Sections F V := {
    toFun := fun s =>
      (F.map (Opens.leSupr W (ULift.up false)).op s,
        F.map (Opens.leSupr W (ULift.up true)).op s)
    invFun := glue
    left_inv := by
      intro s
      let p := (
        F.map (Opens.leSupr W (ULift.up false)).op s,
        F.map (Opens.leSupr W (ULift.up true)).op s)
      have hs : IsGluingSections W (family p) s := by
        intro b
        cases b with
        | up b =>
          cases b
          · change F.map (Opens.leSupr W (ULift.up false)).op s =
              F.map (Opens.leSupr W (ULift.up false)).op s
            rfl
          · change F.map (Opens.leSupr W (ULift.up true)).op s =
              F.map (Opens.leSupr W (ULift.up true)).op s
            rfl
      exact (setSheaf_iff_unique_gluing F |>.mp hF W (family p) (compatible p)).unique
        (glue_spec p) hs
    right_inv := by
      intro p
      apply Prod.ext
      · simpa [glue, family, W] using glue_spec p (ULift.up false)
      · simpa [glue, family, W] using glue_spec p (ULift.up true) }
  refine ⟨?_⟩
  simpa [hW] using e0

/-! ## Continuous functions and constant sheaves -/

/-- The presheaf of continuous functions from opens of `X` to `Y`. -/
def continuousFunctionsPresheaf (X Y : TopCat.{u}) :
    TopCat.Presheaf (Type u) X :=
  TopCat.presheafToTop X Y

/-- Sections of the continuous-functions presheaf are continuous maps on an open. -/
@[simp]
theorem continuousFunctionsPresheaf_obj (X Y : TopCat.{u}) (U : Opens X) :
    (continuousFunctionsPresheaf X Y).obj (op U) =
      ((Opens.toTopCat X).obj U ⟶ Y) := rfl

/-- The restriction operation in the continuous-functions presheaf. -/
abbrev continuousFunctionsRestriction (X Y : TopCat.{u}) {U V : Opens X}
    (i : V ⟶ U) (f : ToType ((continuousFunctionsPresheaf X Y).obj (op U))) :
    ToType ((continuousFunctionsPresheaf X Y).obj (op V)) :=
  TopCat.Presheaf.restrict f i

/-- The sheaf of continuous functions from opens of `X` to `Y`. -/
def continuousFunctionsSheaf (X Y : TopCat.{u}) :
    TopCat.Sheaf (Type u) X :=
  TopCat.sheafToTop (X := X) Y

/-- Continuous functions glue to a continuous function on an open cover. -/
theorem continuousFunctionsPresheaf_isSheaf (X Y : TopCat.{u}) :
    SetSheaf (continuousFunctionsPresheaf X Y) := by
  exact (continuousFunctionsSheaf X Y).property

/-- For a discrete target, continuity is equivalent to local constancy. -/
theorem continuous_iff_locallyConstant_of_discrete
    {Z A : Type u} [TopologicalSpace Z] [TopologicalSpace A]
    [DiscreteTopology A] (f : Z → A) :
    Continuous f ↔ IsLocallyConstant f := by
  exact (IsLocallyConstant.iff_continuous f).symm

/-- The set of locally constant sections on an open, as used in the source. -/
abbrev LocallyConstantSections (X : TopCat.{u}) (A : Type u) (U : Opens X) :=
  {f : U → A // IsLocallyConstant f}

/-- The constant sheaf with value `A`, using the discrete topology on `A`. -/
def constantSheaf (X : TopCat.{u}) (A : Type u) :
    TopCat.Sheaf (Type u) X :=
  continuousFunctionsSheaf X (TopCat.discrete.obj A)

/-- The underlying presheaf of the constant sheaf is the continuous-functions presheaf. -/
@[simp]
theorem constantSheaf_presheaf (X : TopCat.{u}) (A : Type u) :
    (constantSheaf X A).presheaf =
      continuousFunctionsPresheaf X (TopCat.discrete.obj A) := rfl

/-- The sections of the constant sheaf are the locally constant maps. -/
theorem constantSheaf_sections_equiv (X : TopCat.{u}) (A : Type u) (U : Opens X) :
    Nonempty (Sections (constantSheaf X A).presheaf U ≃
      LocallyConstantSections X A U) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  change Nonempty
    (((Opens.toTopCat X).obj U ⟶ TopCat.discrete.obj A) ≃
      LocallyConstantSections X A U)
  refine ⟨{
    toFun := fun f =>
      ⟨ConcreteCategory.hom f,
        (continuous_iff_locallyConstant_of_discrete
          (ConcreteCategory.hom f)).mp (ConcreteCategory.hom f).continuous_toFun⟩
    invFun := fun f =>
      TopCat.ofHom ⟨f.1,
        (continuous_iff_locallyConstant_of_discrete f.1).mpr f.2⟩
    left_inv := ?_
    right_inv := ?_ }⟩
  · intro f
    apply TopCat.Hom.ext
    rfl
  · intro f
    apply Subtype.ext
    rfl

/-! ## Pointwise products of stalkwise sets -/

/-- The presheaf whose sections over `U` are dependent products of the `A x`. -/
def pointwiseProductPresheaf {X : TopCat.{v}} (A : X → Type w) :
    TopCat.Presheaf (Type (max v w)) X :=
  TopCat.presheafToTypes X A

/-- Sections of the pointwise product presheaf are dependent functions on the open. -/
@[simp]
theorem pointwiseProductPresheaf_obj {X : TopCat.{v}} (A : X → Type w)
    (U : Opens X) :
    (pointwiseProductPresheaf A).obj (op U) = ∀ x : U, A x := rfl

/-- Restriction in the pointwise product presheaf is pointwise restriction. -/
theorem pointwiseProductPresheaf_restriction {X : TopCat.{v}} (A : X → Type w)
    {U V : Opens X} (i : V ⟶ U) (s : ∀ x : U, A x) :
    TopCat.Presheaf.restrict (F := pointwiseProductPresheaf A) s i =
      fun x : V => s (i x) := rfl

/-- The pointwise product presheaf is a sheaf. -/
theorem pointwiseProductPresheaf_isSheaf {X : TopCat.{v}} (A : X → Type w) :
    SetSheaf (pointwiseProductPresheaf A) :=
  TopCat.Presheaf.toTypes_isSheaf X A

/-- The corresponding pointwise product sheaf. -/
def pointwiseProductSheaf {X : TopCat.{v}} (A : X → Type w) :
    TopCat.Sheaf (Type (max v w)) X :=
  ⟨pointwiseProductPresheaf A, pointwiseProductPresheaf_isSheaf A⟩

/-! ## Direct sums over points -/

/-- The set-valued form of Unit04's direct-sum-over-points presheaf. -/
noncomputable abbrev directSumPresheafOfSets {X : TopCat.{v}} (M : X → Type w)
    [∀ x, AddCommGroup (M x)] :
    TopCat.Presheaf (Type (max v w)) X :=
  Formalization.Books.Sheaves.Unit04.underlyingPresheaf
    (Formalization.Books.Sheaves.Unit04.directSumPresheaf M)

/-- Sections of the direct-sum presheaf are direct sums over the open. -/
@[simp]
theorem directSumPresheafOfSets_sections {X : TopCat.{v}} (M : X → Type w)
    [∀ x, AddCommGroup (M x)] (U : Opens X) :
    Sections (directSumPresheafOfSets M) U = (⨁ x : U, M x) := rfl

/-- Restriction in the direct-sum presheaf discards summands outside the smaller open. -/
theorem directSumPresheafOfSets_restriction {X : TopCat.{v}} (M : X → Type w)
    [∀ x, AddCommGroup (M x)] {U V : Opens X} (h : V ≤ U)
    (s : Sections (directSumPresheafOfSets M) U) :
    TopCat.Presheaf.restrict (F := directSumPresheafOfSets M) s (homOfLE h) =
      Formalization.Books.Sheaves.Unit04.directSumRestriction M h s := rfl

/-- A singleton open in a discrete space. -/
def singletonOpen (X : TopCat.{v}) [DiscreteTopology X] (x : X) : Opens X :=
  ⟨{x}, isOpen_discrete _⟩

/-- On a discrete space, the sheaf condition identifies sections with singleton data. -/
theorem setSheaf_sections_top_equiv_singletons {X : TopCat.{v}}
    [DiscreteTopology X] {F : Presheaf.{w, v} X} (hF : SetSheaf F) :
    Nonempty (Sections F (⊤ : Opens X) ≃
      ∀ x : X, Sections F (singletonOpen X x)) := by
  classical
  have htop : iSup (singletonOpen X) = (⊤ : Opens X) := by
    ext y
    simp [singletonOpen]
  have compatible (s : ∀ x : X, Sections F (singletonOpen X x)) :
      TopCat.Presheaf.IsCompatible F (singletonOpen X) s := by
    intro x y
    by_cases hxy : x = y
    · subst y
      rw [Subsingleton.elim
        (Opens.infLELeft (singletonOpen X x) (singletonOpen X x))
        (Opens.infLERight (singletonOpen X x) (singletonOpen X x))]
    · have hbot : singletonOpen X x ⊓ singletonOpen X y = (⊥ : Opens X) := by
        ext z
        simp [singletonOpen, hxy]
      have hsub : Subsingleton (Sections F (singletonOpen X x ⊓ singletonOpen X y)) := by
        rw [hbot]
        exact ⟨fun a b => (setSheaf_sections_empty_unique (F := F) hF).2.elim a b⟩
      exact @Subsingleton.elim _ hsub _ _
  let glue (s : ∀ x : X, Sections F (singletonOpen X x)) :
      Sections F (iSup (singletonOpen X)) :=
    (setSheaf_iff_unique_gluing F |>.mp hF (singletonOpen X) s (compatible s)).choose
  have glue_spec (s : ∀ x : X, Sections F (singletonOpen X x)) :
      IsGluingSections (singletonOpen X) s (glue s) :=
    (setSheaf_iff_unique_gluing F |>.mp hF (singletonOpen X) s (compatible s)).choose_spec.1
  let e0 : Sections F (iSup (singletonOpen X)) ≃
      ∀ x : X, Sections F (singletonOpen X x) := {
    toFun := fun t x => F.map (Opens.leSupr (singletonOpen X) x).op t
    invFun := glue
    left_inv := by
      intro t
      let s : ∀ x : X, Sections F (singletonOpen X x) :=
        fun x => F.map (Opens.leSupr (singletonOpen X) x).op t
      have ht : IsGluingSections (singletonOpen X) s t := by
        intro x
        rfl
      exact (setSheaf_iff_unique_gluing F |>.mp hF (singletonOpen X) s (compatible s)).unique
        (glue_spec s) ht
    right_inv := by
      intro s
      funext x
      exact glue_spec s x }
  refine ⟨?_⟩
  simpa [htop] using e0

/-- For the direct-sum presheaf, the discrete infinite sheaf condition would
force a direct-sum/product additive equivalence. -/
theorem directSumPresheaf_sheaf_implies_sum_product {X : TopCat.{v}}
    (hX : Infinite X) [DiscreteTopology X] (M : X → Type w)
    [∀ x, AddCommGroup (M x)]
    (hF : SetSheaf (directSumPresheafOfSets M)) :
    Nonempty ((⨁ x : X, M x) ≃+ (∀ x : X, M x)) := by
  classical
  let e (x : X) : singletonOpen X x ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨x, by simp [singletonOpen]⟩
    left_inv := by
      intro y
      apply Subtype.ext
      simpa [singletonOpen] using y.property.symm
    right_inv := by intro y; cases y; rfl }
  let localEquiv (x : X) :
      (⨁ y : singletonOpen X x, M y) ≃+ M x := by
    let a := DirectSum.equivCongrLeft
      (β := fun y : singletonOpen X x => M y) (κ := Unit) (e x)
    let b := DirectSum.id (M x) Unit
    exact a.trans b
  let q : (∀ x : X, ⨁ y : singletonOpen X x, M y) ≃+
      (∀ x : X, M x) := AddEquiv.piCongrRight localEquiv
  let iSupEquiv : (iSup (singletonOpen X) : Opens X) ≃ X := {
    toFun := fun z => z.1
    invFun := fun x =>
      ⟨x, (Opens.leSupr (singletonOpen X) x
        ⟨x, by simp [singletonOpen]⟩).property⟩
    left_inv := by intro z; apply Subtype.ext; rfl
    right_inv := by intro x; rfl }
  let r : (⨁ x : (iSup (singletonOpen X) : Opens X), M x) →+
      (∀ x : X, ⨁ y : singletonOpen X x, M y) := {
    toFun := fun s x =>
      Formalization.Books.Sheaves.Unit04.directSumRestriction M
        (Opens.leSupr (singletonOpen X) x).le s
    map_zero' := by
      ext x
      simp
    map_add' := by
      intro s t
      ext x
      simp }
  let iSupDS : (⨁ x : (iSup (singletonOpen X) : Opens X), M x) ≃+ (⨁ x : X, M x) := by
    let a := DirectSum.equivCongrLeft
      (β := fun y : (iSup (singletonOpen X) : Opens X) => M y) iSupEquiv
    simpa [a, iSupEquiv] using a
  have compatible (s : ∀ x : X, ⨁ y : singletonOpen X x, M y) :
      TopCat.Presheaf.IsCompatible (directSumPresheafOfSets M)
        (singletonOpen X) s := by
    intro x y
    by_cases hxy : x = y
    · subst y
      rw [Subsingleton.elim
        (Opens.infLELeft (singletonOpen X x) (singletonOpen X x))
        (Opens.infLERight (singletonOpen X x) (singletonOpen X x))]
    · have hbot : singletonOpen X x ⊓ singletonOpen X y = (⊥ : Opens X) := by
        ext z
        simp [singletonOpen, hxy]
      have hsub : Subsingleton
          (Sections (directSumPresheafOfSets M)
            (singletonOpen X x ⊓ singletonOpen X y)) := by
        rw [hbot]
        exact ⟨fun a b =>
          (setSheaf_sections_empty_unique
            (F := directSumPresheafOfSets M) hF).2.elim a b⟩
      exact @Subsingleton.elim _ hsub _ _
  let glue (s : ∀ x : X, ⨁ y : singletonOpen X x, M y) :
      Sections (directSumPresheafOfSets M) (iSup (singletonOpen X) : Opens X) :=
    (setSheaf_iff_unique_gluing (directSumPresheafOfSets M) |>.mp hF
      (singletonOpen X) s (compatible s)).choose
  have glue_spec (s : ∀ x : X, ⨁ y : singletonOpen X x, M y) :
      IsGluingSections (singletonOpen X) s (glue s) :=
    (setSheaf_iff_unique_gluing (directSumPresheafOfSets M) |>.mp hF
      (singletonOpen X) s (compatible s)).choose_spec.1
  have r_eq (a : ⨁ x : (iSup (singletonOpen X) : Opens X), M x) (x : X) :
      r a x = (directSumPresheafOfSets M).map
        (Opens.leSupr (singletonOpen X) x).op a := by
    change Formalization.Books.Sheaves.Unit04.directSumRestriction M
        (Opens.leSupr (singletonOpen X) x).le a = _
    calc
      _ = TopCat.Presheaf.restrict a
          (homOfLE (Opens.leSupr (singletonOpen X) x).le) :=
        (directSumPresheafOfSets_restriction M
          (U := (iSup (singletonOpen X) : Opens X)) (V := singletonOpen X x)
          (Opens.leSupr (singletonOpen X) x).le a).symm
      _ = (directSumPresheafOfSets M).map
          (Opens.leSupr (singletonOpen X) x).op a := by
        change (directSumPresheafOfSets M).map
            (homOfLE (Opens.leSupr (singletonOpen X) x).le).op a = _
        have hh :
            (homOfLE (Opens.leSupr (singletonOpen X) x).le :
              singletonOpen X x ⟶ (iSup (singletonOpen X) : Opens X)) =
              Opens.leSupr (singletonOpen X) x :=
          Subsingleton.elim _ _
        exact congrArg
            (fun h : singletonOpen X x ⟶ (iSup (singletonOpen X) : Opens X) =>
              (directSumPresheafOfSets M).map h.op a)
          hh
  have glue_top (a : ⨁ x : (iSup (singletonOpen X) : Opens X), M x) :
      TopCat.Presheaf.IsGluing (directSumPresheafOfSets M)
        (singletonOpen X) (fun x => r a x) a := by
    intro x
    exact (r_eq a x).symm
  have hr : Function.Bijective r := by
    constructor
    · intro a b hab
      have hb : TopCat.Presheaf.IsGluing (directSumPresheafOfSets M)
          (singletonOpen X) (fun x => r a x) b := by
        simpa [hab] using glue_top b
      have heq : a = b :=
        let ha : TopCat.Presheaf.IsGluing (directSumPresheafOfSets M)
            (singletonOpen X) (fun x => r a x) a := glue_top a
        (setSheaf_iff_unique_gluing (directSumPresheafOfSets M) |>.mp hF
          (singletonOpen X) (fun x => r a x) (compatible (fun x => r a x))).unique
          ha hb
      exact heq
    · intro s
      refine ⟨glue s, ?_⟩
      funext x
      exact (r_eq (glue s) x).trans (glue_spec s x)
  let rEquiv : (⨁ x : (iSup (singletonOpen X) : Opens X), M x) ≃+
      (∀ x : X, ⨁ y : singletonOpen X x, M y) :=
    AddEquiv.ofBijective r hr
  exact ⟨iSupDS.symm.trans (rEquiv.trans q)⟩

/-- A genuine direct-sum/product mismatch prevents the direct-sum presheaf
from being a sheaf on an infinite discrete space. -/
theorem directSumPresheaf_not_sheaf_of_sum_product_gap {X : TopCat.{v}}
    (hX : Infinite X) [DiscreteTopology X] (M : X → Type w)
    [∀ x, AddCommGroup (M x)]
    (hgap : ¬ Nonempty ((⨁ x : X, M x) ≃+ (∀ x : X, M x))) :
    ¬ SetSheaf (directSumPresheafOfSets M) := by
  intro hF
  exact hgap (directSumPresheaf_sheaf_implies_sum_product hX M hF)

/-- The standard countable family of integer groups exhibits the
direct-sum/product mismatch mentioned in the source. -/
theorem directSum_product_gap_nat :
    ¬ Nonempty ((⨁ _ : ℕ, ℤ) ≃+ (ℕ → ℤ)) := by
  rintro ⟨e⟩
  letI : Countable (⨁ _ : ℕ, ℤ) := by
    change Countable (Π₀ _ : ℕ, ℤ)
    infer_instance
  have hcount : Countable (ℕ → ℤ) :=
    Countable.of_equiv (⨁ _ : ℕ, ℤ) e.toEquiv
  letI : Countable (ℕ → ℤ) := hcount
  obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → ℤ)
  let g : ℕ → ℤ := fun n => if f n n = 0 then 1 else 0
  obtain ⟨n, hn⟩ := hf g
  have hng : f n n = g n := congrFun hn n
  have hdiag : g n = if g n = 0 then 1 else 0 := by
    calc
      g n = if f n n = 0 then 1 else 0 := by rfl
      _ = if g n = 0 then 1 else 0 := by rw [hng]
  by_cases hz : g n = 0
  · have h01 : (0 : ℤ) = 1 := by simpa [hz] using hdiag
    exact zero_ne_one h01
  · have hz' : g n = 0 := by simpa [hz] using hdiag
    exact hz hz'

/-- The direct-sum presheaf is not a sheaf for the standard infinite discrete
space and integer-valued family. -/
theorem directSumPresheaf_not_sheaf_nat :
    ¬ SetSheaf
      (directSumPresheafOfSets (X := TopCat.discrete.obj ℕ)
        (fun _ : ℕ => ℤ)) := by
  apply directSumPresheaf_not_sheaf_of_sum_product_gap
    (inferInstanceAs (Infinite ℕ))
  exact directSum_product_gap_nat

/-- If every open is quasi-compact, the direct-sum-over-points presheaf is a sheaf. -/
theorem directSumPresheaf_isSheaf_of_compact_opens {X : TopCat.{v}}
    (M : X → Type w) [∀ x, AddCommGroup (M x)]
    (hcompact : ∀ U : Opens X, IsCompact (U : Set X)) :
    SetSheaf (directSumPresheafOfSets M) := by
  classical
  have restriction_apply {U V : Opens X} (h : V ≤ U)
      (a : ⨁ x : U, M x) (x : V) :
      Formalization.Books.Sheaves.Unit04.directSumRestriction M h a x =
        a ⟨x.1, h x.2⟩ := by
    induction a using DirectSum.induction_on with
    | zero => simp
    | of i m =>
      by_cases hi : (i : X) ∈ V
      · let xi : V := ⟨i.1, hi⟩
        by_cases hxi : xi = x
        · have hix : i = (⟨x.1, h x.2⟩ : U) := by
            apply Subtype.ext
            exact congrArg (fun z : V => (z : X)) hxi
          simp only [Formalization.Books.Sheaves.Unit04.directSumRestriction,
            DirectSum.toAddMonoid_of, dif_pos hi]
          change (DirectSum.of (fun y : V => M y) xi m) x =
            (DirectSum.of (fun y : U => M y) i m) ⟨x.1, h x.2⟩
          simp [DirectSum.of_apply, hxi, hix]
          apply eq_of_heq
          simp only [eqRec_heq_iff]
          exact
            (eqRec_heq
              (φ := fun z : U => M z) hix m).symm
        · have hix : i ≠ (⟨x.1, h x.2⟩ : U) := by
            intro h'
            apply hxi
            apply Subtype.ext
            exact congrArg (fun z : U => (z : X)) h'
          have hxi' : x ≠ xi := fun h' => hxi h'.symm
          have hix' : (⟨x.1, h x.2⟩ : U) ≠ i := fun h' => hix h'.symm
          simp only [Formalization.Books.Sheaves.Unit04.directSumRestriction,
            DirectSum.toAddMonoid_of, dif_pos hi]
          change (DirectSum.of (fun y : V => M y) xi m) x =
            (DirectSum.of (fun y : U => M y) i m) ⟨x.1, h x.2⟩
          rw [DirectSum.of_eq_of_ne (β := fun y : V => M y) xi x
            (show M (xi : X) from m) hxi']
          rw [DirectSum.of_eq_of_ne (β := fun y : U => M y) i
            (⟨x.1, h x.2⟩) m hix']
      · by_cases hix : (i : X) = x.1
        · exact False.elim (hi (hix.symm ▸ x.2))
        · have hix' : i ≠ (⟨x.1, h x.2⟩ : U) := by
            intro h'
            exact hix (congrArg (fun z : U => (z : X)) h')
          have hix'' : (⟨x.1, h x.2⟩ : U) ≠ i := fun h' => hix' h'.symm
          simp only [Formalization.Books.Sheaves.Unit04.directSumRestriction,
            DirectSum.toAddMonoid_of, dif_neg hi]
          rw [DirectSum.of_eq_of_ne (β := fun y : U => M y) i
            (⟨x.1, h x.2⟩) m hix'']
          simp
    | add a b ha hb =>
      calc
        _ = ((Formalization.Books.Sheaves.Unit04.directSumRestriction M h) a x +
            (Formalization.Books.Sheaves.Unit04.directSumRestriction M h) b x) := by
          rw [map_add]
          rfl
        _ = a ⟨x.1, h x.2⟩ + b ⟨x.1, h x.2⟩ := by rw [ha, hb]
        _ = (a + b) ⟨x.1, h x.2⟩ :=
          (DirectSum.add_apply a b ⟨x.1, h x.2⟩).symm
  refine (setSheaf_iff_unique_gluing (directSumPresheafOfSets M)).2 ?_
  intro ι U s hs
  change (∀ i, (⨁ x : U i, M x)) at s
  let W : Opens X := iSup U
  obtain ⟨t, ht⟩ := (hcompact W).elim_finite_subcover
    (fun i : ι => (U i : Set X)) (fun i => (U i).2) (by
      intro x hx
      rw [Opens.coe_iSup] at hx
      exact hx)
  have hxcover (x : W) : ∃ i, i ∈ t ∧ (x : X) ∈ U i := by
    have hx := ht x.property
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨i, hi, hxi⟩
    exact ⟨i, hi, hxi⟩
  choose iOf hiT hiU using hxcover
  let xIn (x : W) : U (iOf x) := ⟨x.1, hiU x⟩
  let f : ∀ x : W, M x := fun x => s (iOf x) (xIn x)
  let embed (i : ι) (x : U i) : W :=
    Opens.leSupr U i x
  let S : Finset W := t.biUnion (fun i => (s i).support.image (embed i))
  have hf_outside (x : W) (hx : x ∉ S) : f x = 0 := by
    by_contra hfx
    apply hx
    refine Finset.mem_biUnion.mpr ⟨iOf x, hiT x, ?_⟩
    refine Finset.mem_image.mpr ⟨xIn x, ?_, ?_⟩
    · exact DFinsupp.mem_support_iff.mpr (by simpa [f] using hfx)
    · apply Subtype.ext
      rfl
  let g : ⨁ x : W, M x :=
    DirectSum.mk (fun x : W => M x) S (fun x : (↑S : Set W) => f x)
  have hg_f (x : W) : g x = f x := by
    by_cases hx : x ∈ S
    · simp only [g, DirectSum.mk_apply_of_mem hx]
    · simp only [g, DirectSum.mk_apply_of_notMem hx, hf_outside x hx]
  have hpoint (i j : ι) (x : (U i ⊓ U j : Opens X)) :
      s i ⟨x.1, x.2.1⟩ = s j ⟨x.1, x.2.2⟩ := by
    have h := hs i j
    change Formalization.Books.Sheaves.Unit04.directSumRestriction M
        (Opens.infLELeft (U i) (U j)).le (s i) =
      Formalization.Books.Sheaves.Unit04.directSumRestriction M
        (Opens.infLERight (U i) (U j)).le (s j) at h
    have h' := congrArg (fun q => q x) h
    simpa only [restriction_apply] using h'
  have hglue : IsGluingSections (F := directSumPresheafOfSets M) U s g := by
    intro i
    apply DirectSum.ext
    intro x
    change Formalization.Books.Sheaves.Unit04.directSumRestriction M
        (Opens.leSupr U i).le g x = s i x
    rw [restriction_apply]
    change g (embed i x) = s i x
    let y : W := embed i x
    have hchosen :
        s i x = s (iOf y) (⟨y.1, hiU y⟩ : U (iOf y)) := by
      apply hpoint i (iOf y)
        ⟨x.1, x.2, hiU y⟩
    calc
      g (embed i x) = f (embed i x) := hg_f _
      _ = s (iOf y) (xIn y) := by rfl
      _ = s i x := hchosen.symm
  refine ⟨g, hglue, ?_⟩
  intro g' hg'
  change (⨁ x : (iSup U : Opens X), M x) at g'
  apply DirectSum.ext
  intro x
  have hlocal := hg' (iOf x)
  change Formalization.Books.Sheaves.Unit04.directSumRestriction M
      (Opens.leSupr U (iOf x)).le g' = s (iOf x) at hlocal
  have hlocal' := congrArg (fun q => q (xIn x)) hlocal
  have hglobal := hglue (iOf x)
  change Formalization.Books.Sheaves.Unit04.directSumRestriction M
      (Opens.leSupr U (iOf x)).le g = s (iOf x) at hglobal
  have hglobal' := congrArg (fun q => q (xIn x)) hglobal
  rw [restriction_apply] at hlocal' hglobal'
  change g' (Opens.leSupr U (iOf x) (xIn x)) = _ at hlocal'
  change g (Opens.leSupr U (iOf x) (xIn x)) = _ at hglobal'
  have hlocal'' : g' x = (s (iOf x)) (xIn x) := by
    simpa only [xIn, Opens.leSupr_apply_mk, Subtype.coe_eta] using hlocal'
  have hglobal'' : g x = (s (iOf x)) (xIn x) := by
    simpa only [xIn, Opens.leSupr_apply_mk, Subtype.coe_eta] using hglobal'
  exact hlocal''.trans hglobal''.symm

end Formalization.Books.Sheaves.Unit07
