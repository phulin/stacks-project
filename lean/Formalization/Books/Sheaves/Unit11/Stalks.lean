import Formalization.Books.Sheaves.Unit07.Sheaves
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Order.Filter.Germ.Basic

/-!
# Sheaves on Spaces, Chapter 11: Stalks

The source span `books/sheaves.tex:893-1049` is the section `Stalks`.  The
stalk, germ, and stalk-functor constructions are Mathlib's canonical filtered
colimit constructions.  This file adds the source-facing maps and statements
that are specific to the section, reusing the set-valued sheaves and
pointwise-product sheaves from Chapter 7.

The source's quotient notation for a stalk is recorded by
`germ_eq_iff_common_restriction`; it is not implemented as a second quotient
type.  The smooth-function example uses Mathlib's canonical smooth sheaf,
whose sections are the expected `C^∞` maps on open subsets of Euclidean space.
-/

namespace Formalization.Books.Sheaves.Unit11

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit07
open scoped ContDiff Manifold

universe w v

/-! ## Stalks, germs, and the stalk functor -/

/-- The stalk of a set-valued presheaf, using Mathlib's filtered colimit. -/
abbrev Stalk {X : TopCat.{w}} (F : TopCat.Presheaf (Type w) X) (x : X) : Type w :=
  TopCat.Presheaf.stalk F x

/-- The stalk functor at a point, using the canonical presheaf functor. -/
noncomputable abbrev StalkFunctor {X : TopCat.{w}} (x : X) :
    TopCat.Presheaf (Type w) X ⥤ Type w :=
  TopCat.Presheaf.stalkFunctor (Type w) x

/-- The map on stalks induced by a morphism of presheaves. -/
noncomputable abbrev StalkMap {X : TopCat.{w}} {F G : TopCat.Presheaf (Type w) X}
    (φ : F ⟶ G) (x : X) : Stalk F x ⟶ Stalk G x :=
  (StalkFunctor x).map φ

/-!
`TopCat.Presheaf.stalk` is definitionally the colimit over the opposite of
`OpenNhds x`; this supplies the reverse-inclusion indexing used in the source,
and `TopCat.Presheaf.germ` is the canonical colimit coprojection.  Thus no
parallel colimit or quotient implementation is introduced here.
-/

/-- Apply the canonical germ morphism to a section. -/
noncomputable abbrev germApply {X : TopCat.{w}} {F : TopCat.Presheaf (Type w) X}
    (U : Opens X) (x : X) (hx : x ∈ U) (s : Sections F U) : Stalk F x :=
  ConcreteCategory.hom (F.germ U x hx) s

/-- The source's explicit quotient criterion for equality of germs. -/
theorem germ_eq_iff_common_restriction
    {X : TopCat.{w}} {F : TopCat.Presheaf (Type w) X}
    {U V : Opens X} (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : Sections F U) (t : Sections F V) :
    germApply (F := F) U x hxU s = germApply (F := F) V x hxV t ↔
      ∃ (W : Opens X) (hxW : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ V),
        F.map (homOfLE hWU).op s = F.map (homOfLE hWV).op t := by
  constructor
  · intro h
    rcases F.germ_eq x hxU hxV s t h with ⟨W, hxW, iWU, iWV, h⟩
    refine ⟨W, hxW, iWU.le, iWV.le, ?_⟩
    simpa [show iWU = homOfLE iWU.le from Subsingleton.elim _ _,
      show iWV = homOfLE iWV.le from Subsingleton.elim _ _] using h
  · rintro ⟨W, hxW, hWU, hWV, h⟩
    exact F.germ_ext W hxW (homOfLE hWU) (homOfLE hWV) h

/-- The canonical map from sections on `U` to the product of their stalks. -/
noncomputable def sectionToStalks {X : TopCat.{w}} {F : TopCat.Presheaf (Type w) X} (U : Opens X) :
    Sections F U → ∀ x : U, Stalk F x.1 :=
  fun s x => germApply (F := F) U x.1 x.2 s

/-- The source's injectivity lemma for a sheaf. -/
theorem sectionToStalks_injective_of_isSheaf
    {X : TopCat.{w}} {F : TopCat.Presheaf (Type w) X} (hF : SetSheaf F)
    (U : Opens X) :
    Function.Injective (sectionToStalks (F := F) U) := by
  intro s t h
  apply hF.section_ext
  intro x hx
  have hst := congr_fun h ⟨x, hx⟩
  rcases (germ_eq_iff_common_restriction x hx hx s t).mp hst with
    ⟨V, hxV, hVU, hVU', h⟩
  refine ⟨V, hVU, hxV, ?_⟩
  simpa [show hVU' = hVU from Subsingleton.elim _ _] using h

/-- A presheaf is separated when sections are determined by all their germs. -/
def SeparatedPresheaf {X : TopCat.{w}} (F : TopCat.Presheaf (Type w) X) : Prop :=
  ∀ U : Opens X, Function.Injective (sectionToStalks (F := F) U)

/-- Every sheaf of sets is separated in the stalk sense. -/
theorem separatedPresheaf_of_isSheaf
    {X : TopCat.{w}} {F : TopCat.Presheaf (Type w) X} (hF : SetSheaf F) :
    SeparatedPresheaf F := by
  intro U
  exact sectionToStalks_injective_of_isSheaf hF U

/-- Stalk functoriality on the germ of a section. -/
theorem stalkMap_germ
    {X : TopCat.{w}} {F G : TopCat.Presheaf (Type w) X} (φ : F ⟶ G)
    {U : Opens X} (x : X) (hx : x ∈ U) (s : Sections F U) :
    StalkMap φ x (germApply (F := F) U x hx s) =
      germApply (F := G) U x hx (φ.app (op U) s) := by
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx φ s

/-! ## The constant-presheaf example -/

/-- The canonical map from the constant presheaf to the constant sheaf. -/
noncomputable def constantPresheafToConstantSheaf
    {X : TopCat.{w}} (A : Type w) :
    constantPresheaf (X := X) A ⟶
      (constantSheaf X A).presheaf where
  app U := letI : TopologicalSpace A := ⊥
    TypeCat.ofHom (show A → ((Opens.toTopCat X).obj U.unop ⟶ TopCat.discrete.obj A) from
      fun a => TopCat.ofHom (ContinuousMap.const ((Opens.toTopCat X).obj U.unop) a))
  naturality := by
    intro U V i
    apply ConcreteCategory.hom_ext _ _
    intro a
    apply TopCat.hom_ext
    rfl

/-- The canonical map from `A` into the stalk of the constant presheaf. -/
noncomputable def constantPresheafStalkMap {X : TopCat.{w}} (A : Type w) (x : X) :
    A → Stalk (constantPresheaf (X := X) A) x :=
  fun a =>
    germApply (F := constantPresheaf (X := X) A) (⊤ : Opens X) x (by simp) a

/-- The constant presheaf has stalk `A`. -/
theorem constantPresheafStalkMap_bijective
    {X : TopCat.{w}} (A : Type w) (x : X) :
    Function.Bijective (constantPresheafStalkMap A x) := by
  constructor
  · intro a b h
    rcases (constantPresheaf (X := X) A).germ_eq x (by simp) (by simp) a b h with
      ⟨W, hxW, iW, iW', h⟩
    have hiW : iW = homOfLE iW.le := Subsingleton.elim _ _
    have hiW' : iW' = homOfLE iW'.le := Subsingleton.elim _ _
    simpa [hiW, hiW'] using (show a = b from by
      change a = b at h
      exact h)
  · intro z
    rcases (constantPresheaf (X := X) A).exists_germ_eq z with ⟨U, hxU, s, hs⟩
    let a : A := s
    let sTop : Sections (constantPresheaf (X := X) A) (⊤ : Opens X) := a
    refine ⟨a, ?_⟩
    change ConcreteCategory.hom
      ((constantPresheaf (X := X) A).germ (⊤ : Opens X) x (by simp)) sTop = z
    rw [← hs]
    rw [← (constantPresheaf (X := X) A).germ_res_apply
      (homOfLE (show U ≤ (⊤ : Opens X) from le_top)) x hxU sTop]
    have hrestrict :
        (constantPresheaf (X := X) A).map
            (homOfLE (show U ≤ (⊤ : Opens X) from le_top)).op sTop = s := by
      rw [constantPresheaf_map]
      dsimp [sTop, a]
      rfl
    rw [hrestrict]

/-- A canonical equivalence between `A` and the stalk of the constant presheaf. -/
noncomputable def constantPresheafStalkEquiv
    {X : TopCat.{w}} (A : Type w) (x : X) :
    A ≃ Stalk (constantPresheaf (X := X) A) x :=
  Equiv.ofBijective (constantPresheafStalkMap A x)
    (constantPresheafStalkMap_bijective A x)

/-- The map on stalks induced by the constant-presheaf-to-constant-sheaf map. -/
noncomputable def constantSheafStalkMap {X : TopCat.{w}} (A : Type w) (x : X) :
    Stalk (constantPresheaf (X := X) A) x →
      Stalk (constantSheaf X A).presheaf x :=
  StalkMap (constantPresheafToConstantSheaf A) x

/-- The constant sheaf has stalk `A`. -/
theorem constantSheafStalkMap_bijective
    {X : TopCat.{w}} (A : Type w) (x : X) :
    Function.Bijective (constantSheafStalkMap A x) := by
  constructor
  · intro z z' h
    rcases (constantPresheafStalkMap_bijective A x).surjective z with ⟨a, ha⟩
    rcases (constantPresheafStalkMap_bijective A x).surjective z' with ⟨b, hb⟩
    let aTop : Sections (constantPresheaf (X := X) A) (⊤ : Opens X) := a
    let bTop : Sections (constantPresheaf (X := X) A) (⊤ : Opens X) := b
    have hsource :
        StalkMap (constantPresheafToConstantSheaf A) x
            (germApply (F := constantPresheaf (X := X) A) (⊤ : Opens X) x (by simp) aTop) =
          StalkMap (constantPresheafToConstantSheaf A) x
            (germApply (F := constantPresheaf (X := X) A) (⊤ : Opens X) x (by simp) bTop) := by
      rw [← ha, ← hb] at h
      exact h
    have h' :
        germApply (F := (constantSheaf X A).presheaf) (⊤ : Opens X) x (by simp)
            ((constantPresheafToConstantSheaf A).app (op (⊤ : Opens X)) aTop) =
          germApply (F := (constantSheaf X A).presheaf) (⊤ : Opens X) x (by simp)
            ((constantPresheafToConstantSheaf A).app (op (⊤ : Opens X)) bTop) := by
      calc
        germApply (F := (constantSheaf X A).presheaf) (⊤ : Opens X) x (by simp)
              ((constantPresheafToConstantSheaf A).app (op (⊤ : Opens X)) aTop) =
            StalkMap (constantPresheafToConstantSheaf A) x
              (germApply (F := constantPresheaf (X := X) A) (⊤ : Opens X) x (by simp) aTop) :=
          (stalkMap_germ (constantPresheafToConstantSheaf A) x (by simp) aTop).symm
        _ = StalkMap (constantPresheafToConstantSheaf A) x
              (germApply (F := constantPresheaf (X := X) A) (⊤ : Opens X) x (by simp) bTop) := hsource
        _ = germApply (F := (constantSheaf X A).presheaf) (⊤ : Opens X) x (by simp)
              ((constantPresheafToConstantSheaf A).app (op (⊤ : Opens X)) bTop) :=
          stalkMap_germ (constantPresheafToConstantSheaf A) x (by simp) bTop
    rcases (constantSheaf X A).presheaf.germ_eq x (by simp) (by simp)
      ((constantPresheafToConstantSheaf A).app (op (⊤ : Opens X)) a)
      ((constantPresheafToConstantSheaf A).app (op (⊤ : Opens X)) b) h' with
      ⟨W, hxW, iW, iW', hW⟩
    have hW' := congrArg (fun q => (ConcreteCategory.hom q) ⟨x, hxW⟩) hW
    change a = b at hW'
    exact ha.symm.trans ((congrArg (constantPresheafStalkMap A x) hW').trans hb)
  · intro z
    rcases (constantSheaf X A).presheaf.exists_germ_eq z with ⟨U, hxU, s, hs⟩
    let _ : TopologicalSpace A := ⊥
    have hs_local : IsLocallyConstant (s.hom : U → A) :=
      (continuous_iff_locallyConstant_of_discrete (s.hom : U → A)).mp s.hom.continuous
    rcases hs_local.exists_open ⟨x, hxU⟩ with ⟨O, hO, hxO, hOconst⟩
    rcases (mem_nhds_subtype (U : Set X) ⟨x, hxU⟩ O).1 (hO.mem_nhds hxO) with
      ⟨u, hu, huO⟩
    rcases mem_nhds_iff.mp hu with ⟨V, hVu, hVopen, hxV⟩
    let W : Opens X := ⟨V ∩ U, hVopen.inter U.2⟩
    have hxW : x ∈ W := ⟨hxV, hxU⟩
    have hWU : W ≤ U := by
      intro y hy
      exact hy.2
    let a : A := s.hom ⟨x, hxU⟩
    let aTop : Sections (constantPresheaf (X := X) A) (⊤ : Opens X) := a
    refine ⟨constantPresheafStalkMap A x a, ?_⟩
    have hstalk :
        constantSheafStalkMap A x (constantPresheafStalkMap A x a) =
          germApply (F := (constantSheaf X A).presheaf) (⊤ : Opens X) x (by simp)
            ((constantPresheafToConstantSheaf A).app (op (⊤ : Opens X)) aTop) := by
      exact stalkMap_germ (constantPresheafToConstantSheaf A) x (by simp) aTop
    rw [hstalk, ← hs]
    apply (constantSheaf X A).presheaf.germ_ext W hxW
      (homOfLE (show W ≤ (⊤ : Opens X) from le_top)) (homOfLE hWU)
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    have hyV : y.1 ∈ V := y.2.1
    have hyU : y.1 ∈ U := y.2.2
    have hyu : y.1 ∈ u := hVu hyV
    have hyO : (⟨y.1, hyU⟩ : U) ∈ O :=
      huO (show (⟨y.1, hyU⟩ : U).1 ∈ u from hyu)
    change s.hom ⟨x, hxU⟩ = s.hom ⟨y.1, hyU⟩
    exact (hOconst _ hyO).symm

/-- The canonical bijection `A ≅ (A_p)_x ≅ \underline A_x`. -/
noncomputable def constantSheafStalkEquiv
    {X : TopCat.{w}} (A : Type w) (x : X) :
    A ≃ Stalk (constantSheaf X A).presheaf x :=
  (constantPresheafStalkEquiv A x).trans
    (Equiv.ofBijective (constantSheafStalkMap A x)
      (constantSheafStalkMap_bijective A x))

/-! ## Smooth functions and their germs -/

/-- The sheaf of smooth real-valued functions on `ℝ^n`, in Mathlib's
coordinate model `Fin n → ℝ`. -/
noncomputable abbrev smoothFunctionsSheaf (n : ℕ) :
    TopCat.Sheaf (Type) (TopCat.of (Fin n → ℝ)) :=
  smoothSheaf (𝓘(ℝ, Fin n → ℝ)) 𝓘(ℝ) (Fin n → ℝ) ℝ

/-- The presheaf underlying the smooth-function sheaf. -/
noncomputable abbrev smoothFunctionsPresheaf (n : ℕ) :=
  (smoothFunctionsSheaf n).presheaf

/-- Its sections over an open are the expected `C^∞` functions. -/
@[simp]
theorem smoothFunctionsPresheaf_obj (n : ℕ)
    (U : Opens (TopCat.of (Fin n → ℝ))) :
    (smoothFunctionsPresheaf n).obj (op U) =
      C^∞⟮𝓘(ℝ, Fin n → ℝ), U; 𝓘(ℝ), ℝ⟯ := by
  rfl

/-- Every space of smooth sections is a real vector space. -/
noncomputable instance smoothFunctionsSections_module (n : ℕ)
    (U : Opens (TopCat.of (Fin n → ℝ))) :
    Module ℝ ((smoothFunctionsPresheaf n).obj (op U)) := by
  change Module ℝ C^∞⟮𝓘(ℝ, Fin n → ℝ), U; 𝓘(ℝ), ℝ⟯
  infer_instance

/-- Evaluation of a smooth germ at its base point. -/
noncomputable abbrev smoothFunctionsStalkEvaluation (n : ℕ)
    (x : Fin n → ℝ) :
    Stalk (smoothFunctionsPresheaf n) x → ℝ :=
  smoothSheaf.eval (𝓘(ℝ, Fin n → ℝ)) 𝓘(ℝ) ℝ x

@[simp]
theorem smoothFunctionsStalkEvaluation_germ (n : ℕ)
    (U : Opens (TopCat.of (Fin n → ℝ))) (x : Fin n → ℝ) (hx : x ∈ U)
    (f : (smoothFunctionsPresheaf n).obj (op U)) :
    smoothFunctionsStalkEvaluation n x
        (germApply (F := smoothFunctionsPresheaf n) U x hx f) = f.1 ⟨x, hx⟩ := by
  exact smoothSheaf.eval_germ U x hx f

/-! ## Pointwise products and the stalk warning -/

/-!
The pointwise-product presheaf and its sheaf property are already provided by
`Unit07.pointwiseProductPresheaf` and
`Unit07.pointwiseProductPresheaf_isSheaf`.  The following cocone is the
canonical evaluation cocone at a point; its colimit descent is the map
`F_x → A_x` mentioned in the source.
-/

/-- The evaluation cocone for the pointwise-product presheaf at `x`. -/
noncomputable def pointwiseProductEvaluationCocone
    {X : TopCat.{v}} (A : X → Type v) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ pointwiseProductPresheaf A) where
  pt := A x
  ι := { app := fun U => ↾fun s => s ⟨x, (unop U).2⟩
         naturality := by
           intro U V i
           ext s
           rfl }

/-- The canonical map from the pointwise-product stalk to its fiber at `x`. -/
noncomputable def pointwiseProductStalkEvaluation
    {X : TopCat.{v}} (A : X → Type v) (x : X) :
    Stalk (pointwiseProductPresheaf A) x → A x :=
  colimit.desc _ (pointwiseProductEvaluationCocone A x)

@[simp]
theorem pointwiseProductStalkEvaluation_germ
    {X : TopCat.{v}} (A : X → Type v) (U : Opens X) (x : X) (hx : x ∈ U)
    (s : (pointwiseProductPresheaf A).obj (op U)) :
        pointwiseProductStalkEvaluation A x
        (germApply (F := pointwiseProductPresheaf A) U x hx s) = s ⟨x, hx⟩ := by
  simp only [pointwiseProductStalkEvaluation, germApply]
  exact colimit.ι_desc_apply (pointwiseProductEvaluationCocone A x)
    (op (⟨U, hx⟩ : OpenNhds x)) s

/-- The type of tails of binary sequences, i.e. binary sequences modulo
eventual equality. -/
abbrev BinarySequenceTail :=
  Filter.Germ (Filter.cofinite : Filter ℕ) Bool

/-- There are infinitely many binary sequence tails. -/
theorem binarySequenceTail_infinite : Infinite BinarySequenceTail := by
  let f : ℕ → ℕ → Bool := fun n k => decide (n + 1 ∣ k)
  have hseparate : ∀ {n m : ℕ}, n < m →
      (f n : BinarySequenceTail) ≠ (f m : BinarySequenceTail) := by
    intro n m hnm h
    have heq : f n =ᶠ[(Filter.cofinite : Filter ℕ)] f m :=
      Filter.Germ.coe_eq.mp h
    have hdiff : {k : ℕ | f n k ≠ f m k}.Infinite := by
      let g : ℕ → ℕ := fun r => (n + 1) * ((m + 1) * r + 1)
      have hg : Function.Injective g := by
        intro r s hrs
        apply Nat.mul_left_cancel (Nat.zero_lt_succ m)
        apply Nat.add_right_cancel
        exact Nat.mul_left_cancel (Nat.zero_lt_succ n) hrs
      apply Set.infinite_of_injective_forall_mem hg
      intro r
      have hde : n + 1 < m + 1 := Nat.succ_lt_succ hnm
      have hform : g r = ((n + 1) * r) * (m + 1) + (n + 1) := by
        dsimp [g]
        rw [Nat.mul_add]
        simp [Nat.mul_comm, Nat.mul_left_comm]
      have hmod : g r % (m + 1) = n + 1 := by
        rw [hform, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hde]
        simpa using hnm
      have hdvd : n + 1 ∣ g r := by
        refine ⟨(m + 1) * r + 1, ?_⟩
        rfl
      have hndvd : ¬m + 1 ∣ g r := by
        intro hdiv
        have hz : g r % (m + 1) = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
        rw [hmod] at hz
        exact (Nat.succ_ne_zero n) hz
      simp [f, hdvd, hndvd]
    exact hdiff (Filter.eventually_cofinite.mp heq)
  refine Infinite.of_injective (fun n => (f n : BinarySequenceTail)) ?_
  intro n m h
  by_contra hnm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hseparate hlt h
  · exact hseparate hgt h.symm

/-- A convergent sequence of distinct points produces all binary sequence
tails in the corresponding pointwise-product stalk. -/
theorem pointwiseProductStalk_surjects_binarySequenceTails
    {X : TopCat.{v}} (x : X) (xSeq : ℕ → X)
    (hlim : Filter.Tendsto xSeq Filter.atTop (𝓝 x))
    (hinj : Function.Injective xSeq) :
    ∃ q : TopCat.Presheaf.stalk
        (pointwiseProductPresheaf (fun _ : X => Bool)) x →
        BinarySequenceTail,
      Function.Surjective q := by
  classical
  let D := (OpenNhds.inclusion x).op ⋙
    pointwiseProductPresheaf (fun _ : X => Bool)
  let tailMap : ∀ U : (OpenNhds x)ᵒᵖ,
      (pointwiseProductPresheaf (fun _ : X => Bool)).obj
        ((OpenNhds.inclusion x).op.obj U) → BinarySequenceTail :=
    fun U s =>
      (fun n => if hn : xSeq n ∈ (unop U).1 then
        s ⟨xSeq n, hn⟩ else false : BinarySequenceTail)
  have hEventually : ∀ U : (OpenNhds x),
      ∀ᶠ n in Filter.atTop, xSeq n ∈ U.1 := by
    intro U
    exact hlim (U.1.isOpen.mem_nhds U.2)
  let c : Cocone D :=
    { pt := ULift.{v} BinarySequenceTail
      ι :=
        { app := fun U => ↾fun s => ULift.up (tailMap U s)
          naturality := by
            intro U V i
            apply ConcreteCategory.hom_ext _ _
            intro s
            change ULift.up (tailMap V (D.map i s)) = ULift.up (tailMap U s)
            congr 1
            apply Filter.Germ.coe_eq.2
            have hn' : ∀ᶠ n in (Filter.cofinite : Filter ℕ),
                xSeq n ∈ (unop V).1 := by
              simpa [Nat.cofinite_eq_atTop] using hEventually (unop V)
            filter_upwards [hn'] with n hn
            have hnU : xSeq n ∈ (unop U).1 := i.unop.le hn
            simp only [dif_pos hn, dif_pos hnU]
            have hnV' : xSeq n ∈
                (unop ((OpenNhds.inclusion x).op.obj V)).1 := by
              change xSeq n ∈ (unop V).1
              exact hn
            have hnU' : xSeq n ∈
                (unop ((OpenNhds.inclusion x).op.obj U)).1 := by
              change xSeq n ∈ (unop U).1
              exact hnU
            have hrestrict :
                TopCat.Presheaf.restrict (F :=
                  pointwiseProductPresheaf (fun _ : X => Bool)) s
                    ((OpenNhds.inclusion x).map i.unop) =
                  fun y => s (((OpenNhds.inclusion x).map i.unop) y) := by
              exact pointwiseProductPresheaf_restriction
                (fun _ : X => Bool) ((OpenNhds.inclusion x).map i.unop) s
            have hrestrict' := congrArg
              (fun r => r ⟨xSeq n, hnV'⟩) hrestrict
            simpa [D, TopCat.Presheaf.restrict] using hrestrict' } }
  let qLift : TopCat.Presheaf.stalk
      (pointwiseProductPresheaf (fun _ : X => Bool)) x →
      ULift.{v} BinarySequenceTail :=
    ConcreteCategory.hom (colimit.desc _ c)
  let q : TopCat.Presheaf.stalk
      (pointwiseProductPresheaf (fun _ : X => Bool)) x →
      BinarySequenceTail :=
    fun t => (qLift t).down
  refine ⟨q, ?_⟩
  intro t
  refine Filter.Germ.inductionOn t ?_
  intro b
  let s : (pointwiseProductPresheaf (fun _ : X => Bool)).obj (op (⊤ : Opens X)) :=
    fun y => if hy : ∃ n, xSeq n = y.1 then b (Classical.choose hy) else false
  have hs : ∀ n : ℕ, s ⟨xSeq n, by simp⟩ = b n := by
    intro n
    have hn : ∃ k, xSeq k = xSeq n := ⟨n, rfl⟩
    have hchoose : Classical.choose hn = n :=
      hinj (Classical.choose_spec hn)
    simp [s, hn, hchoose]
  refine ⟨germApply
      (F := pointwiseProductPresheaf (fun _ : X => Bool)) (⊤ : Opens X) x (by simp) s, ?_⟩
  change q (germApply
      (F := pointwiseProductPresheaf (fun _ : X => Bool)) (⊤ : Opens X) x (by simp) s) =
    (b : BinarySequenceTail)
  rw [show q (germApply
      (F := pointwiseProductPresheaf (fun _ : X => Bool)) (⊤ : Opens X) x (by simp) s) =
      tailMap (op (⟨⊤, by simp⟩ : OpenNhds x)) s by
    change (qLift (germApply
      (F := pointwiseProductPresheaf (fun _ : X => Bool)) (⊤ : Opens X) x (by simp) s)).down =
      tailMap (op (⟨⊤, by simp⟩ : OpenNhds x)) s
    exact congrArg ULift.down (colimit.ι_desc_apply c
      (op (⟨⊤, by simp⟩ : OpenNhds x)) s)]
  apply Filter.Germ.coe_eq.2
  filter_upwards [] with n
  simp [hs n]

/-- Under the preceding hypotheses, the pointwise-product stalk is not the
fiber `Bool` at the limit point. -/
theorem pointwiseProductStalk_not_equiv_bool_of_limit_sequence
    {X : TopCat.{v}} (x : X) (xSeq : ℕ → X)
    (hlim : Filter.Tendsto xSeq Filter.atTop (𝓝 x))
    (hinj : Function.Injective xSeq) :
    ¬ Nonempty (TopCat.Presheaf.stalk
      (pointwiseProductPresheaf (fun _ : X => Bool)) x ≃ Bool) := by
  rintro ⟨e⟩
  let _ : Infinite BinarySequenceTail := binarySequenceTail_infinite
  rcases pointwiseProductStalk_surjects_binarySequenceTails x xSeq hlim hinj with
    ⟨q, hq⟩
  have hfinite : Finite (TopCat.Presheaf.stalk
      (pointwiseProductPresheaf (fun _ : X => Bool)) x) :=
    Finite.of_injective e e.injective
  exact (Infinite.of_surjective q hq).not_finite hfinite

/-- If every neighborhood of `x` contains an empty fiber, the pointwise-
product stalk at `x` is empty. -/
theorem pointwiseProductStalk_isEmpty_of_empty_fiber_near
    {X : TopCat.{v}} (A : X → Type v) (x : X)
    (hEmpty : ∀ U : Opens X, x ∈ U →
      ∃ y : X, y ∈ U ∧ IsEmpty (A y)) :
    IsEmpty (TopCat.Presheaf.stalk (pointwiseProductPresheaf A) x) := by
  constructor
  intro t
  rcases (pointwiseProductPresheaf A).exists_germ_eq t with ⟨U, hxU, s, hs⟩
  rcases hEmpty U hxU with ⟨y, hyU, hAy⟩
  exact (hAy.false (s ⟨y, hyU⟩)).elim

end Formalization.Books.Sheaves.Unit11
