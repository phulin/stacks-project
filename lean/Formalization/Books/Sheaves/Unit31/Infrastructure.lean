import Formalization.Books.Sheaves.Unit30.Infrastructure
import Formalization.Books.Sheaves.Unit06.PresheavesOfModules
import Formalization.Books.Sheaves.Unit08.AbelianSheaves
import Formalization.Books.Sheaves.Unit17.Sheafification
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Stalks

/-!
# Shared infrastructure for Chapter 31: Open immersions

The restriction functors use Mathlib's pullback and open-subspace sheaf
restriction APIs.  Extension by the initial object is kept as a named
interface, since its concrete sectionwise construction depends on the value
category; its sheaf version is obtained by sheafification.
-/

namespace Formalization.Books.Sheaves.Unit22

-- The historical namespace is retained for API compatibility.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.Topology
open scoped ZeroObject
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit10

universe v u

noncomputable section

/-! ## Constant sheaves on a topological space -/

/-- The site-theoretic constant sheaf of types agrees with the concrete
sheaf of locally constant functions. -/
noncomputable def constantTypeSheafIso (X : TopCat.{v}) (A : Type v) :
    (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) (Type v)).obj A ≅
      Formalization.Books.Sheaves.Unit07.constantSheaf X A := by
  let P := Formalization.Books.Sheaves.Unit03.constantPresheaf (X := X) A
  let k :
      (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) (Type v)).obj A ⟶
        Formalization.Books.Sheaves.Unit07.constantSheaf X A :=
    ((CategoryTheory.sheafificationAdjunction
      (Opens.grothendieckTopology X) (Type v)).homEquiv P
        (Formalization.Books.Sheaves.Unit07.constantSheaf X A)).symm
        (Formalization.Books.Sheaves.Unit11.constantPresheafToConstantSheaf A)
  have hkcomp :
      CategoryTheory.toSheafify (Opens.grothendieckTopology X) P ≫ k.hom =
        Formalization.Books.Sheaves.Unit11.constantPresheafToConstantSheaf A :=
    by
      change
        ((CategoryTheory.sheafificationAdjunction
          (Opens.grothendieckTopology X) (Type v)).homEquiv P
            (Formalization.Books.Sheaves.Unit07.constantSheaf X A)) k = _
      exact ((CategoryTheory.sheafificationAdjunction
        (Opens.grothendieckTopology X) (Type v)).homEquiv P
          (Formalization.Books.Sheaves.Unit07.constantSheaf X A)).apply_symm_apply _
  have hk : IsIso k :=
    (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso k).2 (by
      intro x
      let u := (TopCat.Presheaf.stalkFunctor (Type v) x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)
      let m := (TopCat.Presheaf.stalkFunctor (Type v) x).map k.hom
      let w := (TopCat.Presheaf.stalkFunctor (Type v) x).map
        (Formalization.Books.Sheaves.Unit11.constantPresheafToConstantSheaf A)
      have hu : Function.Bijective u := by
        rw [← isIso_iff_bijective]
        exact
        TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type v) P
      have hw : Function.Bijective w := by
        exact Formalization.Books.Sheaves.Unit11.constantSheafStalkMap_bijective A x
      have huw : u ≫ m = w := by
        dsimp only [u, m, w]
        calc
          _ = (TopCat.Presheaf.stalkFunctor (Type v) x).map
                (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P ≫ k.hom) :=
            (Functor.map_comp _ _ _).symm
          _ = _ := congrArg
            (fun q => (TopCat.Presheaf.stalkFunctor (Type v) x).map q) hkcomp
      rw [isIso_iff_bijective]
      constructor
      · intro a b hab
        obtain ⟨a₀, ha₀⟩ := hu.2 a
        obtain ⟨b₀, hb₀⟩ := hu.2 b
        have ha := congrArg (fun q => q a₀) huw
        have hb := congrArg (fun q => q b₀) huw
        change m (u a₀) = w a₀ at ha
        change m (u b₀) = w b₀ at hb
        rw [ha₀] at ha
        rw [hb₀] at hb
        have hab₀ : a₀ = b₀ := hw.1 (ha.symm.trans (hab.trans hb))
        exact ha₀.symm.trans ((congrArg (fun z => u z) hab₀).trans hb₀)
      · intro b
        obtain ⟨a, ha⟩ := hw.2 b
        refine ⟨u a, ?_⟩
        have h := congrArg (fun q => q a) huw
        change m (u a) = w a at h
        exact h.trans ha)
  letI := hk
  exact asIso k

/-- After forgetting the additive structure, the site-theoretic constant
additive sheaf is the concrete sheaf of locally constant functions. -/
noncomputable def constantAddCommGrpSheafUnderlyingIso
    (X : TopCat.{v}) (A : AddCommGrpCat.{v}) :
    (((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj A).obj ⋙ CategoryTheory.forget AddCommGrpCat) ≅
      (Formalization.Books.Sheaves.Unit07.constantSheaf X A).presheaf := by
  exact (CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X) (Type v)).mapIso
        ((CategoryTheory.constantCommuteCompose
          (Opens.grothendieckTopology X)
          (CategoryTheory.forget AddCommGrpCat)).app A) ≪≫
    (CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X) (Type v)).mapIso
        (constantTypeSheafIso X A)

/-- A section of a constant additive sheaf, viewed as a locally constant
function after forgetting its additive structure. -/
noncomputable def constantAddCommGrpSheafSectionFunction
    {X : TopCat.{v}} (A : AddCommGrpCat.{v}) (U : Opens X)
    (s : ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj A).obj.obj (op U)) : U → A :=
  fun x => ConcreteCategory.hom (ConcreteCategory.hom
    ((constantAddCommGrpSheafUnderlyingIso X A).hom.app (op U)) s) x

/-- The locus where a section of a constant additive sheaf differs from the
zero section is clopen. -/
theorem constantAddCommGrpSheafSectionFunction_ne_zero_isClopen
    {X : TopCat.{v}} (A : AddCommGrpCat.{v}) (U : Opens X)
    (s : ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj A).obj.obj (op U)) :
    IsClopen {x : U |
      constantAddCommGrpSheafSectionFunction A U s x ≠
        constantAddCommGrpSheafSectionFunction A U 0 x} := by
  let e := constantAddCommGrpSheafUnderlyingIso X A
  let fs := e.hom.app (op U) s
  let fz := e.hom.app (op U) 0
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let h : U → A × A := fun x => (ConcreteCategory.hom fs x,
    ConcreteCategory.hom fz x)
  have hh : Continuous h :=
    (ConcreteCategory.hom fs).continuous.prodMk
      (ConcreteCategory.hom fz).continuous
  have hc : IsClopen {p : A × A | p.1 ≠ p.2} := isClopen_discrete _
  convert hc.preimage hh using 1
  ext x
  rfl

/-- For a section of a constant additive sheaf, vanishing of the germ is
detected by the value of the associated locally constant function. -/
theorem constantAddCommGrpSheaf_germ_eq_zero_iff
    {X : TopCat.{v}} (A : AddCommGrpCat.{v}) (U : Opens X)
    (s : ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj A).obj.obj (op U))
    (x : X) (hx : x ∈ U) :
    ConcreteCategory.hom
        (TopCat.Presheaf.germ
          (((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
            AddCommGrpCat.{v}).obj A).obj) U x hx) s = 0 ↔
      constantAddCommGrpSheafSectionFunction A U s ⟨x, hx⟩ =
        constantAddCommGrpSheafSectionFunction A U 0 ⟨x, hx⟩ := by
  let F : TopCat.Presheaf AddCommGrpCat.{v} X :=
    ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj A).obj
  let e := constantAddCommGrpSheafUnderlyingIso X A
  constructor
  · intro hs
    have hs' : ConcreteCategory.hom (F.germ U x hx) s =
        ConcreteCategory.hom (F.germ U x hx) 0 := by
      simpa only [map_zero] using hs
    rcases F.germ_eq x hx hx s 0 hs' with ⟨W, hxW, i₁, i₂, hres⟩
    have hi : i₂ = i₁ := Subsingleton.elim _ _
    subst i₂
    have heq := congrArg
      (fun z => ConcreteCategory.hom (e.hom.app (op W)) z) hres
    have hnat := e.hom.naturality i₁.op
    have hnat_s := ConcreteCategory.congr_hom hnat s
    have hnat_z := ConcreteCategory.congr_hom hnat (0 : F.obj (op U))
    change e.hom.app (op W) (F.map i₁.op s) =
      ((Formalization.Books.Sheaves.Unit07.constantSheaf X A).presheaf.map i₁.op)
        (e.hom.app (op U) s) at hnat_s
    change e.hom.app (op W) (F.map i₁.op 0) =
      ((Formalization.Books.Sheaves.Unit07.constantSheaf X A).presheaf.map i₁.op)
        (e.hom.app (op U) 0) at hnat_z
    have ht :
        ((Formalization.Books.Sheaves.Unit07.constantSheaf X A).presheaf.map i₁.op)
            (e.hom.app (op U) s) =
          ((Formalization.Books.Sheaves.Unit07.constantSheaf X A).presheaf.map i₁.op)
            (e.hom.app (op U) 0) := by
      calc
        _ = e.hom.app (op W) (F.map i₁.op s) := by simpa using hnat_s.symm
        _ = e.hom.app (op W) (F.map i₁.op 0) := heq
        _ = _ := by simpa using hnat_z
    have ht' := congrArg
      (fun z : (Formalization.Books.Sheaves.Unit07.constantSheaf X A).presheaf.obj
          (op W) => ConcreteCategory.hom z ⟨x, hxW⟩) ht
    change constantAddCommGrpSheafSectionFunction A U s (i₁ ⟨x, hxW⟩) =
      constantAddCommGrpSheafSectionFunction A U 0 (i₁ ⟨x, hxW⟩) at ht'
    have hix : i₁ ⟨x, hxW⟩ = (⟨x, hx⟩ : U) := by
      apply Subtype.ext
      rfl
    simpa [hix] using ht'
  · intro hs
    let S : Set U := {y |
      constantAddCommGrpSheafSectionFunction A U s y ≠
        constantAddCommGrpSheafSectionFunction A U 0 y}
    have hS := constantAddCommGrpSheafSectionFunction_ne_zero_isClopen A U s
    have hxS : (⟨x, hx⟩ : U) ∈ Sᶜ := by simpa [S] using hs
    let W : Opens X :=
      ⟨Subtype.val '' Sᶜ, U.isOpenEmbedding.isOpenMap Sᶜ hS.1.isOpen_compl⟩
    have hxW : x ∈ W := ⟨⟨x, hx⟩, hxS, rfl⟩
    have hWU : W ≤ U := by
      rintro y ⟨z, -, rfl⟩
      exact z.2
    let i : W ⟶ U := homOfLE hWU
    have ht :
        ((Formalization.Books.Sheaves.Unit07.constantSheaf X A).presheaf.map i.op)
            (e.hom.app (op U) s) =
          ((Formalization.Books.Sheaves.Unit07.constantSheaf X A).presheaf.map i.op)
            (e.hom.app (op U) 0) := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro y
      rcases y.2 with ⟨z, hz, hzy⟩
      have hz' : z ∉ S := hz
      have hval :
          constantAddCommGrpSheafSectionFunction A U s z =
            constantAddCommGrpSheafSectionFunction A U 0 z := not_ne_iff.mp hz'
      have hiyz : i y = z := by
        apply Subtype.ext
        exact hzy.symm
      change constantAddCommGrpSheafSectionFunction A U s (i y) =
        constantAddCommGrpSheafSectionFunction A U 0 (i y)
      simpa [hiyz] using hval
    have hnat := e.hom.naturality i.op
    have hnat_s := ConcreteCategory.congr_hom hnat s
    have hnat_z := ConcreteCategory.congr_hom hnat (0 : F.obj (op U))
    change e.hom.app (op W) (F.map i.op s) =
      ((Formalization.Books.Sheaves.Unit07.constantSheaf X A).presheaf.map i.op)
        (e.hom.app (op U) s) at hnat_s
    change e.hom.app (op W) (F.map i.op 0) =
      ((Formalization.Books.Sheaves.Unit07.constantSheaf X A).presheaf.map i.op)
        (e.hom.app (op U) 0) at hnat_z
    have heq : e.hom.app (op W) (F.map i.op s) =
        e.hom.app (op W) (F.map i.op 0) := by
      calc
        _ = ((Formalization.Books.Sheaves.Unit07.constantSheaf X A).presheaf.map i.op)
              (e.hom.app (op U) s) := by simpa using hnat_s
        _ = _ := ht
        _ = e.hom.app (op W) (F.map i.op 0) := by simpa using hnat_z.symm
    have hres : F.map i.op s = F.map i.op 0 :=
      (e.app (op W)).toEquiv.injective heq
    have hg : ConcreteCategory.hom (F.germ U x hx) s =
        ConcreteCategory.hom (F.germ U x hx) 0 :=
      F.germ_ext (hxU := hx) (hxV := hx) W hxW i i hres
    simpa only [map_zero] using hg

/-- The support of a section of an additive sheaf, inside its domain. -/
def additiveSectionSupport {X : TopCat.{v}}
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (U : Opens X)
    (s : F.presheaf.obj (op U)) : Set U :=
  {x | ConcreteCategory.hom (F.presheaf.germ U x.1 x.2) s ≠ 0}

/-- The support of a section of an additive sheaf is closed in its domain. -/
theorem additiveSectionSupport_isClosed {X : TopCat.{v}}
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (U : Opens X)
    (s : F.presheaf.obj (op U)) : IsClosed (additiveSectionSupport F U s) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  simp only [additiveSectionSupport, Set.mem_compl_iff, Set.mem_ofPred_eq,
    not_ne_iff] at hx
  have hx' : ConcreteCategory.hom (F.presheaf.germ U x.1 x.2) s =
      ConcreteCategory.hom (F.presheaf.germ U x.1 x.2) 0 := by
    simpa only [map_zero] using hx
  rcases F.presheaf.germ_eq x.1 x.2 x.2 s 0 hx' with
    ⟨W, hxW, i₁, i₂, hres⟩
  let O : Set U := (Subtype.val : U → X) ⁻¹' (W : Set X)
  have hOopen : IsOpen O := W.isOpen.preimage continuous_subtype_val
  refine Filter.mem_of_superset (hOopen.mem_nhds hxW) ?_
  intro y hy
  simp only [additiveSectionSupport, Set.mem_compl_iff, Set.mem_ofPred_eq,
    not_ne_iff]
  have hgy := F.presheaf.germ_ext (x := y.1) (hxU := y.2) (hxV := y.2)
    W hy i₁ i₂ hres
  simpa only [map_zero] using hgy

/-- An isomorphism of additive sheaves identifies the supports of
corresponding sections. -/
theorem additiveSectionSupport_map_iso {X : TopCat.{v}}
    (F G : TopCat.Sheaf AddCommGrpCat.{v} X)
    (e : F.presheaf ≅ G.presheaf)
    (U : Opens X) (s : F.presheaf.obj (op U)) :
    additiveSectionSupport G U (e.hom.app (op U) s) =
      additiveSectionSupport F U s := by
  ext x
  let ei := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x.1).mapIso
    e
  have hei : Function.Injective (ConcreteCategory.hom ei.hom) := by
    intro a b hab
    have hab' := congrArg (ConcreteCategory.hom ei.inv) hab
    have hleft : ConcreteCategory.hom ei.inv
        (ConcreteCategory.hom ei.hom a) = a := by
      change ConcreteCategory.hom (ei.hom ≫ ei.inv) a = a
      rw [ei.hom_inv_id]
      rfl
    have hright : ConcreteCategory.hom ei.inv
        (ConcreteCategory.hom ei.hom b) = b := by
      change ConcreteCategory.hom (ei.hom ≫ ei.inv) b = b
      rw [ei.hom_inv_id]
      rfl
    exact hleft.symm.trans (hab'.trans hright)
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply U x.1 x.2 e.hom s
  have h' : ConcreteCategory.hom (G.presheaf.germ U x.1 x.2)
        (e.hom.app (op U) s) =
      ConcreteCategory.hom ei.hom
        (ConcreteCategory.hom (F.presheaf.germ U x.1 x.2) s) := by
    simpa [ei] using h.symm
  simp only [additiveSectionSupport, Set.mem_ofPred_eq]
  rw [h']
  constructor
  · intro hs hs0
    apply hs
    calc
      _ = ConcreteCategory.hom ei.hom 0 := congrArg _ hs0
      _ = 0 := map_zero _
  · intro hs hs0
    apply hs
    apply hei
    exact hs0.trans (map_zero _).symm

/-- Every section of a categorical constant additive sheaf has clopen
support. -/
theorem constantAddCommGrpSheaf_support_isClopen
    {X : TopCat.{v}} (A : AddCommGrpCat.{v}) (U : Opens X)
    (s : ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj A).obj.obj (op U)) :
    IsClopen (additiveSectionSupport
      ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{v}).obj A) U s) := by
  have h := constantAddCommGrpSheafSectionFunction_ne_zero_isClopen A U s
  convert h using 1
  ext x
  change (ConcreteCategory.hom (TopCat.Presheaf.germ
      (((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{v}).obj A).obj) U x.1 x.2) s ≠ 0) ↔
    constantAddCommGrpSheafSectionFunction A U s x ≠
      constantAddCommGrpSheafSectionFunction A U 0 x
  simpa using not_congr
    (constantAddCommGrpSheaf_germ_eq_zero_iff A U s x.1 x.2)

/-- A morphism from a constant additive sheaf has zero stalk map at a point
which admits a neighbourhood with no target sections. -/
theorem constantAddCommGrpSheaf_stalk_map_eq_zero_of_isZero
    {X : TopCat.{v}} (A : AddCommGrpCat.{v})
    (G : TopCat.Sheaf AddCommGrpCat.{v} X)
    (f : (CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj A ⟶ G)
    (V : Opens X) (x : X) (hx : x ∈ V)
    (hV : IsZero (G.presheaf.obj (op V))) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map f.hom = 0 := by
  let P : TopCat.Presheaf AddCommGrpCat.{v} X :=
    (Functor.const (Opens X)ᵒᵖ).obj A
  let K : TopCat.Sheaf AddCommGrpCat.{v} X :=
    (CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj A
  let η : P ⟶ K.presheaf :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology X) P
  let q : P ⟶ G.presheaf := η ≫ f.hom
  have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x AddCommGrpCat.{v} P
  apply (cancel_epi
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map η)).1
  rw [← Functor.map_comp]
  apply TopCat.Presheaf.stalk_hom_ext P
  intro U hxU
  let W := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hx⟩
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  have hqV : q.app (op V) = 0 := hV.eq_of_tgt _ _
  have hqW : q.app (op W) = 0 := by
    have hnat := q.naturality iWV.op
    rw [hqV, zero_comp] at hnat
    simpa [P] using hnat
  rw [TopCat.Presheaf.stalkFunctor_map_germ]
  calc
    q.app (op U) ≫ G.presheaf.germ U x hxU = 0 := by
      rw [← G.presheaf.germ_res iWU x hxW]
      rw [← Category.assoc, ← q.naturality iWU.op, hqW]
      simp only [comp_zero, zero_comp]
    _ = P.germ U x hxU ≫ 0 := (comp_zero).symm

/-! ## Restriction to an open subspace -/

/-- The topological space underlying an open subspace. -/
abbrev openSubspace {X : TopCat.{v}} (U : Opens X) : TopCat.{v} :=
  (Opens.toTopCat X).obj U

/-- The canonical open-subspace inclusion. -/
abbrev openInclusion {X : TopCat.{v}} (U : Opens X) : openSubspace U ⟶ X :=
  Opens.inclusion' U

/-- Pullback/restriction of presheaves to an open subspace. -/
noncomputable abbrev openPresheafRestriction (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C X ⥤ TopCat.Presheaf C (openSubspace U) :=
  TopCat.Presheaf.pullback C (openInclusion U)

/-- Direct image of presheaves along an open inclusion. -/
abbrev openPresheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C (openSubspace U) ⥤ TopCat.Presheaf C X :=
  TopCat.Presheaf.pushforward C (openInclusion U)

/-- Restriction of sheaves to an open subspace. -/
abbrev openSheafRestriction (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubspace U) :=
  TopologicalSpace.Opens.sheafRestrict U

/-- Direct image of sheaves along an open inclusion. -/
abbrev openSheafDirectImage (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Sheaf C (openSubspace U) ⥤ TopCat.Sheaf C X :=
  TopCat.Sheaf.pushforward C (openInclusion U)

/-- The presheaf underlying restriction to an open subspace is naturally
isomorphic to presheaf pullback. -/
noncomputable def openSheafRestrictionPresheafIso (C : Type u)
    [Category.{v} C] [HasColimits C] {X : TopCat.{v}} (U : Opens X) :
    openSheafRestriction C U ⋙ TopCat.Sheaf.forget C (openSubspace U) ≅
      TopCat.Sheaf.forget C X ⋙ openPresheafRestriction C U := by
  let H : IsOpenEmbedding
      (TopCat.Hom.hom (TopCat.ofHom ⟨_, continuous_subtype_val⟩)) :=
    U.isOpenEmbedding
  let : H.functor.IsContinuous (Opens.grothendieckTopology (openSubspace U))
      (Opens.grothendieckTopology X) := H.functor_isContinuous
  exact (H.isOpenMap.functor.sheafPushforwardContinuousCompSheafToPresheafIso
      C (Opens.grothendieckTopology (openSubspace U))
      (Opens.grothendieckTopology X)) ≪≫
    Functor.isoWhiskerLeft (TopCat.Sheaf.forget C X)
      H.isOpenMap.pullbackIso.symm

/-- The presheaf restriction is the canonical pullback construction. -/
theorem openPresheafRestriction_formula (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C X) :
    Nonempty ((openPresheafRestriction C U).obj F ≅
      (TopCat.Presheaf.pullback C (openInclusion U)).obj F) := by
  exact ⟨Iso.refl _⟩

/-- Restriction to an open subspace is computed by taking sections over the
image open in the ambient space. -/
noncomputable def openPresheafRestriction_obj_iso (C : Type u)
    [Category.{v} C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C X) (V : Opens (openSubspace U)) :
    ((openPresheafRestriction C U).obj F).obj (op V) ≅
      F.obj (op ⟨(openInclusion U) '' V,
        (U.isOpenEmbedding.isOpenMap V V.2)⟩) := by
  exact TopCat.Presheaf.pullbackObjObjOfImageOpen
    (openInclusion U) F V (U.isOpenEmbedding.isOpenMap V V.2)

/-- The presheaf of the restricted sheaf, written directly as ambient
sections on image opens. -/
noncomputable def openSheafRestrictionImageIso (C : Type u)
    [Category.{v} C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Sheaf C X) :
    ((openSheafRestriction C U).obj F).presheaf ≅
      U.isOpenEmbedding.isOpenMap.functor.op ⋙ F.presheaf :=
  (openSheafRestrictionPresheafIso C U).app F ≪≫
    U.isOpenEmbedding.isOpenMap.pullbackObjIso F.presheaf

/-- The open-subspace sheaf restriction has the corresponding presheaf. -/
theorem openSheafRestriction_formula (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C X) :
    Nonempty (((openSheafRestriction C U).obj F).presheaf ≅
      (openPresheafRestriction C U).obj F.presheaf) := by
  refine ⟨?_⟩
  let H : IsOpenEmbedding (TopCat.Hom.hom (TopCat.ofHom ⟨_, continuous_subtype_val⟩)) :=
    U.isOpenEmbedding
  let : H.functor.IsContinuous (Opens.grothendieckTopology (openSubspace U))
      (Opens.grothendieckTopology X) := H.functor_isContinuous
  exact (H.isOpenMap.functor.sheafPushforwardContinuousCompSheafToPresheafIso
      C (Opens.grothendieckTopology (openSubspace U))
      (Opens.grothendieckTopology X)).app F ≪≫
    (H.isOpenMap.pullbackObjIso F.presheaf).symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical stalk morphism for presheaf pullback is natural in the
presheaf. -/
theorem stalkPullbackHom_naturality (C : Type u) [Category.{v} C]
    [HasColimits C] {X Y : TopCat.{v}} (f : X ⟶ Y)
    {F G : TopCat.Presheaf C Y} (g : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor C (f x)).map g ≫
        TopCat.Presheaf.stalkPullbackHom C f G x =
      TopCat.Presheaf.stalkPullbackHom C f F x ≫
        (TopCat.Presheaf.stalkFunctor C x).map
          ((TopCat.Presheaf.pullback C f).map g) := by
  apply TopCat.Presheaf.stalk_hom_ext F
  intro V hV
  rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc V (f x) hV g
    (TopCat.Presheaf.stalkPullbackHom C f G x)]
  simp only [TopCat.Presheaf.germ_stalkPullbackHom]
  have hnat := NatTrans.congr_app
    ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.naturality g) (op V)
  change g.app (op V) ≫
      ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app G).app (op V) =
    ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app F).app (op V) ≫
      ((TopCat.Presheaf.pullback C f).map g).app (op ((Opens.map f).obj V)) at hnat
  rw [← Category.assoc, hnat]
  rw [TopCat.Presheaf.germ_stalkPullbackHom_assoc,
    TopCat.Presheaf.stalkFunctor_map_germ]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Pullback preserves the stalk at a point, naturally in the presheaf. -/
noncomputable def pullbackStalkIso (C : Type u) [Category.{v} C]
    [HasColimits C] {X Y : TopCat.{v}} (f : X ⟶ Y) (x : X) :
    TopCat.Presheaf.pullback C f ⋙ TopCat.Presheaf.stalkFunctor C x ≅
      TopCat.Presheaf.stalkFunctor C (f x) :=
  NatIso.ofComponents
    (fun F ↦ (TopCat.Presheaf.stalkPullbackIso C f F x).symm)
    (fun {F G} g ↦ by
      apply (cancel_epi (TopCat.Presheaf.stalkPullbackIso C f F x).hom).1
      change (TopCat.Presheaf.stalkPullbackIso C f F x).hom ≫
          (TopCat.Presheaf.stalkFunctor C x).map
            ((TopCat.Presheaf.pullback C f).map g) ≫
            (TopCat.Presheaf.stalkPullbackIso C f G x).inv =
        (TopCat.Presheaf.stalkPullbackIso C f F x).hom ≫
          (TopCat.Presheaf.stalkPullbackIso C f F x).inv ≫
            (TopCat.Presheaf.stalkFunctor C (f x)).map g
      calc
        _ = ((TopCat.Presheaf.stalkFunctor C (f x)).map g ≫
            (TopCat.Presheaf.stalkPullbackIso C f G x).hom) ≫
              (TopCat.Presheaf.stalkPullbackIso C f G x).inv := by
          simpa only [TopCat.Presheaf.stalkPullbackIso, Category.assoc] using congrArg
            (fun k ↦ k ≫ (TopCat.Presheaf.stalkPullbackIso C f G x).inv)
            (stalkPullbackHom_naturality C f g x).symm
        _ = (TopCat.Presheaf.stalkFunctor C (f x)).map g := by simp
        _ = ((TopCat.Presheaf.stalkPullbackIso C f F x).hom ≫
            (TopCat.Presheaf.stalkPullbackIso C f F x).inv) ≫
              (TopCat.Presheaf.stalkFunctor C (f x)).map g := by simp
        _ = _ := by simp)

set_option backward.isDefEq.respectTransparency false in
/-- For an open map, the section isomorphism over the image of an open is
compatible with the canonical pullback-stalk isomorphism. -/
theorem pullbackObjObjOfImageOpen_hom_germ (C : Type u) [Category.{v} C]
    [HasColimits C] {X Y : TopCat.{v}} (f : X ⟶ Y) (hf : IsOpenMap f)
    (F : TopCat.Presheaf C Y) (V : Opens X) (x : X) (hx : x ∈ V) :
    (TopCat.Presheaf.pullbackObjObjOfImageOpen f F V
        (hf (V : Set X) V.2)).hom ≫
        F.germ ⟨f '' V, hf (V : Set X) V.2⟩ (f x) ⟨x, hx, rfl⟩ =
      TopCat.Presheaf.germToPullbackStalk C f F V x hx := by
  dsimp [TopCat.Presheaf.pullbackObjObjOfImageOpen,
    TopCat.Presheaf.germToPullbackStalk]
  refine ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F
    (op V)).hom_ext (fun j ↦ ?_)
  rw [Limits.IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
    Limits.IsColimit.fac]
  dsimp
  apply F.germ_res

/-- Restriction to an open subspace preserves its stalks, naturally in the
ambient sheaf. -/
noncomputable def openSheafRestrictionStalkIso (C : Type u)
    [Category.{v} C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (u : openSubspace U) :
    openSheafRestriction C U ⋙ TopCat.Sheaf.forget C (openSubspace U) ⋙
        TopCat.Presheaf.stalkFunctor C u ≅
      TopCat.Sheaf.forget C X ⋙
        TopCat.Presheaf.stalkFunctor C ((openInclusion U) u) :=
  Functor.isoWhiskerRight (openSheafRestrictionPresheafIso C U)
      (TopCat.Presheaf.stalkFunctor C u) ≪≫
    Functor.isoWhiskerLeft (TopCat.Sheaf.forget C X)
      (pullbackStalkIso C (openInclusion U) u)

set_option backward.isDefEq.respectTransparency false in
/-- The image-open description of restriction carries germs to the
corresponding ambient germs. -/
theorem openSheafRestrictionImageIso_germ (C : Type u)
    [Category.{v} C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Sheaf C X) (V : Opens (openSubspace U))
    (x : U) (hx : x ∈ V) :
    ((openSheafRestriction C U).obj F).presheaf.germ V x hx ≫
        ((openSheafRestrictionStalkIso C U x).app F).hom =
      (openSheafRestrictionImageIso C U F).hom.app (op V) ≫
        F.presheaf.germ
          ⟨(openInclusion U) '' V,
            U.isOpenEmbedding.isOpenMap V V.2⟩
          ((openInclusion U) x) ⟨x, hx, rfl⟩ := by
  dsimp [openSheafRestrictionStalkIso, openSheafRestrictionImageIso,
    pullbackStalkIso, openPresheafRestriction,
    TopCat.Presheaf.stalkPullbackIso, IsOpenMap.pullbackObjIso]
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    Category.assoc, TopCat.Presheaf.germ_stalkPullbackInv,
    Category.assoc]
  let P := (TopCat.Sheaf.forget C X).obj F
  change ((openSheafRestrictionPresheafIso C U).hom.app F).app (op V) ≫
      TopCat.Presheaf.germToPullbackStalk C (openInclusion U) P V x hx =
    ((openSheafRestrictionPresheafIso C U).hom.app F).app (op V) ≫
      (TopCat.Presheaf.pullbackObjObjOfImageOpen (openInclusion U) P V
        (U.isOpenEmbedding.isOpenMap V V.2)).hom ≫
        P.germ ⟨(openInclusion U) '' V,
          U.isOpenEmbedding.isOpenMap V V.2⟩
          ((openInclusion U) x) ⟨x, hx, rfl⟩
  have hpb := pullbackObjObjOfImageOpen_hom_germ C (openInclusion U)
    U.isOpenEmbedding.isOpenMap P V x hx
  simpa only [Category.assoc] using congrArg
    (fun k ↦ ((openSheafRestrictionPresheafIso C U).hom.app F).app (op V) ≫ k)
    hpb.symm

/-- If a section is supported in an open on which the sheaf is constant,
then its support is open. -/
theorem additiveSectionSupport_isOpen_of_restrict_iso_constant
    {X : TopCat.{v}} (E : TopCat.Sheaf AddCommGrpCat.{v} X)
    (U : Opens X) (A : AddCommGrpCat.{v})
    (e : (openSheafRestriction AddCommGrpCat.{v} U).obj E ≅
      (CategoryTheory.constantSheaf
        (Opens.grothendieckTopology (openSubspace U))
        AddCommGrpCat.{v}).obj A)
    (V : Opens X) (s : E.presheaf.obj (op V))
    (hsupport : ∀ x : V, x ∈ additiveSectionSupport E V s → x.1 ∈ U) :
    IsOpen (additiveSectionSupport E V s) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hxU : x.1 ∈ U := hsupport x hx
  let W : Opens (openSubspace U) :=
    (Opens.map (openInclusion U)).obj V
  have hWmemV (y : W) : (openInclusion U) y.1 ∈ V := y.2
  let Q : Opens X :=
    ⟨(openInclusion U) '' W, U.isOpenEmbedding.isOpenMap W W.2⟩
  have hQV : Q ≤ V := by
    rintro z ⟨y, hy, rfl⟩
    exact hy
  let iQV : Q ⟶ V := homOfLE hQV
  let sQ : E.presheaf.obj (op Q) := E.presheaf.map iQV.op s
  let R := (openSheafRestriction AddCommGrpCat.{v} U).obj E
  let eImage := openSheafRestrictionImageIso AddCommGrpCat.{v} U E
  let t : R.presheaf.obj (op W) := eImage.inv.app (op W) sQ
  let K := (CategoryTheory.constantSheaf
    (Opens.grothendieckTopology (openSubspace U))
    AddCommGrpCat.{v}).obj A
  let ep : R.presheaf ≅ K.obj :=
    (TopCat.Sheaf.forget AddCommGrpCat.{v} (openSubspace U)).mapIso e
  let c : K.obj.obj (op W) := ep.hom.app (op W) t
  have ht : eImage.hom.app (op W) t = sQ := by
    have h := ConcreteCategory.congr_hom
      (eImage.inv_hom_id_app (op W)) sQ
    change eImage.hom.app (op W) (eImage.inv.app (op W) sQ) = sQ at h
    simpa only [t] using h
  have hsupport_t : IsClopen (additiveSectionSupport R W t) := by
    have hc := constantAddCommGrpSheaf_support_isClopen A W c
    have heq := additiveSectionSupport_map_iso R K ep W t
    rw [heq] at hc
    exact hc
  have hpoint : ∀ y : W,
      y ∈ additiveSectionSupport R W t ↔
        (⟨(openInclusion U) y.1, hWmemV y⟩ : V) ∈
          additiveSectionSupport E V s := by
    intro y
    let rStalk : R.presheaf.stalk y.1 ≅
        E.presheaf.stalk ((openInclusion U) y.1) :=
      (openSheafRestrictionStalkIso AddCommGrpCat.{v} U y.1).app E
    have hrinj : Function.Injective (ConcreteCategory.hom rStalk.hom) := by
      intro a b hab
      have hab' := congrArg (ConcreteCategory.hom rStalk.inv) hab
      have hleft : ConcreteCategory.hom rStalk.inv
          (ConcreteCategory.hom rStalk.hom a) = a := by
        change ConcreteCategory.hom (rStalk.hom ≫ rStalk.inv) a = a
        rw [rStalk.hom_inv_id]
        rfl
      have hright : ConcreteCategory.hom rStalk.inv
          (ConcreteCategory.hom rStalk.hom b) = b := by
        change ConcreteCategory.hom (rStalk.hom ≫ rStalk.inv) b = b
        rw [rStalk.hom_inv_id]
        rfl
      exact hleft.symm.trans (hab'.trans hright)
    have hgImage := ConcreteCategory.congr_hom
      (openSheafRestrictionImageIso_germ AddCommGrpCat.{v} U E W y.1 y.2) t
    have hgImage' :
        ConcreteCategory.hom rStalk.hom
            (ConcreteCategory.hom (R.presheaf.germ W y.1 y.2) t) =
          ConcreteCategory.hom (E.presheaf.germ Q ((openInclusion U) y.1)
            ⟨y.1, y.2, rfl⟩) sQ := by
      change ConcreteCategory.hom rStalk.hom
          (ConcreteCategory.hom (R.presheaf.germ W y.1 y.2) t) =
        ConcreteCategory.hom (E.presheaf.germ Q ((openInclusion U) y.1)
          ⟨y.1, y.2, rfl⟩) (eImage.hom.app (op W) t) at hgImage
      rw [ht] at hgImage
      exact hgImage
    have hgRes := ConcreteCategory.congr_hom
      (E.presheaf.germ_res iQV ((openInclusion U) y.1)
        ⟨y.1, y.2, rfl⟩) s
    have hg :
        ConcreteCategory.hom rStalk.hom
            (ConcreteCategory.hom (R.presheaf.germ W y.1 y.2) t) =
          ConcreteCategory.hom (E.presheaf.germ V
            ((openInclusion U) y.1) (hWmemV y)) s := by
      change ConcreteCategory.hom (E.presheaf.germ Q ((openInclusion U) y.1)
          ⟨y.1, y.2, rfl⟩) (E.presheaf.map iQV.op s) =
        ConcreteCategory.hom (E.presheaf.germ V
          ((openInclusion U) y.1) (hWmemV y)) s at hgRes
      exact hgImage'.trans (by simpa only [sQ] using hgRes)
    simp only [additiveSectionSupport, Set.mem_ofPred_eq]
    apply not_congr
    constructor
    · intro hz
      rw [← hg, hz, map_zero]
    · intro hz
      apply hrinj
      rw [hg, hz, map_zero]
  let ST : Set W := additiveSectionSupport R W t
  let OU : Set U := Subtype.val '' ST
  have hOU : IsOpen OU := by
    exact W.isOpenEmbedding.isOpenMap ST hsupport_t.2
  let OX : Set X := Subtype.val '' OU
  have hOX : IsOpen OX := U.isOpenEmbedding.isOpenMap OU hOU
  let OV : Set V := (Subtype.val : V → X) ⁻¹' OX
  have hOV : IsOpen OV := hOX.preimage continuous_subtype_val
  have hxW : (⟨x.1, hxU⟩ : U) ∈ W := x.2
  let xW : W := ⟨⟨x.1, hxU⟩, hxW⟩
  have hxST : xW ∈ ST := by
    apply (hpoint xW).2
    have hxeq : (⟨(openInclusion U) xW.1, hWmemV xW⟩ : V) = x := by
      apply Subtype.ext
      rfl
    simpa only [hxeq] using hx
  have hxOV : x ∈ OV := by
    exact ⟨⟨x.1, hxU⟩, ⟨xW, hxST, rfl⟩, rfl⟩
  refine Filter.mem_of_superset (hOV.mem_nhds hxOV) ?_
  intro y hy
  rcases hy with ⟨yu, ⟨yw, hyw, hyw_eq⟩, hyu_eq⟩
  have hy' := (hpoint yw).1 hyw
  have heq : (⟨(openInclusion U) yw.1, hWmemV yw⟩ : V) = y := by
    apply Subtype.ext
    exact (congrArg Subtype.val hyw_eq).trans hyu_eq
  simpa only [heq] using hy'

/-- Sections of a sheaf restricted to an open subspace are the ambient
sections over the corresponding image open. -/
theorem openSheafRestriction_obj_iso (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C X)
    (V : Opens (openSubspace U)) :
    Nonempty ((((openSheafRestriction C U).obj F).presheaf).obj (op V) ≅
      F.presheaf.obj (op ⟨(openInclusion U) '' V,
        (U.isOpenEmbedding.isOpenMap V V.2)⟩)) := by
  rcases openSheafRestriction_formula C U F with ⟨e⟩
  exact ⟨e.app (op V) ≪≫ openPresheafRestriction_obj_iso C U F.presheaf V⟩

/-- A morphism from a constant additive sheaf to a restricted sheaf has
zero stalk map when the corresponding ambient image open has no sections. -/
theorem constantAddCommGrpSheaf_stalk_map_eq_zero_of_restriction_image_isZero
    {X : TopCat.{v}} (U : Opens X) (G : TopCat.Sheaf AddCommGrpCat.{v} X)
    (A : AddCommGrpCat.{v})
    (f : (CategoryTheory.constantSheaf
      (Opens.grothendieckTopology (openSubspace U))
      AddCommGrpCat.{v}).obj A ⟶
        (openSheafRestriction AddCommGrpCat.{v} U).obj G)
    (V : Opens (openSubspace U)) (x : U) (hx : x ∈ V)
    (hV : IsZero (G.presheaf.obj
      (op ⟨(openInclusion U) '' V,
        U.isOpenEmbedding.isOpenMap V V.2⟩))) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map f.hom = 0 := by
  rcases openSheafRestriction_obj_iso AddCommGrpCat.{v} U G V with ⟨eV⟩
  have hRV : IsZero (((openSheafRestriction AddCommGrpCat.{v} U).obj G).presheaf.obj
      (op V)) := (eV.isZero_iff).2 hV
  exact constantAddCommGrpSheaf_stalk_map_eq_zero_of_isZero A
    ((openSheafRestriction AddCommGrpCat.{v} U).obj G) f V x hx hRV

/-- Restriction preserves the stalk at a point of the open subspace. -/
theorem openSheafRestriction_stalk_iso (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C X)
    (u : openSubspace U) :
    Nonempty (((openSheafRestriction C U).obj F).presheaf.stalk u ≅
      F.presheaf.stalk ((openInclusion U) u)) := by
  rcases openSheafRestriction_formula C U F with ⟨e⟩
  exact ⟨(TopCat.Presheaf.stalkFunctor C u).mapIso e ≪≫
    (TopCat.Presheaf.stalkPullbackIso C (openInclusion U) F.presheaf u).symm⟩

/-- An epimorphism of additive sheaves is epimorphic on every stalk. -/
theorem openAbelianSheaf_stalk_map_epi {X : TopCat.{v}}
    {F G : TopCat.Sheaf AddCommGrpCat.{v} X} (f : F ⟶ G) [Epi f] (x : X) :
    Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.hom) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks f.hom).mp
  exact (TopCat.Sheaf.isLocallySurjective_iff_epi f).mpr inferInstance

/-- An epimorphism of additive sheaves whose map on a stalk is zero has a
zero target stalk. -/
theorem openAbelianSheaf_target_stalk_isZero_of_epi_of_map_eq_zero
    {X : TopCat.{v}} {F G : TopCat.Sheaf AddCommGrpCat.{v} X}
    (f : F ⟶ G) [Epi f] (x : X)
    (hzero : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map f.hom = 0) :
    IsZero (G.presheaf.stalk x) := by
  let m := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map f.hom
  let : Epi m := openAbelianSheaf_stalk_map_epi f x
  have hsurj : Function.Surjective (ConcreteCategory.hom m) := by
    rw [← AddCommGrpCat.epi_iff_surjective]
    infer_instance
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  constructor
  intro a b
  obtain ⟨p, hp⟩ := hsurj a
  obtain ⟨q, hq⟩ := hsurj b
  have hm : m = 0 := hzero
  rw [hm] at hp hq
  change 0 = a at hp
  change 0 = b at hq
  exact hp.symm.trans hq

/-- An additive sheaf morphism is an epimorphism when all of its stalk maps
are epimorphisms. -/
theorem openAbelianSheaf_epi_of_stalk_map_epi {X : TopCat.{v}}
    {F G : TopCat.Sheaf AddCommGrpCat.{v} X} (f : F ⟶ G)
    (h : ∀ x : X,
      Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.hom)) :
    Epi f := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi f).mp
  apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks f.hom).mpr
  intro x
  rw [← AddCommGrpCat.epi_iff_surjective]
  exact h x

/-- Direct image is computed by inverse images of opens. -/
@[simp] theorem openPresheafDirectImage_obj (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) (V : Opens X) :
    ((openPresheafDirectImage C U).obj F).obj (op V) =
      F.obj (op ((Opens.map (openInclusion U)).obj V)) := rfl

/-- Restriction followed by direct image is the identity on presheaves of an open subspace. -/
theorem openPresheafRestriction_directImage_iso (C : Type u) [Category.{v} C]
    [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) :
    Nonempty ((openPresheafRestriction C U).obj
      ((openPresheafDirectImage C U).obj F) ≅ F) := by
  let f := openInclusion U
  refine ⟨?_⟩
  let hf := U.isOpenEmbedding
  have hfun : hf.functor ⋙ Opens.map f = 𝟭 _ := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro V
      exact TopologicalSpace.Opens.map_functor_eq' f hf V
    · subsingleton
  let e : hf.functor.op ⋙ (TopCat.Presheaf.pushforward C f).obj F ≅ F :=
    eqToIso (by
      dsimp [TopCat.Presheaf.pushforward]
      change ((hf.functor ⋙ Opens.map f).op ⋙ F) = F
      rw [hfun]
      rfl)
  exact (hf.isOpenMap.pullbackObjIso ((TopCat.Presheaf.pushforward C f).obj F)) ≪≫ e

/-- Restriction followed by direct image is the identity on sheaves of an open subspace. -/
theorem openSheafRestriction_directImage_iso {C : Type u} [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) (F : TopCat.Sheaf C (openSubspace U)) :
    Nonempty ((openSheafRestriction C U).obj
      ((openSheafDirectImage C U).obj F) ≅ F) := by
  let f := openInclusion U
  let hf := U.isOpenEmbedding
  have hfun : hf.functor ⋙ Opens.map f = 𝟭 _ := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro V
      exact TopologicalSpace.Opens.map_functor_eq' f hf V
    · subsingleton
  have hobj :
      (openSheafRestriction C U).obj ((openSheafDirectImage C U).obj F) = F := by
    apply ObjectProperty.FullSubcategory.ext
    dsimp [openSheafRestriction, openSheafDirectImage, TopCat.Sheaf.pushforward,
      Functor.sheafPushforwardContinuous]
    change ((hf.functor ⋙ Opens.map f).op ⋙ F.presheaf) = F.presheaf
    rw [hfun]
    rfl
  exact ⟨eqToIso hobj⟩

/-- Direct image along an open inclusion is fully faithful. -/
theorem openSheafDirectImage_fullFaithful (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X) :
    Nonempty (openSheafDirectImage C U).FullyFaithful := by
  let f := openInclusion U
  let hf := U.isOpenEmbedding
  have hfun : hf.functor ⋙ Opens.map f = 𝟭 _ := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro V
      exact TopologicalSpace.Opens.map_functor_eq' f hf V
    · subsingleton
  have hcont : hf.functor.IsContinuous (Opens.grothendieckTopology (openSubspace U))
      (Opens.grothendieckTopology X) := hf.functor_isContinuous
  let adj₀ := hf.isOpenMap.adjunction
  let adj : openSheafRestriction C U ⊣ openSheafDirectImage C U :=
    adj₀.sheafPushforwardContinuous
    (Opens.grothendieckTopology (openSubspace U))
    (Opens.grothendieckTopology X)
  have hIso : IsIso adj.counit := by
    have hF : ∀ F, IsIso (adj.counit.app F) := by
      intro F
      apply (ObjectProperty.isIso_hom_iff
        (adj.counit.app F)).mp
      change IsIso ((adj₀.op.whiskerLeft _).counit.app F.presheaf)
      have hV : ∀ V, IsIso (((adj₀.op.whiskerLeft _).counit.app F.presheaf).app V) := by
        intro V
        dsimp [CategoryTheory.Adjunction.whiskerLeft]
        rw [show adj₀.op.counit.app V =
          eqToHom (by
            change op ((hf.functor ⋙ Opens.map f).obj V.unop) = V
            rw [hfun]
            rfl) from Subsingleton.elim _ _]
        infer_instance
      exact NatIso.isIso_of_isIso_app _
    exact NatIso.isIso_of_isIso_app _
  exact ⟨adj.fullyFaithfulROfIsIsoCounit⟩

/-! ## Extension by the initial object -/

/-- Extension by the initial object at the presheaf level. -/
noncomputable def openPresheafExtensionByInitial (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C (openSubspace U) ⥤ TopCat.Presheaf C X := by
  classical
  let j := Opens.map (openInclusion U)
  exact {
    obj := fun F => {
      obj := fun V => if hV : V.unop ≤ U then F.obj (j.op.obj V) else ⊥_ C
      map := by
        intro V W i
        by_cases hV : V.unop ≤ U
        · have hW : W.unop ≤ U := by
            exact (show W.unop ≤ V.unop from leOfHom i.unop).trans hV
          exact eqToHom (by simp [hV]) ≫ F.map (j.op.map i) ≫
            eqToHom (by simp [hW])
        · exact eqToHom (by simp [hV]) ≫ initial.to _
      map_id := by
        intro V
        by_cases hV : V.unop ≤ U
        · simp [hV]
        · let e : (if V.unop ≤ U then F.obj (j.op.obj V) else ⊥_ C) ≅ (⊥_ C) :=
            eqToIso (if_neg hV)
          rw [← cancel_epi e.inv]
          simp only [dif_neg hV]
          exact initial.hom_ext _ _
      map_comp := by
        intro V W T i k
        by_cases hV : V.unop ≤ U
        · have hW : W.unop ≤ U := by
            exact (show W.unop ≤ V.unop from leOfHom i.unop).trans hV
          have hT : T.unop ≤ U := by
            exact (show T.unop ≤ W.unop from leOfHom k.unop).trans hW
          simp [hV, hW, hT]
        · let e : (if V.unop ≤ U then F.obj (j.op.obj V) else ⊥_ C) ≅ (⊥_ C) :=
            eqToIso (if_neg hV)
          rw [← cancel_epi e.inv]
          simp only [dif_neg hV]
          exact initial.hom_ext _ _
    }
    map := fun {F G} φ => {
      app := fun V => if hV : V.unop ≤ U then
          eqToHom (by simp [hV]) ≫ φ.app (j.op.obj V) ≫
            eqToHom (by simp [hV])
        else eqToHom (by simp [hV]) ≫ initial.to _
      naturality := by
        intro V W i
        by_cases hV : V.unop ≤ U
        · have hW : W.unop ≤ U := by
            exact (show W.unop ≤ V.unop from leOfHom i.unop).trans hV
          simp [hV, hW]
        · let e : (if V.unop ≤ U then F.obj (j.op.obj V) else ⊥_ C) ≅ (⊥_ C) :=
            eqToIso (if_neg hV)
          rw [← cancel_epi e.inv]
          simp only [dif_neg hV]
          exact initial.hom_ext _ _
      }
    map_id := by
      intro F
      apply NatTrans.ext'
      funext V
      by_cases hV : V.unop ≤ U
      · simp [hV]
        change eqToHom _ ≫ 𝟙 _ ≫ eqToHom _ = 𝟙 _
        simp
      · let e : (if V.unop ≤ U then F.obj (j.op.obj V) else ⊥_ C) ≅
            (⊥_ C) := eqToIso (if_neg hV)
        rw [← cancel_epi e.inv]
        simp only [dif_neg hV]
        exact initial.hom_ext _ _
    map_comp := by
      intro F G H φ ψ
      apply NatTrans.ext'
      funext V
      by_cases hV : V.unop ≤ U
      · simp [hV]
      · let e : (if V.unop ≤ U then F.obj (j.op.obj V) else ⊥_ C) ≅
            (⊥_ C) := eqToIso (if_neg hV)
        rw [← cancel_epi e.inv]
        simp only [dif_neg hV]
        exact initial.hom_ext _ _
  }

/-- On opens contained in `U`, extension by the initial object has the original
sections. -/
@[simp] theorem openPresheafExtensionByInitial_obj_of_le (C : Type u)
    [Category.{v} C] [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) (V : Opens X) (hV : V ≤ U) :
    ((openPresheafExtensionByInitial C U).obj F).obj (op V) =
      F.obj (op ((Opens.map (openInclusion U)).obj V)) := by
  simp [openPresheafExtensionByInitial, hV]

/-- On opens not contained in `U`, extension by the initial object has the
initial section object. -/
@[simp] theorem openPresheafExtensionByInitial_obj_of_not_le (C : Type u)
    [Category.{v} C] [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) (V : Opens X) (hV : ¬ V ≤ U) :
    ((openPresheafExtensionByInitial C U).obj F).obj (op V) = (⊥_ C) := by
  simp [openPresheafExtensionByInitial, hV]

/-- Extension by the empty set for set-valued presheaves. -/
noncomputable abbrev openPresheafExtensionByEmpty {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf (Type v) (openSubspace U) ⥤ TopCat.Presheaf (Type v) X :=
  openPresheafExtensionByInitial (Type v) U

/-! The same initial-object construction for abelian and algebraic
presheaves. -/

noncomputable abbrev openAbelianPresheafExtensionByZero {X : TopCat.{v}}
    (U : Opens X) :
    AbelianPresheaf (openSubspace U) ⥤ AbelianPresheaf X :=
  openPresheafExtensionByInitial AddCommGrpCat U

noncomputable abbrev openAlgebraicPresheafExtensionByInitial
    (C : Type u) [Category.{v} C] [HasInitial C]
    {X : TopCat.{v}} (U : Opens X) :
    TopCat.Presheaf C (openSubspace U) ⥤ TopCat.Presheaf C X :=
  openPresheafExtensionByInitial C U

/-- Sheafification of extension by the initial object. -/
noncomputable def openSheafExtensionByInitial (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    TopCat.Sheaf C (openSubspace U) ⥤ TopCat.Sheaf C X := by
  exact (TopCat.Sheaf.forget C (openSubspace U) ⋙
    openPresheafExtensionByInitial C U ⋙
    CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) C)

/-- Extension by the empty set for sheaves of sets. -/
noncomputable abbrev openSetSheafExtensionByEmpty {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    TopCat.Sheaf (Type v) (openSubspace U) ⥤ TopCat.Sheaf (Type v) X :=
  openSheafExtensionByInitial (Type v) U

noncomputable abbrev openAbelianSheafExtensionByZero {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :
    Ab (openSubspace U) ⥤ Ab X :=
  openSheafExtensionByInitial AddCommGrpCat U

private noncomputable def openPresheafRestrictionAux (C : Type u) [Category.{v} C]
    {X : TopCat.{v}} (U : Opens X)
    (hf : IsOpenEmbedding ⇑(ConcreteCategory.hom U.inclusion')) :
    TopCat.Presheaf C X ⥤ TopCat.Presheaf C (openSubspace U) :=
  (Functor.whiskeringLeft (Opens (openSubspace U))ᵒᵖ
    (Opens X)ᵒᵖ C).obj hf.functor.op

private noncomputable def openPresheafExtensionToHom (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    (hf : IsOpenEmbedding ⇑(ConcreteCategory.hom U.inclusion'))
    (F : TopCat.Presheaf C (openSubspace U)) (G : TopCat.Presheaf C X)
    (φ : (openPresheafExtensionByInitial C U).obj F ⟶ G) :
    F ⟶ hf.functor.op ⋙ G := by
  classical
  let f := openInclusion U
  let j := Opens.map f
  have hfun : hf.functor ⋙ j = 𝟭 _ := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro V
      exact TopologicalSpace.Opens.map_functor_eq' f hf V
    · subsingleton
  have hsub : ∀ V : Opens (openSubspace U), hf.functor.obj V ≤ U := by
    intro V
    change (f '' V) ≤ U
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  refine { app := ?_, naturality := ?_ }
  · intro V
    have hobj : j.obj (hf.functor.obj V.unop) = V.unop := by
      simpa [j] using congrArg (fun K => K.obj V.unop) hfun
    have hEleft :
        ((openPresheafExtensionByInitial C U).obj F).obj
            (hf.functor.op.obj V) =
          F.obj (j.op.obj (hf.functor.op.obj V)) := by
      simpa [j, f] using
        (openPresheafExtensionByInitial_obj_of_le C U F
          (hf.functor.obj V.unop) (hsub V.unop))
    exact F.map (eqToHom hobj).op ≫ eqToHom hEleft.symm ≫
      φ.app (hf.functor.op.obj V)
  · intro V W i
    have hobjV : (Opens.map f).obj (hf.functor.obj V.unop) = V.unop := by
      simpa [j] using congrArg (fun K => K.obj V.unop) hfun
    have hobjW : (Opens.map f).obj (hf.functor.obj W.unop) = W.unop := by
      simpa [j] using congrArg (fun K => K.obj W.unop) hfun
    have hmap :
        (Opens.map f).map (hf.functor.map i.unop) =
          eqToHom hobjW ≫ i.unop ≫ eqToHom hobjV.symm := by
      simpa [j] using (Functor.congr_hom hfun i.unop)
    have hEleft :
        ((openPresheafExtensionByInitial C U).obj F).obj
            (hf.functor.op.obj V) =
          F.obj (j.op.obj (hf.functor.op.obj V)) := by
      simpa [j, f] using
        (openPresheafExtensionByInitial_obj_of_le C U F
          (hf.functor.obj V.unop) (hsub V.unop))
    have hEright :
        F.obj (j.op.obj (hf.functor.op.obj W)) =
          ((openPresheafExtensionByInitial C U).obj F).obj
            (hf.functor.op.obj W) := by
      simpa [j, f] using
        (openPresheafExtensionByInitial_obj_of_le C U F
          (hf.functor.obj W.unop) (hsub W.unop)).symm
    have hE :
        ((openPresheafExtensionByInitial C U).obj F).map
            (hf.functor.op.map i) =
          eqToHom hEleft ≫
            F.map (j.op.map (hf.functor.op.map i)) ≫
          eqToHom hEright := by
      change (if h : hf.functor.obj V.unop ≤ U then
        eqToHom _ ≫ F.map (j.op.map (hf.functor.op.map i)) ≫ eqToHom _
      else _) = _
      rw [dif_pos (hsub V.unop)]
      rfl
    simp only [Category.assoc]
    rw [show (hf.functor.op ⋙ G).map i = G.map (hf.functor.op.map i) from rfl]
    rw [← φ.naturality]
    conv_rhs =>
      rw [hE]
    simp [hmap, j, f, Functor.map_comp, eqToHom_map, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

private noncomputable def openPresheafExtensionFromHom (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    (hf : IsOpenEmbedding ⇑(ConcreteCategory.hom U.inclusion'))
    (F : TopCat.Presheaf C (openSubspace U)) (G : TopCat.Presheaf C X)
    (ψ : F ⟶ hf.functor.op ⋙ G) :
    (openPresheafExtensionByInitial C U).obj F ⟶ G := by
  classical
  let f := openInclusion U
  let j := Opens.map f
  have hfun : hf.functor ⋙ j = 𝟭 _ := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro V
      exact TopologicalSpace.Opens.map_functor_eq' f hf V
    · subsingleton
  have himage : ∀ W : Opens X, W ≤ U →
      hf.functor.obj (j.obj W) = W := by
    intro W hW
    apply Opens.ext
    change f '' (j.obj W) = W
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hW hx⟩, hx, rfl⟩
  refine { app := ?_, naturality := ?_ }
  · intro W
    by_cases hW : W.unop ≤ U
    · have himageW := himage W.unop hW
      have hG' :
          G.obj (op (hf.functor.obj (j.obj W.unop))) = G.obj W := by
        exact congrArg (fun K => G.obj (op K)) himageW
      exact eqToHom (openPresheafExtensionByInitial_obj_of_le C U F W.unop hW) ≫
        ψ.app (op (j.obj W.unop)) ≫
        eqToHom hG'
    · change (if h : W.unop ≤ U then
        F.obj (j.op.obj W) else ⊥_ C) ⟶ G.obj W
      rw [dif_neg hW]
      exact initial.to _
  · intro V W i
    by_cases hV : V.unop ≤ U
    · have hW : W.unop ≤ U := by
        exact (show W.unop ≤ V.unop from leOfHom i.unop).trans hV
      have himageV := himage V.unop hV
      have himageW := himage W.unop hW
      have hG' :
          G.obj (op (hf.functor.obj (j.obj W.unop))) = G.obj W := by
        exact congrArg (fun K => G.obj (op K)) himageW
      have hmap :
          hf.functor.map ((Opens.map (openInclusion U)).map i.unop) =
            eqToHom himageW ≫ i.unop ≫ eqToHom himageV.symm := by
        apply Subsingleton.elim
      have hEleft :
          ((openPresheafExtensionByInitial C U).obj F).obj V =
            F.obj ((Opens.map (openInclusion U)).op.obj V) := by
        exact openPresheafExtensionByInitial_obj_of_le C U F V.unop hV
      have hEright :
          F.obj ((Opens.map (openInclusion U)).op.obj W) =
            ((openPresheafExtensionByInitial C U).obj F).obj W := by
        exact (openPresheafExtensionByInitial_obj_of_le C U F W.unop hW).symm
      have hcancelW :
          eqToHom hEright ≫
              eqToHom (openPresheafExtensionByInitial_obj_of_le C U F W.unop hW) = 𝟙 _ := by
        simp
      have hcancelW' :
          eqToHom hEright ≫
              (eqToHom (openPresheafExtensionByInitial_obj_of_le C U F W.unop hW) ≫
                (ψ.app (op (j.obj W.unop)) ≫ eqToHom hG')) =
            ψ.app (op (j.obj W.unop)) ≫ eqToHom hG' := by
        rw [← Category.assoc, hcancelW, Category.id_comp]
      have hE :
          ((openPresheafExtensionByInitial C U).obj F).map i =
            eqToHom hEleft ≫
              F.map ((Opens.map (openInclusion U)).op.map i) ≫
            eqToHom hEright := by
        change (if h : V.unop ≤ U then
          eqToHom _ ≫
              F.map ((Opens.map (openInclusion U)).op.map i) ≫ eqToHom _ else _) = _
        simp only [dif_pos hV]
        rfl
      dsimp [openPresheafRestrictionAux] at ψ ⊢
      simp only [dif_pos hV, dif_pos hW, Category.assoc]
      rw [hE]
      simp only [Category.assoc]
      rw [hcancelW']
      dsimp [j] at ⊢
      rw [← Category.assoc
        (F.map (((Opens.map (openInclusion U)).map i.unop).op))
        (ψ.app (op ((Opens.map (openInclusion U)).obj W.unop))) (eqToHom hG')]
      rw [ψ.naturality (((Opens.map (openInclusion U)).map i.unop).op)]
      change eqToHom hEleft ≫
          (ψ.app (op ((Opens.map (openInclusion U)).obj V.unop)) ≫
            G.map (hf.functor.map ((Opens.map (openInclusion U)).map i.unop)).op) ≫
          eqToHom hG' = _
      rw [hmap]
      simp [j, f, Category.assoc, Functor.map_comp, eqToHom_map, Category.comp_id]
    · let e :
          ((openPresheafExtensionByInitial C U).obj F).obj V ≅
            (⊥_ C) := eqToIso
          (openPresheafExtensionByInitial_obj_of_not_le C U F V.unop hV)
      rw [← cancel_epi e.inv]
      simp only [dif_neg hV]
      exact initial.hom_ext _ _

private noncomputable def openPresheafExtensionHomEquiv (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    (hf : IsOpenEmbedding ⇑(ConcreteCategory.hom U.inclusion'))
    (F : TopCat.Presheaf C (openSubspace U)) (G : TopCat.Presheaf C X) :
    ((openPresheafExtensionByInitial C U).obj F ⟶ G) ≃
      (F ⟶ hf.functor.op ⋙ G) := by sorry
/- Prior attempt (does not compile; retained for reference):
  classical
  exact {
    toFun := openPresheafExtensionToHom C U hf F G
    invFun := openPresheafExtensionFromHom C U hf F G
    left_inv := by
      intro φ
      apply NatTrans.ext'
      funext V
      dsimp [openPresheafExtensionToHom,
        openPresheafExtensionFromHom]
      by_cases hV : V.unop ≤ U
      · let f := openInclusion U
        let j := Opens.map f
        have hfun : hf.functor ⋙ j = 𝟭 _ := by
          refine CategoryTheory.Functor.ext ?_ ?_
          · intro V
            exact TopologicalSpace.Opens.map_functor_eq' f hf V
          · subsingleton
        have hsub : ∀ V : Opens (openSubspace U), hf.functor.obj V ≤ U := by
          intro V
          change (f '' V) ≤ U
          rintro x ⟨y, hy, rfl⟩
          exact y.property
        have himage : ∀ W : Opens X, W ≤ U →
            hf.functor.obj (j.obj W) = W := by
          intro W hW
          apply Opens.ext
          change f '' (j.obj W) = W
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact hy
          · intro hx
            exact ⟨⟨x, hW hx⟩, hx, rfl⟩
        have hobjj :
            j.obj (hf.functor.obj (j.obj V.unop)) = j.obj V.unop := by
          simpa [j] using congrArg (fun K => K.obj (j.obj V.unop)) hfun
        have hV' : hf.functor.op.obj (op (j.obj V.unop)) = V := by
          exact congrArg op (himage (V.unop) hV)
        have hEleft :
            ((openPresheafExtensionByInitial C U).obj F).obj V =
              F.obj (j.op.obj V) := by
          simpa [j, f] using
            (openPresheafExtensionByInitial_obj_of_le C U F V.unop hV)
        have hEright :
            F.obj (j.op.obj (hf.functor.op.obj (op (j.obj V.unop)))) =
              ((openPresheafExtensionByInitial C U).obj F).obj
                (hf.functor.op.obj (op (j.obj V.unop))) := by
          simpa [j, f] using
            (openPresheafExtensionByInitial_obj_of_le C U F
              (hf.functor.obj (j.obj V.unop))
              (hsub (j.obj V.unop))).symm
        have hE :
            ((openPresheafExtensionByInitial C U).obj F).map
                (eqToHom hV'.symm) =
              (eqToHom hEleft ≫ F.map (eqToHom hobjj).op) ≫
                eqToHom hEright := by
          change (if h : V.unop ≤ U then
            eqToHom _ ≫ F.map (j.op.map (eqToHom hV'.symm)) ≫ eqToHom _
          else _) = _
          simp only [openPresheafExtensionByInitial, dif_pos hV,
            dif_pos (hsub (j.obj V.unop))]
          have hmap :
              j.op.map (eqToHom hV'.symm) = (eqToHom hobjj).op := by
            apply Subsingleton.elim
          rw [hmap]
          simp [Category.assoc]
        simp only [dif_pos hV]
        have hnat := φ.naturality (eqToHom hV')
        simp only [Category.assoc]
        rw [← Category.assoc, ← Category.assoc]
        rw [← hE]
        simpa [j, eqToHom_map] using hnat
      · let e :
            ((openPresheafExtensionByInitial C U).obj F).obj V ≅
              (⊥_ C) := eqToIso
            (openPresheafExtensionByInitial_obj_of_not_le C U F V.unop hV)
        rw [← cancel_epi e.inv]
        simp only [dif_neg hV]
        exact initial.hom_ext _ _
    right_inv := by
      intro ψ
      apply NatTrans.ext'
      funext V
      dsimp [openPresheafExtensionToHom,
        openPresheafExtensionFromHom]
      let f := openInclusion U
      let j := Opens.map f
      have hfun : hf.functor ⋙ j = 𝟭 _ := by
        refine CategoryTheory.Functor.ext ?_ ?_
        · intro V
          exact TopologicalSpace.Opens.map_functor_eq' f hf V
        · subsingleton
      have hsub : ∀ V : Opens (openSubspace U), hf.functor.obj V ≤ U := by
        intro V
        change (f '' V) ≤ U
        rintro x ⟨y, hy, rfl⟩
        exact y.property
      have himage : ∀ W : Opens X, W ≤ U →
          hf.functor.obj (j.obj W) = W := by
        intro W hW
        apply Opens.ext
        change f '' (j.obj W) = W
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hW hx⟩, hx, rfl⟩
      have hobj : j.obj (hf.functor.obj V.unop) = V.unop := by
        simpa [j] using congrArg (fun K => K.obj V.unop) hfun
      have hobjj :
          j.obj (hf.functor.obj (j.obj (hf.functor.obj V.unop))) =
            j.obj (hf.functor.obj V.unop) := by
        simpa [j] using congrArg
          (fun K => K.obj (j.obj (hf.functor.obj V.unop))) hfun
      have hq : V = op (j.obj (hf.functor.obj V.unop)) := by
        exact (congrArg op hobj).symm
      have hnat := ψ.naturality (eqToHom hq)
      have hG' :
          G.obj (op (hf.functor.obj (j.obj (hf.functor.obj V.unop)))) =
            G.obj (op (hf.functor.obj V.unop)) := by
        exact congrArg (fun K => G.obj (op K))
          (himage (hf.functor.obj V.unop) (hsub V.unop))
      simp only [dif_pos (hsub V.unop), eqToHom_map, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
      dsimp [j] at hnat
      have htarget :
          F.map (eqToHom hq) ≫
              ψ.app (op (j.obj (hf.functor.obj V.unop))) ≫ eqToHom hG' =
            ψ.app V := by
        rw [← Category.assoc, hnat]
        simp [eqToHom_map, hq, hG']
      simpa [j] using htarget }
-/
/- The presheaf extension/restriction adjunction. -/
theorem exists_openPresheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X) :
    Nonempty (openPresheafExtensionByInitial C U ⊣ openPresheafRestriction C U) := by sorry
/-
  classical
  let hf := U.isOpenEmbedding
  let R₀ := (Functor.whiskeringLeft (Opens (openSubspace U))ᵒᵖ
    (Opens X)ᵒᵖ C).obj hf.functor.op
  let adj₀ : openPresheafExtensionByInitial C U ⊣ R₀ := by
    refine Adjunction.mkOfHomEquiv {
      homEquiv := fun F G => openPresheafExtensionHomEquiv C U hf F G
      homEquiv_naturality_left_symm := by
        intros
        simp
      homEquiv_naturality_right := by
        intros
        simp }
  exact ⟨adj₀.ofNatIsoRight hf.isOpenMap.pullbackIso.symm⟩

-/
/-- The presheaf extension/restriction adjunction. -/
noncomputable def openPresheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X) :
    openPresheafExtensionByInitial C U ⊣ openPresheafRestriction C U := by
  exact Classical.choice (exists_openPresheafExtensionAdjunction C U)

noncomputable abbrev openAbelianPresheafExtensionAdjunction
    {X : TopCat.{v}} (U : Opens X) :
    openAbelianPresheafExtensionByZero U ⊣ openPresheafRestriction AddCommGrpCat U :=
  openPresheafExtensionAdjunction AddCommGrpCat U

/-- The sheaf extension/restriction adjunction. -/
theorem exists_openSheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    Nonempty (openSheafExtensionByInitial C U ⊣ openSheafRestriction C U) := by sorry
/-
  classical
  let hf := U.isOpenEmbedding
  let R₀ := (Functor.whiskeringLeft (Opens (openSubspace U))ᵒᵖ
    (Opens X)ᵒᵖ C).obj hf.functor.op
  let adj₀ : openPresheafExtensionByInitial C U ⊣ R₀ := by
    refine Adjunction.mkOfHomEquiv {
      homEquiv := fun F G => openPresheafExtensionHomEquiv C U hf F G
      homEquiv_naturality_left_symm := by
        intros
        simp
      homEquiv_naturality_right := by
        intros
        simp }
  let adj₁ := adj₀.comp
    (sheafificationAdjunction (Opens.grothendieckTopology X) C)
  let adj₂ := adj₁.restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (openSubspace U)) C)
    (Functor.FullyFaithful.id _)
    (L := openSheafExtensionByInitial C U) (R := openSheafRestriction C U)
    (Iso.refl _) (Iso.refl _)
  exact ⟨adj₂⟩

-/
/-- The sheaf extension/restriction adjunction. -/
noncomputable def openSheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    openSheafExtensionByInitial C U ⊣ openSheafRestriction C U := by
  exact Classical.choice (exists_openSheafExtensionAdjunction C U)

/-- Restricting the presheaf extension by the initial object recovers the
original presheaf on the open subspace. -/
theorem openPresheafExtension_restrict_iso (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    (F : TopCat.Presheaf C (openSubspace U)) :
    Nonempty ((openPresheafRestriction C U).obj
      ((openPresheafExtensionByInitial C U).obj F) ≅ F) := by
  sorry

/-- Restricting the sheaf extension by the initial object recovers the
original sheaf on the open subspace. -/
theorem openAlgebraicSheafExtension_restrict_iso (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : TopCat.Sheaf C (openSubspace U)) :
    Nonempty ((openSheafRestriction C U).obj
      ((openSheafExtensionByInitial C U).obj F) ≅ F) := by
  sorry

/-- The set-valued Hom correspondence for extension by the empty set. -/
noncomputable abbrev openSetSheafExtensionHomEquiv {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (F : TopCat.Sheaf (Type v) (openSubspace U)) (G : TopCat.Sheaf (Type v) X) :
    ((openSetSheafExtensionByEmpty U).obj F ⟶ G) ≃
      (F ⟶ (openSheafRestriction (Type v) U).obj G) :=
  (openSheafExtensionAdjunction (Type v) U).homEquiv F G

/-- Outside the open, extension by the empty set has empty stalks. -/
theorem openSetSheafExtension_stalk_empty {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (F : TopCat.Sheaf (Type v) (openSubspace U)) (x : X) (hx : x ∉ U) :
    IsEmpty (((openSetSheafExtensionByEmpty U).obj F).presheaf.stalk x) := by
  sorry

/-- On the open, extension by the empty set has the original stalk. -/
theorem openSetSheafExtension_stalk_iso {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (F : TopCat.Sheaf (Type v) (openSubspace U)) (x : X) (hx : x ∈ U) :
    Nonempty (((openSetSheafExtensionByEmpty U).obj F).presheaf.stalk x ≃
      F.presheaf.stalk ⟨x, hx⟩) := by
  sorry

/-- Restricting an extension by the empty set recovers the original sheaf. -/
theorem openSetSheafExtension_restrict_iso {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (F : TopCat.Sheaf (Type v) (openSubspace U)) :
    Nonempty ((openSheafRestriction (Type v) U).obj
      ((openSetSheafExtensionByEmpty U).obj F) ≅ F) := by
  sorry

/-! ## Algebraic structures and modules -/

/-- Extension by the initial object for a category-valued sheaf. -/
noncomputable def openAlgebraicSheafExtensionFunctor (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    TopCat.Sheaf C (openSubspace U) ⥤ TopCat.Sheaf C X :=
  openSheafExtensionByInitial C U

/-- The algebraic-structure extension/restriction adjunction. -/
noncomputable def openAlgebraicSheafExtensionAdjunction (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    openAlgebraicSheafExtensionFunctor C U ⊣ openSheafRestriction C U := by
  exact openSheafExtensionAdjunction C U

/-- Initial stalk outside the open for an algebraic-structure extension. -/
theorem openAlgebraicSheafExtension_stalk_initial (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : TopCat.Sheaf C (openSubspace U)) (x : X) (hx : x ∉ U) :
    Nonempty (((openAlgebraicSheafExtensionFunctor C U).obj F).presheaf.stalk x ≅
      (⊥_ C)) := by
  sorry

/-- The original stalk on the open for an algebraic-structure extension. -/
theorem openAlgebraicSheafExtension_stalk_iso (C : Type u) [Category.{v} C]
    [HasInitial C] [HasColimits C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : TopCat.Sheaf C (openSubspace U)) (x : X) (hx : x ∈ U) :
    Nonempty (((openAlgebraicSheafExtensionFunctor C U).obj F).presheaf.stalk x ≅
      F.presheaf.stalk ⟨x, hx⟩) := by
  sorry

/-- Abelian sheaf extension by zero. -/
noncomputable abbrev openAbelianSheafExtensionFunctor {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :=
  openAlgebraicSheafExtensionFunctor AddCommGrpCat U

/-- A section of the extension by zero of a constant additive sheaf on a
preconnected open which meets the complement of the extension locus is
zero. -/
theorem openAbelianSheafExtension_constant_sections_isZero_of_isPreconnected
    {X : TopCat.{v}} (U V : Opens X) (A : AddCommGrpCat.{v})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    (hV : IsPreconnected (V : Set X))
    (x₀ : X) (hx₀V : x₀ ∈ V) (hx₀U : x₀ ∉ U) :
    IsZero (((openAbelianSheafExtensionFunctor U).obj
      ((CategoryTheory.constantSheaf
        (Opens.grothendieckTopology (openSubspace U))
        AddCommGrpCat.{v}).obj A)).presheaf.obj (op V)) := by
  let F := (CategoryTheory.constantSheaf
    (Opens.grothendieckTopology (openSubspace U))
    AddCommGrpCat.{v}).obj A
  let E := (openAbelianSheafExtensionFunctor U).obj F
  rcases openAlgebraicSheafExtension_restrict_iso
    AddCommGrpCat.{v} U F with ⟨e⟩
  have hsupportU : ∀ (s : E.presheaf.obj (op V)) (x : V),
      x ∈ additiveSectionSupport E V s → x.1 ∈ U := by
    intro s x hx
    by_contra hxU
    rcases openAlgebraicSheafExtension_stalk_initial
      AddCommGrpCat.{v} U F x.1 hxU with ⟨ez⟩
    have hezinj : Function.Injective (ConcreteCategory.hom ez.hom) := by
      intro a b hab
      have hab' := congrArg (ConcreteCategory.hom ez.inv) hab
      have hleft : ConcreteCategory.hom ez.inv
          (ConcreteCategory.hom ez.hom a) = a := by
        change ConcreteCategory.hom (ez.hom ≫ ez.inv) a = a
        rw [ez.hom_inv_id]
        rfl
      have hright : ConcreteCategory.hom ez.inv
          (ConcreteCategory.hom ez.hom b) = b := by
        change ConcreteCategory.hom (ez.hom ≫ ez.inv) b = b
        rw [ez.hom_inv_id]
        rfl
      exact hleft.symm.trans (hab'.trans hright)
    apply hx
    apply hezinj
    let ezero : (⊥_ AddCommGrpCat.{v}) ≅ (0 : AddCommGrpCat.{v}) :=
      initialIsInitial.uniqueUpToIso
        (CategoryTheory.Limits.isZero_zero AddCommGrpCat.{v}).isInitial
    have hzeroInitial : IsZero (⊥_ AddCommGrpCat.{v}) :=
      (CategoryTheory.Limits.isZero_zero AddCommGrpCat.{v}).of_iso ezero
    have hsub : Subsingleton (↑(⊥_ AddCommGrpCat.{v})) :=
      AddCommGrpCat.subsingleton_of_isZero hzeroInitial
    exact hsub.elim _ _
  have hsection_zero : ∀ s : E.presheaf.obj (op V), s = 0 := by
    intro s
    let S := additiveSectionSupport E V s
    have hSclosed : IsClosed S := additiveSectionSupport_isClosed E V s
    have hSopen : IsOpen S :=
      additiveSectionSupport_isOpen_of_restrict_iso_constant
        E U A e V s (hsupportU s)
    have hSclopen : IsClopen S := ⟨hSclosed, hSopen⟩
    let : PreconnectedSpace V := Subtype.preconnectedSpace hV
    let xV : V := ⟨x₀, hx₀V⟩
    have hxVnot : xV ∉ S := by
      intro hxS
      exact hx₀U (hsupportU s xV hxS)
    have hSne : S ≠ Set.univ := by
      intro hSu
      apply hxVnot
      rw [hSu]
      exact Set.mem_univ _
    have hSempty : S = ∅ :=
      (isClopen_iff.mp hSclopen).resolve_right hSne
    apply TopCat.Presheaf.section_ext E V
    intro x hxV
    have hxnot : (⟨x, hxV⟩ : V) ∉ S := by
      rw [hSempty]
      simp only [Set.mem_empty_iff_false, not_false_eq_true]
    have hg : ConcreteCategory.hom (E.presheaf.germ V x hxV) s = 0 := by
      exact not_ne_iff.mp hxnot
    simpa only [map_zero] using hg
  change IsZero (E.presheaf.obj (op V))
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  constructor
  intro s t
  exact (hsection_zero s).trans (hsection_zero t).symm

/-- The positive half-line, named here for the extension-by-zero
infrastructure. -/
def positiveRealHalfLine : Opens (TopCat.of ℝ) :=
  ⟨Set.Ioi (0 : ℝ), isOpen_Ioi⟩

/-- Extension by zero of a constant additive sheaf from the positive
half-line. -/
noncomputable def positiveRealHalfLineConstantExtension
    (A : AddCommGrpCat) : TopCat.Sheaf AddCommGrpCat (TopCat.of ℝ) :=
  (openAbelianSheafExtensionFunctor positiveRealHalfLine).obj
    ((CategoryTheory.constantSheaf
      (Opens.grothendieckTopology (openSubspace positiveRealHalfLine))
      AddCommGrpCat).obj A)

/-- Sections of a positive-half-line constant extension vanish on an
interval which meets both the positive half-line and its complement. -/
theorem positiveRealHalfLineConstantExtension_interval_sections_isZero
    (A : AddCommGrpCat) (a b : ℝ) (ha : a < 0) (hb : 0 < b) :
    IsZero ((positiveRealHalfLineConstantExtension A).presheaf.obj
      (op (⟨Set.Ioo a b, isOpen_Ioo⟩ : Opens (TopCat.of ℝ)))) := by
  apply openAbelianSheafExtension_constant_sections_isZero_of_isPreconnected
    positiveRealHalfLine
    (⟨Set.Ioo a b, isOpen_Ioo⟩ : Opens (TopCat.of ℝ)) A
    isPreconnected_Ioo (0 : ℝ)
  · exact ⟨ha, hb⟩
  · change ¬ (0 : ℝ) < 0
    exact lt_irrefl 0

/-- At a positive point, every morphism from a constant additive sheaf to
the positive-half-line constant extension induces the zero map on stalks. -/
theorem positiveRealHalfLineConstantExtension_stalk_map_eq_zero
    (A B : AddCommGrpCat)
    (f : (CategoryTheory.constantSheaf
      (Opens.grothendieckTopology (TopCat.of ℝ)) AddCommGrpCat).obj B ⟶
        positiveRealHalfLineConstantExtension A)
    (x : ℝ) (hx : 0 < x) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.hom = 0 := by
  let V : Opens (TopCat.of ℝ) :=
    ⟨Set.Ioo (-1 : ℝ) (x + 1), isOpen_Ioo⟩
  have hxV : x ∈ V := by
    change -1 < x ∧ x < x + 1
    constructor <;> linarith
  have hV : IsZero
      ((positiveRealHalfLineConstantExtension A).presheaf.obj (op V)) := by
    exact positiveRealHalfLineConstantExtension_interval_sections_isZero
      A (-1) (x + 1) (by norm_num) (by linarith)
  exact constantAddCommGrpSheaf_stalk_map_eq_zero_of_isZero
    B (positiveRealHalfLineConstantExtension A) f V x hxV hV

/-- The abelian sheaf extension/restriction adjunction. -/
noncomputable abbrev openAbelianSheafExtensionAdjunction
    {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :
    openAbelianSheafExtensionFunctor U ⊣
      openSheafRestriction AddCommGrpCat U :=
  openAlgebraicSheafExtensionAdjunction AddCommGrpCat U

/-- Extension by zero for abelian sheaves is fully faithful. -/
theorem openAbelianSheafExtension_fullFaithful {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat] :
    Nonempty (openAbelianSheafExtensionFunctor U).FullyFaithful := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- The open-extension counit is an isomorphism on stalks over the open. -/
theorem openAbelianSheafExtension_counit_stalk_map_isIso
    {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    (F : TopCat.Sheaf AddCommGrpCat X) (x : X) (hx : x ∈ U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((openAbelianSheafExtensionAdjunction U).counit.app F).hom) := by
  let hff := Classical.choice (openAbelianSheafExtension_fullFaithful U)
  let : (openAbelianSheafExtensionFunctor U).Full := hff.full
  let : (openAbelianSheafExtensionFunctor U).Faithful := hff.faithful
  let f := (openAbelianSheafExtensionAdjunction U).counit.app F
  let e := openSheafRestrictionStalkIso AddCommGrpCat.{v} U
    (⟨x, hx⟩ : (openSubspace U : Type v))
  have : IsIso ((openSheafRestriction AddCommGrpCat U).map f) := inferInstance
  have : IsIso (((openSheafRestriction AddCommGrpCat U).map f).hom) := by
    change IsIso ((TopCat.Sheaf.forget AddCommGrpCat (openSubspace U)).map
      ((openSheafRestriction AddCommGrpCat U).map f))
    infer_instance
  have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v}
      (⟨x, hx⟩ : (openSubspace U : Type v))).map
      ((openSheafRestriction AddCommGrpCat U).map f).hom) := by infer_instance
  have h := e.hom.naturality f
  have hleft : IsIso
      ((openSheafRestriction AddCommGrpCat U ⋙
          TopCat.Sheaf.forget AddCommGrpCat (openSubspace U) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v}
            (⟨x, hx⟩ : (openSubspace U : Type v))).map f ≫
        e.hom.app ((Functor.id (TopCat.Sheaf AddCommGrpCat X)).obj F)) := by
    apply IsIso.comp_isIso'
    · change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v}
          (⟨x, hx⟩ : (openSubspace U : Type v))).map
        ((openSheafRestriction AddCommGrpCat U).map f).hom)
      infer_instance
    · infer_instance
  have htarget : IsIso ((TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v}
        ((openInclusion U) (⟨x, hx⟩ : (openSubspace U : Type v)))).map f) := by
    let := hleft
    exact IsIso.of_isIso_fac_left h.symm
  change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map f.hom) at htarget
  exact htarget

set_option backward.isDefEq.respectTransparency false in
/-- The counit of open extension and restriction agrees on a stalk over the
open with the canonical extension and restriction stalk identifications. -/
theorem openAbelianSheafExtension_counit_stalk_map_compatibility
    {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    (F : TopCat.Sheaf AddCommGrpCat X) (x : X) (hx : x ∈ U) :
    ∃ e₁ :
        ((openAbelianSheafExtensionFunctor U).obj
          ((openSheafRestriction AddCommGrpCat U).obj F)).presheaf.stalk x ≅
          ((openSheafRestriction AddCommGrpCat U).obj F).presheaf.stalk
            ⟨x, hx⟩,
      ∃ e₂ :
          ((openSheafRestriction AddCommGrpCat U).obj F).presheaf.stalk
              ⟨x, hx⟩ ≅ F.presheaf.stalk ((openInclusion U) ⟨x, hx⟩),
        e₁.hom ≫ e₂.hom =
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            ((openAbelianSheafExtensionAdjunction U).counit.app F).hom := by
  let m := (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((openAbelianSheafExtensionAdjunction U).counit.app F).hom
  let : IsIso m := openAbelianSheafExtension_counit_stalk_map_isIso U F x hx
  let e₂ := (openSheafRestrictionStalkIso AddCommGrpCat U ⟨x, hx⟩).app F
  refine ⟨asIso m ≪≫ e₂.symm, e₂, ?_⟩
  change m ≫ e₂.inv ≫ e₂.hom = m
  simp

/-- The module-valued open subspace of a ringed space. -/
def ringedOpenSubspace (X : RingedSpace.{v}) (U : Opens X.carrier) : RingedSpace.{v} where
  carrier := openSubspace U
  structureSheaf := (TopologicalSpace.Opens.sheafRestrict U).obj X.structureSheaf

/-- The canonical morphism of ringed spaces from an open subspace. -/
noncomputable def ringedOpenInclusion (X : RingedSpace.{v}) (U : Opens X.carrier) :
    RingedSpaceHom (ringedOpenSubspace X U) X where
  continuous := openInclusion U
  sharp := by
    let hU : IsOpenEmbedding (openInclusion U) := U.isOpenEmbedding
    exact (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
      (openInclusion U)).unit.app X.structureSheaf ≫
      (TopCat.Sheaf.pushforward RingCat (openInclusion U)).map
        ((Topology.IsOpenEmbedding.sheafPullbackIso (A := RingCat) hU).app
          X.structureSheaf).hom

 /-- A module extension by zero together with its underlying additive
presheaf identification. -/
 structure OpenModulePresheafExtensionData (X : RingedSpace.{v})
    (U : Opens X.carrier) where
  functor : PMod (ringedOpenSubspace X U).structureSheaf.obj ⥤
    PMod X.structureSheaf.obj
  restriction : PMod X.structureSheaf.obj ⥤
    PMod (ringedOpenSubspace X U).structureSheaf.obj
  underlying_functor_iso :
    Nonempty
      (functor ⋙ PresheafOfModules.toPresheaf X.structureSheaf.obj ≅
        PresheafOfModules.toPresheaf (ringedOpenSubspace X U).structureSheaf.obj ⋙
          openPresheafExtensionByInitial AddCommGrpCat U)
  adjunction : functor ⊣ restriction

 /-- Extension by zero for modules on an open subspace. -/
theorem exists_openModulePresheafExtensionByZero (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Nonempty (OpenModulePresheafExtensionData X U) := by
  sorry

noncomputable def openModulePresheafExtensionData (X : RingedSpace.{v})
    (U : Opens X.carrier) : OpenModulePresheafExtensionData X U :=
  Classical.choice (exists_openModulePresheafExtensionByZero X U)

/-! The module-valued presheaf construction is the initial-object extension
on the underlying additive presheaf, equipped with the ambient structure-sheaf
action.  Its categorical interface is chosen from the source construction. -/
noncomputable def openModulePresheafExtensionByZero (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    PMod (ringedOpenSubspace X U).structureSheaf.obj ⥤
      PMod X.structureSheaf.obj :=
  (openModulePresheafExtensionData X U).functor

/-- The underlying additive presheaf of module extension by zero is the
initial-object extension. -/
theorem openModulePresheafExtension_underlying_iso (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Nonempty
      (openModulePresheafExtensionByZero X U ⋙
          PresheafOfModules.toPresheaf X.structureSheaf.obj ≅
        PresheafOfModules.toPresheaf
            (ringedOpenSubspace X U).structureSheaf.obj ⋙
          openPresheafExtensionByInitial AddCommGrpCat U) :=
  (openModulePresheafExtensionData X U).underlying_functor_iso

/-- Restriction of presheaves of modules to an open subspace. -/
noncomputable def openModulePresheafRestrictionFunctor (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    PMod X.structureSheaf.obj ⥤
      PMod (ringedOpenSubspace X U).structureSheaf.obj :=
  (openModulePresheafExtensionData X U).restriction

/-- The presheaf-module extension by zero is left adjoint to restriction. -/
theorem exists_openModulePresheafExtensionAdjunction (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Nonempty (openModulePresheafExtensionByZero X U ⊣
      openModulePresheafRestrictionFunctor X U) := by
  exact ⟨(openModulePresheafExtensionData X U).adjunction⟩

noncomputable def openModulePresheafExtensionAdjunction (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    openModulePresheafExtensionByZero X U ⊣
      openModulePresheafRestrictionFunctor X U :=
  (openModulePresheafExtensionData X U).adjunction

/-- Extension by zero for modules on an open subspace. -/
noncomputable def openModuleExtensionFunctor (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Mod (ringedOpenSubspace X U).structureSheaf ⥤ Mod X.structureSheaf := by
  exact
    SheafOfModules.forget (ringedOpenSubspace X U).structureSheaf ⋙
      openModulePresheafExtensionByZero X U ⋙
      PresheafOfModules.sheafification (𝟙 X.structureSheaf.obj)

theorem exists_openModuleExtensionFunctor (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Nonempty (Mod (ringedOpenSubspace X U).structureSheaf ⥤ Mod X.structureSheaf) :=
  ⟨openModuleExtensionFunctor X U⟩

noncomputable abbrev openModuleSheafExtensionByZero (X : RingedSpace.{v})
    (U : Opens X.carrier) :
    Mod (ringedOpenSubspace X U).structureSheaf ⥤ Mod X.structureSheaf :=
  openModuleExtensionFunctor X U

/-- Restriction of modules to an open subspace. -/
noncomputable def openModuleRestrictionFunctor (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Mod X.structureSheaf ⥤ Mod (ringedOpenSubspace X U).structureSheaf := by
  letI : (SheafOfModules.pushforward (ringedOpenInclusion X U).sharp).IsRightAdjoint := by
    sorry
  exact ringedSpaceModulePullback (ringedOpenInclusion X U)

/-- The module extension/restriction adjunction for an open subspace. -/
theorem exists_openModuleExtensionAdjunction (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (openModuleExtensionFunctor X U ⊣ openModuleRestrictionFunctor X U) := by
  sorry

/-- The module extension/restriction adjunction for an open subspace. -/
noncomputable def openModuleExtensionAdjunction (X : RingedSpace.{v}) (U : Opens X.carrier) :
    openModuleExtensionFunctor X U ⊣ openModuleRestrictionFunctor X U := by
  exact Classical.choice (exists_openModuleExtensionAdjunction X U)

/-- Module stalks of extension by zero vanish outside the open. -/
theorem openModuleExtension_stalk_zero (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod (ringedOpenSubspace X U).structureSheaf) (x : X.carrier) (hx : x ∉ U) :
    Nonempty ((moduleStalkFunctor X.structureSheaf x).obj
      ((openModuleExtensionFunctor X U).obj F) ≅ 0) := by
  sorry

/-- Module stalks of extension by zero agree with the original stalk on the open. -/
theorem openModuleExtension_stalk_iso (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod (ringedOpenSubspace X U).structureSheaf) (x : X.carrier) (hx : x ∈ U) :
    Nonempty ((moduleStalkFunctor X.structureSheaf x).obj
      ((openModuleExtensionFunctor X U).obj F) ≅
      (ModuleCat.restrictScalars
        (moduleSheafFMapStalkScalarMap
          (ringedOpenInclusion X U).sharp ⟨x, hx⟩).hom).obj
        ((moduleStalkFunctor (ringedOpenSubspace X U).structureSheaf
          ⟨x, hx⟩).obj F)) := by
  sorry

/-- The module restriction of extension by zero is the identity. -/
theorem openModuleExtension_restrict_iso (X : RingedSpace.{v}) (U : Opens X.carrier)
    (F : Mod (ringedOpenSubspace X U).structureSheaf) :
    Nonempty ((openModuleRestrictionFunctor X U).obj
      ((openModuleExtensionFunctor X U).obj F) ≅ F) := by
  sorry

/-! ## Essential images and exactness warnings -/

/-- The set-valued essential-image stalk condition for `j_!`. -/
def OpenEmptyStalkCondition {X : TopCat.{v}} (U : Opens X)
    (G : TopCat.Sheaf (Type v) X) : Prop :=
  ∀ x : X, x ∉ U → IsEmpty (G.presheaf.stalk x)

/-- Extension by the empty set is fully faithful. -/
theorem openSetSheafExtension_fullFaithful {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    Nonempty (openSetSheafExtensionByEmpty U).FullyFaithful := by
  sorry

/-- The essential image of `j_!` is characterized by empty outside stalks. -/
theorem openSetSheafExtension_essentialImage {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)]
    (G : TopCat.Sheaf (Type v) X) :
    (∃ F, Nonempty ((openSetSheafExtensionByEmpty U).obj F ≅ G)) ↔
      OpenEmptyStalkCondition U G := by
  sorry

/-- The abelian essential image of extension by zero is characterized by
zero stalks outside the open. -/
def OpenAbelianZeroStalkCondition {X : TopCat.{v}} (U : Opens X)
    (G : Ab X) : Prop :=
  ∀ x : X, x ∉ U → Nonempty (G.presheaf.stalk x ≅ (0 : AddCommGrpCat.{v}))

theorem openAbelianSheafExtension_essentialImage {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    (G : Ab X) :
    (∃ F, Nonempty ((openAbelianSheafExtensionFunctor U).obj F ≅ G)) ↔
      OpenAbelianZeroStalkCondition U G := by
  sorry

/-- The generic algebraic essential image of extension by the initial object
is characterized by initial stalks outside the open. -/
def OpenInitialStalkCondition (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X) [HasColimits C]
    (G : TopCat.Sheaf C X) : Prop :=
  ∀ x : X, x ∉ U → Nonempty (G.presheaf.stalk x ≅ (⊥_ C))

theorem openAlgebraicSheafExtension_fullFaithful (C : Type u) [Category.{v} C]
    [HasInitial C] {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    Nonempty (openAlgebraicSheafExtensionFunctor C U).FullyFaithful := by
  sorry

theorem openAlgebraicSheafExtension_essentialImage (C : Type u)
    [Category.{v} C] [HasInitial C] [HasColimits C]
    {X : TopCat.{v}} (U : Opens X)
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (G : TopCat.Sheaf C X) :
    (∃ F, Nonempty ((openAlgebraicSheafExtensionFunctor C U).obj F ≅ G)) ↔
      OpenInitialStalkCondition C U G := by
  sorry

/-- Extension by zero for modules is fully faithful. -/
theorem openModuleExtension_fullFaithful (X : RingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (openModuleExtensionFunctor X U).FullyFaithful := by
  sorry

/-- The module essential image of extension by zero is characterized by zero
stalk modules outside the open. -/
def OpenModuleZeroStalkCondition (X : RingedSpace.{v})
    (U : Opens X.carrier) (G : Mod X.structureSheaf) : Prop :=
  ∀ x : X.carrier, x ∉ U →
    Nonempty ((moduleStalkFunctor X.structureSheaf x).obj G ≅ 0)

theorem openModuleExtension_essentialImage (X : RingedSpace.{v})
    (U : Opens X.carrier) (G : Mod X.structureSheaf) :
    (∃ F, Nonempty ((openModuleExtensionFunctor X U).obj F ≅ G)) ↔
      OpenModuleZeroStalkCondition X U G := by
  sorry

/-- The set-valued `j_!` warning: a nontrivial open complement prevents left exactness. -/
theorem openSetSheafExtension_not_left_exact {X : TopCat.{v}} (U : Opens X)
    (hU : ∃ x : X, x ∉ U)
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type v)] :
    ¬ PreservesFiniteLimits (openSetSheafExtensionByEmpty U) := by
  sorry

end

end Formalization.Books.Sheaves.Unit22
