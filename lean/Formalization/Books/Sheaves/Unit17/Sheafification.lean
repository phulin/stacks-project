import Formalization.Books.Sheaves.Unit11.Stalks
import Formalization.Books.Sheaves.Unit16.ExactnessAndPoints
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Sheaves on Spaces, Chapter 17, Section 1: Sheafification

The source span is `books/sheaves.tex:1458-1661`.  The pointwise product of
stalks and the local-germ condition are Mathlib's canonical
`presheafToTypes`/`LocalPredicate` construction.  In particular, the
sheafification below is `TopCat.Presheaf.sheafify`; this avoids introducing a
second implementation of the plus construction.
-/

namespace Formalization.Books.Sheaves.Unit17

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit07
open Formalization.Books.Sheaves.Unit11
open Formalization.Books.Sheaves.Unit16

universe v

noncomputable section

/-! ## The stalkwise product and the local-germ condition -/

/-- The presheaf `Π(F)` with sections `∏ x ∈ U, Fₓ`. -/
def stalkProductPresheaf {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) : TopCat.Presheaf (Type v) X :=
  TopCat.presheafToTypes X (fun x : X => F.stalk x)

@[simp]
theorem stalkProductPresheaf_obj {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (U : Opens X) :
    (stalkProductPresheaf F).obj (op U) =
      ∀ x : U, F.stalk x := rfl

/-- `Π(F)` is the sheaf of all dependent functions into the stalks. -/
theorem stalkProductPresheaf_isSheaf {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    TopCat.Presheaf.IsSheaf (stalkProductPresheaf F) := by
  exact TopCat.Presheaf.toTypes_isSheaf X (fun x : X => F.stalk x)

/-- The sheaf corresponding to the stalkwise product presheaf. -/
def stalkProductSheaf {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) : TopCat.Sheaf (Type v) X :=
  ⟨stalkProductPresheaf F, stalkProductPresheaf_isSheaf F⟩

/-- The source's condition `(*)`, expressed through Mathlib's local-germ API. -/
def sheafificationCondition {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) {U : Opens X}
    (s : ∀ x : U, F.stalk x) : Prop :=
  (TopCat.Presheaf.Sheafify.isLocallyGerm F).pred s

/-- Expanded form of the local-germ condition used in the source. -/
theorem sheafificationCondition_iff {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) {U : Opens X}
    (s : ∀ x : U, F.stalk x) :
    sheafificationCondition F s ↔
      ∀ x : U, ∃ (V : Opens X) (_hxV : x.1 ∈ V) (i : V ⟶ U)
        (σ : F.obj (op V)),
        ∀ y : V, s (i y) = F.germ V y.1 y.2 σ := by
  rfl

/-! ## The canonical sheafification and its maps -/

/-- The canonical sheafification `F#` of a set-valued presheaf. -/
def sheafification {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) : TopCat.Sheaf (Type v) X :=
  F.sheafify

/-- The presheaf underlying the canonical sheafification. -/
abbrev sheafificationPresheaf {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) : TopCat.Presheaf (Type v) X :=
  (sheafification F).presheaf

@[simp]
theorem sheafificationPresheaf_obj {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (U : Opens X) :
    (sheafificationPresheaf F).obj (op U) =
      {s : ∀ x : U, F.stalk x // sheafificationCondition F s} := rfl

/-- The sheafification map `F → F#`. -/
abbrev sheafificationUnit {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    F ⟶ sheafificationPresheaf F :=
  F.toSheafify

/-- The inclusion `F# → Π(F)`. -/
def sheafificationProductMap {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    sheafificationPresheaf F ⟶ stalkProductPresheaf F :=
  TopCat.subpresheafToTypes.subtype
    (TopCat.Presheaf.Sheafify.isLocallyGerm F).toPrelocalPredicate

/-- The canonical map `F → Π(F)` obtained from the two maps in the source. -/
abbrev presheafToStalkProduct {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    F ⟶ stalkProductPresheaf F :=
  sheafificationUnit F ≫ sheafificationProductMap F

theorem sheafificationUnit_comp_productMap {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    sheafificationUnit F ≫ sheafificationProductMap F =
      presheafToStalkProduct F := rfl

/-- The component of `F → Π(F)` sends a section to all of its germs. -/
theorem presheafToStalkProduct_app_apply {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (U : Opens X)
    (s : F.obj (op U)) (x : U) :
    (presheafToStalkProduct F).app (op U) s x =
      F.germ U x.1 x.2 s := by
  rfl

private theorem existsUnique_sheafificationLift_aux {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X)
    (φ : F ⟶ G.presheaf) :
    ∃! ψ : sheafificationPresheaf F ⟶ G.presheaf,
      sheafificationUnit F ≫ ψ = φ := by
  classical
  let LiftProperty : ∀ (U : Opens X),
      (s : (sheafificationPresheaf F).obj (op U)) →
        (t : G.presheaf.obj (op U)) → Prop := fun U s t =>
    ∀ x : U,
      ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ) (s.1 x) =
        G.presheaf.germ U x.1 x.2 t
  have lift_exists (U : Opens X) (s : (sheafificationPresheaf F).obj (op U)) :
      ∃ t : G.presheaf.obj (op U), LiftProperty U s t := by
    choose V hxV i σ hs using
      fun x : U => (sheafificationCondition_iff F s.1).mp s.2 x
    let sf : ∀ x : U, G.presheaf.obj (op (V x)) :=
      fun x => (φ.app (op (V x))) (σ x)
    have hcover : U ≤ iSup V := by
      intro x hx
      simp only [Opens.mem_iSup]
      exact ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
    have hcompat : TopCat.Presheaf.IsCompatible G.presheaf V sf := by
      intro x y
      apply TopCat.Presheaf.section_ext G (V x ⊓ V y)
      intro z hz
      have hz' : z ∈ V x ∧ z ∈ V y := by simpa using hz
      have hF : F.germ (V x) z hz'.1 (σ x) = F.germ (V y) z hz'.2 (σ y) := by
        calc
          F.germ (V x) z hz'.1 (σ x) = s.1 (i x ⟨z, hz'.1⟩) :=
            (hs x ⟨z, hz'.1⟩).symm
          _ = s.1 (i y ⟨z, hz'.2⟩) := by
            have hp : (i x) ⟨z, hz'.1⟩ = (i y) ⟨z, hz'.2⟩ := by
              apply Subtype.ext
              rfl
            cases hp
            rfl
          _ = F.germ (V y) z hz'.2 (σ y) := hs y ⟨z, hz'.2⟩
      have hG : G.presheaf.germ (V x) z hz'.1 (sf x) =
          G.presheaf.germ (V y) z hz'.2 (sf y) := by
        dsimp [sf]
        rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,
          ← TopCat.Presheaf.stalkFunctor_map_germ_apply]
        exact congrArg
          ((TopCat.Presheaf.stalkFunctor (Type v) z).map φ) hF
      rw [G.presheaf.germ_res_apply, G.presheaf.germ_res_apply]
      exact hG
    obtain ⟨t, ht, -⟩ := G.existsUnique_gluing' V U i hcover sf hcompat
    refine ⟨t, ?_⟩
    dsimp [LiftProperty]
    intro x
    have hxs : s.1 x = F.germ (V x) x.1 (hxV x) (σ x) := by
      calc
        s.1 x = s.1 (i x ⟨x.1, hxV x⟩) := by
          congr 1
        _ = F.germ (V x) x.1 (hxV x) (σ x) := hs x ⟨x.1, hxV x⟩
    rw [hxs]
    have h1 :
        ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ)
            (F.germ (V x) x.1 (hxV x) (σ x)) =
          G.presheaf.germ (V x) x.1 (hxV x) (sf x) := by
      simpa [sf] using TopCat.Presheaf.stalkFunctor_map_germ_apply
        (V x) x.1 (hxV x) φ (σ x)
    have h2 :
        G.presheaf.germ (V x) x.1 (hxV x) (sf x) =
          G.presheaf.germ (V x) x.1 (hxV x)
            (G.presheaf.map (i x).op t) :=
      congrArg (G.presheaf.germ (V x) x.1 (hxV x)) (ht x).symm
    have h3 :
        G.presheaf.germ (V x) x.1 (hxV x)
            (G.presheaf.map (i x).op t) =
          G.presheaf.germ U x.1 x.2 t := by
      simp
    exact h1.trans (h2.trans h3)
  let liftApp : ∀ (U : Opens X),
      (sheafificationPresheaf F).obj (op U) → G.presheaf.obj (op U) :=
    fun U s => Classical.choose (lift_exists U s)
  have liftApp_property (U : Opens X)
      (s : (sheafificationPresheaf F).obj (op U)) :
      LiftProperty U s (liftApp U s) :=
    Classical.choose_spec (lift_exists U s)
  have section_ext_of_germ {U : Opens X}
      {a b : G.presheaf.obj (op U)}
      (h : ∀ x : U, G.presheaf.germ U x.1 x.2 a =
        G.presheaf.germ U x.1 x.2 b) : a = b := by
    apply TopCat.Presheaf.section_ext G U
    intro x hx
    exact h ⟨x, hx⟩
  let ψ : sheafificationPresheaf F ⟶ G.presheaf := {
    app U := TypeCat.ofHom (liftApp U.unop)
    naturality := by
      intro U V i
      induction U with
      | op U =>
        induction V with
        | op V =>
          apply ConcreteCategory.hom_ext
          intro s
          apply section_ext_of_germ
          intro x
          have hleft := liftApp_property V
            ((sheafificationPresheaf F).map i s) x
          have hright := liftApp_property U s
            ⟨x.1, (i.unop.le x.2)⟩
          have hsmap : ((sheafificationPresheaf F).map i s).1 x =
              s.1 (i.unop x) := rfl
          have h1 :
              G.presheaf.germ V x.1 x.2
                  (liftApp V ((sheafificationPresheaf F).map i s)) =
                ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ)
                  (((sheafificationPresheaf F).map i s).1 x) := hleft.symm
          have h2 :
              ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ)
                  (((sheafificationPresheaf F).map i s).1 x) =
                ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ)
                  (s.1 (i.unop x)) := congrArg _ hsmap
          have h3 :
              ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ)
                  (s.1 (i.unop x)) =
                G.presheaf.germ U x.1 (i.unop.le x.2) (liftApp U s) := hright
          have h4 :
              G.presheaf.germ U x.1 (i.unop.le x.2) (liftApp U s) =
                G.presheaf.germ V x.1 x.2
                  (G.presheaf.map i.unop.op (liftApp U s)) := by
            simpa using (G.presheaf.germ_res_apply i.unop x.1 x.2 (liftApp U s)).symm
          exact h1.trans (h2.trans (h3.trans h4))
  }
  have hψ : sheafificationUnit F ≫ ψ = φ := by
    ext U s
    apply section_ext_of_germ
    intro x
    change G.presheaf.germ U x.1 x.2
        (liftApp U ((sheafificationUnit F).app (op U) s)) =
      G.presheaf.germ U x.1 x.2 (φ.app (op U) s)
    have h := liftApp_property U
      ((sheafificationUnit F).app (op U) s) x
    have h1 :
        G.presheaf.germ U x.1 x.2
            (liftApp U ((sheafificationUnit F).app (op U) s)) =
          ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ)
            (((sheafificationUnit F).app (op U) s).1 x) := h.symm
    have h2 :
        ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ)
            (((sheafificationUnit F).app (op U) s).1 x) =
          ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ)
            (F.germ U x.1 x.2 s) := by rfl
    have h3 :
        ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ)
            (F.germ U x.1 x.2 s) =
          G.presheaf.germ U x.1 x.2 (φ.app (op U) s) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply U x.1 x.2 φ s
    exact h1.trans (h2.trans h3)
  refine ⟨ψ, hψ, ?_⟩
  intro ψ' hψ'
  ext U s
  apply section_ext_of_germ
  intro x
  change G.presheaf.germ U x.1 x.2 (ψ'.app (op U) s) =
    G.presheaf.germ U x.1 x.2 (liftApp U s)
  have hL := liftApp_property U s x
  obtain ⟨V, hxV, i, σ, hs⟩ :=
    (sheafificationCondition_iff F s.1).mp s.2 x
  have hs_eq : (sheafificationPresheaf F).map i.op s =
      (sheafificationUnit F).app (op V) σ := by
    apply Subtype.ext
    funext y
    change s.1 (i y) = F.germ V y.1 y.2 σ
    exact hs y
  have hfactor : (ψ'.app (op V))
      ((sheafificationUnit F).app (op V) σ) = (φ.app (op V)) σ := by
    have h := congrArg (fun q => q σ) (congr_app hψ' (op V))
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    exact h
  have hnat : G.presheaf.map i.op (ψ'.app (op U) s) =
      (ψ'.app (op V)) ((sheafificationPresheaf F).map i.op s) := by
    have h := congrArg (fun q => q s) (ψ'.naturality i.op)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact h.symm
  have hxs : s.1 x = F.germ V x.1 hxV σ := by
    simpa [show i = i from rfl] using (hs ⟨x.1, hxV⟩)
  have h5 : G.presheaf.germ V x.1 hxV ((φ.app (op V)) σ) =
      ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ)
        (F.germ V x.1 hxV σ) := by
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply V x.1 hxV φ σ).symm
  have h6 :
      ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ)
          (F.germ V x.1 hxV σ) =
        ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ) (s.1 x) :=
    congrArg (fun z => ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ) z)
      hxs.symm
  have h7 :
      ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ) (s.1 x) =
        G.presheaf.germ U x.1 x.2 (liftApp U s) := hL
  have k1 :
      G.presheaf.germ U x.1 x.2 (ψ'.app (op U) s) =
        G.presheaf.germ V x.1 hxV (G.presheaf.map i.op (ψ'.app (op U) s)) := by
    simp
  have k2 :
      G.presheaf.germ V x.1 hxV (G.presheaf.map i.op (ψ'.app (op U) s)) =
        G.presheaf.germ V x.1 hxV
          ((ψ'.app (op V)) ((sheafificationPresheaf F).map i.op s)) :=
    congrArg (G.presheaf.germ V x.1 hxV) hnat
  have k3 :
      G.presheaf.germ V x.1 hxV
          ((ψ'.app (op V)) ((sheafificationPresheaf F).map i.op s)) =
        G.presheaf.germ V x.1 hxV
          ((ψ'.app (op V)) ((sheafificationUnit F).app (op V) σ)) :=
    congrArg (fun q => G.presheaf.germ V x.1 hxV ((ψ'.app (op V)) q)) hs_eq
  have k4 :
      G.presheaf.germ V x.1 hxV
          ((ψ'.app (op V)) ((sheafificationUnit F).app (op V) σ)) =
        G.presheaf.germ V x.1 hxV ((φ.app (op V)) σ) :=
    congrArg (G.presheaf.germ V x.1 hxV) hfactor
  exact k1.trans (k2.trans (k3.trans (k4.trans (h5.trans (h6.trans h7)))))

/-- The construction `F ↦ (F → F# → Π(F))` is functorial in `F`. -/
theorem sheafification_maps_are_functorial {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) :
    ∃ ψ : sheafificationPresheaf F ⟶ sheafificationPresheaf G,
      sheafificationUnit F ≫ ψ = φ ≫ sheafificationUnit G := by
  exact (existsUnique_sheafificationLift_aux F (sheafification G)
    (φ ≫ sheafificationUnit G)).exists

/-! ## Sheaf property, stalks, and the universal property -/

/-- The canonical `F#` is a sheaf. -/
theorem sheafification_isSheaf {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    TopCat.Presheaf.IsSheaf (sheafificationPresheaf F) := by
  exact (sheafification F).property

/-- The canonical stalk comparison `F#ₓ ≅ Fₓ`. -/
noncomputable def sheafificationStalkIso {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (x : X) :
    (sheafificationPresheaf F).stalk x ≅ F.stalk x :=
  TopCat.Presheaf.sheafifyStalkIso F x

/-- The source's stalk equality, represented by the canonical inverse equivalence. -/
noncomputable def sheafificationStalkEquiv {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (x : X) :
    F.stalk x ≃ (sheafificationPresheaf F).stalk x :=
  (sheafificationStalkIso F x).toEquiv.symm

/-- The map `Fₓ → F#ₓ` induced by the sheafification unit is bijective. -/
theorem sheafificationUnit_stalk_bijective {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (x : X) :
    Function.Bijective
      ((TopCat.Presheaf.stalkFunctor (Type v) x).map (sheafificationUnit F)) := by
  let u := (TopCat.Presheaf.stalkFunctor (Type v) x).map (sheafificationUnit F)
  let p := TopCat.Presheaf.stalkToFiber F x
  have hcomp : u ≫ p = 𝟙 _ := by
    apply TopCat.Presheaf.stalk_hom_ext F
    intro U hx
    apply ConcreteCategory.hom_ext
    intro s
    change p (u (F.germ U x hx s)) = F.germ U x hx s
    rw [show u (F.germ U x hx s) =
      (sheafificationPresheaf F).germ U x hx ((sheafificationUnit F).app (op U) s) by
        exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (sheafificationUnit F) s]
    exact TopCat.stalkToFiber_germ _ _ _ _ _
  constructor
  · intro a b hab
    have ha : p (u a) = a := by
      have h := congrArg
        (fun f : (TopCat.Presheaf.stalkFunctor (Type v) x).obj F ⟶
          (TopCat.Presheaf.stalkFunctor (Type v) x).obj F => f a) hcomp
      change p (u a) = a at h
      exact h
    have hb : p (u b) = b := by
      have h := congrArg
        (fun f : (TopCat.Presheaf.stalkFunctor (Type v) x).obj F ⟶
          (TopCat.Presheaf.stalkFunctor (Type v) x).obj F => f b) hcomp
      change p (u b) = b at h
      exact h
    rw [← ha, ← hb]
    exact congrArg (fun z => p z) hab
  · intro b
    let b' : F.sheafify.presheaf.stalk x := b
    refine ⟨p b', ?_⟩
    change u (p b') = b'
    apply (TopCat.Presheaf.stalkToFiber_injective F x)
    change p (u (p b')) = p b'
    have h := congrArg
      (fun f : (TopCat.Presheaf.stalkFunctor (Type v) x).obj F ⟶
        (TopCat.Presheaf.stalkFunctor (Type v) x).obj F => f (p b')) hcomp
    change p (u (p b')) = p b' at h
    exact h

/-- Every map from `F` to a sheaf factors through `F#`. -/
theorem existsUnique_sheafificationLift {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X)
    (φ : F ⟶ G.presheaf) :
    ∃! ψ : sheafificationPresheaf F ⟶ G.presheaf,
      sheafificationUnit F ≫ ψ = φ := by
  exact existsUnique_sheafificationLift_aux F G φ

/-- The chosen factorization through `F#`. -/
noncomputable def sheafificationLift {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X)
    (φ : F ⟶ G.presheaf) :
    sheafificationPresheaf F ⟶ G.presheaf :=
  Classical.choose (existsUnique_sheafificationLift F G φ).exists

theorem sheafificationUnit_comp_lift {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X)
    (φ : F ⟶ G.presheaf) :
    sheafificationUnit F ≫ sheafificationLift F G φ = φ := by
  exact Classical.choose_spec (existsUnique_sheafificationLift F G φ).exists

/-- The chosen lift is the unique map with the required factorization property. -/
theorem sheafificationLift_unique {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X)
    (φ : F ⟶ G.presheaf) (ψ : sheafificationPresheaf F ⟶ G.presheaf)
    (hψ : sheafificationUnit F ≫ ψ = φ) :
    ψ = sheafificationLift F G φ := by
  exact (existsUnique_sheafificationLift F G φ).unique hψ
    (sheafificationUnit_comp_lift F G φ)

/-- The Hom-set bijection expressing the sheafification adjunction. -/
noncomputable def sheafificationHomEquiv {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X) :
    (sheafificationPresheaf F ⟶ G.presheaf) ≃ (F ⟶ G.presheaf) where
  toFun ψ := sheafificationUnit F ≫ ψ
  invFun φ := sheafificationLift F G φ
  left_inv ψ := by
    let φ := sheafificationUnit F ≫ ψ
    have h₁ : sheafificationUnit F ≫ ψ = φ := rfl
    have h₂ : sheafificationUnit F ≫ sheafificationLift F G φ = φ :=
      sheafificationUnit_comp_lift F G φ
    have huniq : ψ = sheafificationLift F G φ :=
      (existsUnique_sheafificationLift F G φ).unique h₁ h₂
    exact huniq.symm
  right_inv φ := sheafificationUnit_comp_lift F G φ

/-- The adjunction in the source's direction, from presheaf maps to sheaf maps. -/
noncomputable def sheafificationAdjunctionHomEquiv {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (G : TopCat.Sheaf (Type v) X) :
    (F ⟶ G.presheaf) ≃ (sheafificationPresheaf F ⟶ G.presheaf) :=
  (sheafificationHomEquiv F G).symm

/-! ## The constant-presheaf example -/

noncomputable def constantPresheafSheafificationMap {X : TopCat.{v}} (A : Type v) :
    sheafificationPresheaf (constantPresheaf (X := X) A) ⟶
      (constantSheaf X A).presheaf :=
  sheafificationLift (constantPresheaf (X := X) A) (constantSheaf X A)
    (constantPresheafToConstantSheaf A)

/-- The sheafification of the constant presheaf is the constant sheaf. -/
theorem constantPresheafSheafificationMap_isIso {X : TopCat.{v}} (A : Type v) :
    IsIso (constantPresheafSheafificationMap (X := X) A) := by
  let P := constantPresheaf (X := X) A
  let f : sheafification P ⟶ constantSheaf X A :=
    ⟨constantPresheafSheafificationMap (X := X) A⟩
  let : IsIso f := (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso f).2 (by
    intro x
    rw [isIso_iff_bijective]
    let u := (TopCat.Presheaf.stalkFunctor (Type v) x).map (sheafificationUnit P)
    let v := (TopCat.Presheaf.stalkFunctor (Type v) x).map f.hom
    let w := (TopCat.Presheaf.stalkFunctor (Type v) x).map
      (constantPresheafToConstantSheaf A)
    have hu := sheafificationUnit_stalk_bijective P x
    have hw := constantSheafStalkMap_bijective A x
    have huv : u ≫ v = w := by
      dsimp [u, v, w]
      calc
        (TopCat.Presheaf.stalkFunctor (Type v) x).map (sheafificationUnit P) ≫
              (TopCat.Presheaf.stalkFunctor (Type v) x).map f.hom =
            (TopCat.Presheaf.stalkFunctor (Type v) x).map
              (sheafificationUnit P ≫ f.hom) :=
          (Functor.map_comp _ _ _).symm
        _ = (TopCat.Presheaf.stalkFunctor (Type v) x).map
              (constantPresheafToConstantSheaf A) := by
          rw [show sheafificationUnit P ≫ f.hom =
            constantPresheafToConstantSheaf A by
              exact sheafificationUnit_comp_lift P (constantSheaf X A)
                (constantPresheafToConstantSheaf A)]
    constructor
    · intro a b hab
      obtain ⟨a₀, ha₀⟩ := hu.2 a
      obtain ⟨b₀, hb₀⟩ := hu.2 b
      have hwab : w a₀ = w b₀ := by
        have h := congrArg (fun q => q a₀) huv
        have h' := congrArg (fun q => q b₀) huv
        change v (u a₀) = w a₀ at h
        change v (u b₀) = w b₀ at h'
        change u a₀ = a at ha₀
        change u b₀ = b at hb₀
        rw [ha₀] at h
        rw [hb₀] at h'
        have hₐ : v a = w a₀ := h
        have h_b : v b = w b₀ := h'
        exact hₐ.symm.trans (hab.trans h_b)
      have hwab' : constantSheafStalkMap A x a₀ = constantSheafStalkMap A x b₀ := by
        change (TopCat.Presheaf.stalkFunctor (Type v) x).map
            (constantPresheafToConstantSheaf A) a₀ =
          (TopCat.Presheaf.stalkFunctor (Type v) x).map
            (constantPresheafToConstantSheaf A) b₀
        exact hwab
      have hab₀ : a₀ = b₀ := hw.1 hwab'
      calc
        a = u a₀ := ha₀.symm
        _ = u b₀ := congrArg (fun z => u z) hab₀
        _ = b := hb₀
    · intro b
      obtain ⟨a, ha⟩ := hw.2 b
      refine ⟨u a, ?_⟩
      have h := congrArg (fun q => q a) huv
      change v (u a) = w a at h
      change v (u a) = b
      simpa [w, constantSheafStalkMap] using h.trans ha)
  change IsIso f.hom
  exact (TopCat.Sheaf.forget (Type v) X).map_isIso f

/-- A canonical isomorphism in the constant-presheaf example. -/
noncomputable def constantPresheafSheafificationIso {X : TopCat.{v}} (A : Type v) :
    sheafificationPresheaf (constantPresheaf (X := X) A) ≅
      (constantSheaf X A).presheaf := by
  letI := constantPresheafSheafificationMap_isIso (X := X) A
  exact asIso (constantPresheafSheafificationMap (X := X) A)

/-! ## Separatedness and injectivity/surjectivity -/

/-- A presheaf is separated exactly when its map to `F#` is sectionwise injective. -/
theorem separatedPresheaf_iff_sheafificationUnit_injective
    {X : TopCat.{v}} (F : TopCat.Presheaf (Type v) X) :
    SeparatedPresheaf F ↔
      PresheafInjective (sheafificationUnit F) := by
  constructor
  · intro h U s t hst
    apply h U
    exact congrArg Subtype.val hst
  · intro h U s t hst
    apply h U
    apply Subtype.ext
    exact hst

/-- The induced map on sheafifications of a presheaf morphism. -/
noncomputable def sheafificationMap {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) :
    sheafificationPresheaf F ⟶ sheafificationPresheaf G :=
  sheafificationLift F (sheafification G) (φ ≫ sheafificationUnit G)

theorem sheafificationUnit_comp_map {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) :
    sheafificationUnit F ≫ sheafificationMap φ =
      φ ≫ sheafificationUnit G := by
  exact sheafificationUnit_comp_lift F (sheafification G)
    (φ ≫ sheafificationUnit G)

theorem sheafificationMap_id {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) :
    sheafificationMap (𝟙 F) = 𝟙 _ := by
  apply (existsUnique_sheafificationLift F (sheafification F)
    (𝟙 F ≫ sheafificationUnit F)).unique
  · exact sheafificationUnit_comp_map (𝟙 F)
  · simp

theorem sheafificationMap_comp {X : TopCat.{v}}
    {F G H : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) (ψ : G ⟶ H) :
    sheafificationMap (φ ≫ ψ) = sheafificationMap φ ≫ sheafificationMap ψ := by
  apply (existsUnique_sheafificationLift F (sheafification H)
    ((φ ≫ ψ) ≫ sheafificationUnit H)).unique
  · exact sheafificationUnit_comp_map (φ ≫ ψ)
  · rw [← Category.assoc, sheafificationUnit_comp_map φ, Category.assoc,
      sheafificationUnit_comp_map ψ]
    exact (Category.assoc φ ψ (sheafificationUnit H)).symm

/-- Sectionwise injectivity is preserved by sheafification. -/
theorem sheafificationMap_preserves_injective {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G)
    (hφ : PresheafInjective φ) :
    PresheafInjective (sheafificationMap φ) := by
  let f : sheafification F ⟶ sheafification G := ⟨sheafificationMap φ⟩
  change ∀ U, Function.Injective (f.hom.app (op U))
  apply (TopCat.Presheaf.app_injective_iff_stalkFunctor_map_injective f.hom).1
  intro x
  let uF := (TopCat.Presheaf.stalkFunctor (Type v) x).map (sheafificationUnit F)
  let m := (TopCat.Presheaf.stalkFunctor (Type v) x).map (sheafificationMap φ)
  let p := (TopCat.Presheaf.stalkFunctor (Type v) x).map φ
  let uG := (TopCat.Presheaf.stalkFunctor (Type v) x).map (sheafificationUnit G)
  have hF := sheafificationUnit_stalk_bijective F x
  have hG := sheafificationUnit_stalk_bijective G x
  have hp : Function.Injective p :=
    TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective hφ x
  have hcomp : uF ≫ m = p ≫ uG := by
    have h := congrArg
      (fun q => (TopCat.Presheaf.stalkFunctor (Type v) x).map q)
      (sheafificationUnit_comp_map φ)
    dsimp [uF, m, p, uG]
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  intro a b hab
  obtain ⟨a₀, ha₀⟩ := hF.2 a
  obtain ⟨b₀, hb₀⟩ := hF.2 b
  have hca := congrArg (fun q => q a₀) hcomp
  have hcb := congrArg (fun q => q b₀) hcomp
  change m (uF a₀) = uG (p a₀) at hca
  change m (uF b₀) = uG (p b₀) at hcb
  change uF a₀ = a at ha₀
  change uF b₀ = b at hb₀
  change m a = m b at hab
  have hstalk : uG (p a₀) = uG (p b₀) := by
    rw [← hca, ← hcb, ha₀, hb₀]
    exact hab
  have hpab : p a₀ = p b₀ := hG.1 hstalk
  have hab₀ : a₀ = b₀ := hp hpab
  calc
    a = uF a₀ := ha₀.symm
    _ = uF b₀ := congrArg (fun z => uF z) hab₀
    _ = b := hb₀

/-- Surjectivity in the sheaf sense (local sectionwise preimages) is
preserved by sheafification. -/
theorem sheafificationMap_preserves_surjective {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G)
    (hφ : PresheafSurjective φ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (sheafificationMap φ) := by
  let f : sheafification F ⟶ sheafification G := ⟨sheafificationMap φ⟩
  change TopCat.Presheaf.IsLocallySurjective f.hom
  apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks f.hom).2
  have hloc : TopCat.Presheaf.IsLocallySurjective φ := by
    apply (TopCat.Presheaf.isLocallySurjective_iff φ).2
    intro U t x hx
    obtain ⟨s, hs⟩ := hφ U t
    refine ⟨U, le_rfl, ⟨s, ?_⟩, hx⟩
    simpa using hs
  have hp_all :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ).1 hloc
  intro x
  let uF := (TopCat.Presheaf.stalkFunctor (Type v) x).map (sheafificationUnit F)
  let m := (TopCat.Presheaf.stalkFunctor (Type v) x).map (sheafificationMap φ)
  let p := (TopCat.Presheaf.stalkFunctor (Type v) x).map φ
  let uG := (TopCat.Presheaf.stalkFunctor (Type v) x).map (sheafificationUnit G)
  have hF := sheafificationUnit_stalk_bijective F x
  have hG := sheafificationUnit_stalk_bijective G x
  have hp : Function.Surjective p := by
    simpa [p] using hp_all x
  have hcomp : uF ≫ m = p ≫ uG := by
    have h := congrArg
      (fun q => (TopCat.Presheaf.stalkFunctor (Type v) x).map q)
      (sheafificationUnit_comp_map φ)
    dsimp [uF, m, p, uG]
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  intro b
  obtain ⟨c, hc⟩ := hG.2 b
  obtain ⟨a, ha⟩ := hp c
  refine ⟨uF a, ?_⟩
  have h := congrArg (fun q => q a) hcomp
  change m (uF a) = uG (p a) at h
  change m (uF a) = b
  have h' : uG (p a) = uG c :=
    congrArg (fun z => (ConcreteCategory.hom uG) z) ha
  exact h.trans (h'.trans hc)

end

end Formalization.Books.Sheaves.Unit17
