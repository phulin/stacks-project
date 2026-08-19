import Formalization.Books.Homology.Unit27.Injectives
import Formalization.Books.MoreAlgebra.Unit54.InjectiveAbelianGroups
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Injectives, Chapter 4: Abelian sheaves on a space

The source's construction is expressed with the canonical category of
`AddCommGrpCat`-valued sheaves.  The pointwise product sheaf and the
stalk/skyscraper adjunction are reused from the earlier Sheaves chapters.
The proposition-level injectivity arguments are theorem interfaces for the
prove stage; the object, product, and canonical map constructions have real
bodies here.
-/

namespace Formalization.Books.Injectives.Unit04

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Homology.Unit27
open ZeroObject

universe v

noncomputable section

/-! ## The canonical skyscraper interfaces -/

/-- The canonical functor sending an abelian group to its skyscraper sheaf.
The local classical choice packages Mathlib's decidability parameter. -/
noncomputable def abelianSkyscraperSheafFunctor {X : TopCat.{v}} (x : X) :
    AddCommGrpCat.{v} ⥤ TopCat.Sheaf AddCommGrpCat.{v} X := by
  classical
  exact skyscraperSheafFunctor x

/-- The stalk/skyscraper adjunction for abelian sheaves. -/
noncomputable def abelianStalkSkyscraperAdjunction {X : TopCat.{v}}
    (x : X) :
    (TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x) ⊣
      abelianSkyscraperSheafFunctor x := by
  letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  exact stalkSkyscraperSheafAdjunction x

/-- The categorical stalk of an abelian sheaf at a point. -/
abbrev abelianSheafStalk {X : TopCat.{v}}
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (x : X) : AddCommGrpCat.{v} :=
  (TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).obj F

/-! ## Injective envelopes of the stalks -/

/-- A chosen injective presentation of an abelian group.  This is the
canonical `EnoughInjectives.presentation` interface supplying the injective
object and monomorphism used in the pointwise construction. -/
noncomputable def abelianGroupInjectivePresentation (A : AddCommGrpCat.{v}) :
    InjectivePresentation A :=
  Classical.choice (EnoughInjectives.presentation A)

/-- The injective group `J(A)` chosen for an abelian group `A`. -/
noncomputable abbrev abelianGroupInjectiveObject (A : AddCommGrpCat.{v}) :
    AddCommGrpCat.{v} :=
  (abelianGroupInjectivePresentation A).J

/-- The canonical embedding `A ⟶ J(A)` associated to the chosen presentation. -/
noncomputable abbrev abelianGroupInjectiveMap (A : AddCommGrpCat.{v}) :
    A ⟶ abelianGroupInjectiveObject A :=
  (abelianGroupInjectivePresentation A).f

theorem abelianGroupInjectiveMap_mono (A : AddCommGrpCat.{v}) :
    Mono (abelianGroupInjectiveMap A) :=
  (abelianGroupInjectivePresentation A).mono

theorem abelianGroupInjectiveObject_injective (A : AddCommGrpCat.{v}) :
    Injective (abelianGroupInjectiveObject A) :=
  (abelianGroupInjectivePresentation A).injective

/-! ## The pointwise product sheaf -/

/-- The product of the fibres over the points of an open. -/
noncomputable def abelianSheafPointwiseProductObject {X : TopCat.{v}}
    (A : X → AddCommGrpCat.{v}) (U : Opens X) : AddCommGrpCat.{v} :=
  AddCommGrpCat.of (∀ x : U, A x)

/-- The presheaf whose sections over `U` are products of the fibres over the
points of `U`. -/
def abelianSheafPointwiseProductPresheaf {X : TopCat.{v}}
    (A : X → AddCommGrpCat.{v}) : TopCat.Presheaf AddCommGrpCat.{v} X where
  obj U := abelianSheafPointwiseProductObject A U.unop
  map {U V} f :=
    AddCommGrpCat.ofHom {
      toFun := fun s x => s (f.unop x)
      map_zero' := by
        ext x
        simp
      map_add' := by
        intro s t
        ext x
        simp }
  map_id U := by
    apply AddCommGrpCat.hom_ext
    ext s x
    rfl
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    ext s x
    rfl

/-- Restriction in the pointwise product presheaf is pointwise restriction. -/
@[simp]
theorem abelianSheafPointwiseProductPresheaf_restriction
    {X : TopCat.{v}} (A : X → AddCommGrpCat.{v})
    {U V : Opens X} (i : V ⟶ U) (s : ∀ x : U, A x) (x : V) :
    (abelianSheafPointwiseProductPresheaf A).map i.op s x =
    s (i x) :=
  rfl

/-- The pointwise product presheaf is a sheaf. -/
noncomputable def abelianSheafPointwiseProduct {X : TopCat.{v}}
    (A : X → AddCommGrpCat.{v}) :
    TopCat.Sheaf AddCommGrpCat.{v} X := by
  refine ⟨abelianSheafPointwiseProductPresheaf A, ?_⟩
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (CategoryTheory.forget AddCommGrpCat.{v})
    (abelianSheafPointwiseProductPresheaf A)).2
  change (TopCat.presheafToTypes X (fun x => A x)).IsSheaf
  exact TopCat.Presheaf.toTypes_isSheaf X (fun x => A x)

@[simp]
theorem abelianSheafPointwiseProduct_obj {X : TopCat.{v}}
    (A : X → AddCommGrpCat.{v}) (U : Opens X) :
    (abelianSheafPointwiseProduct A).presheaf.obj (op U) =
      abelianSheafPointwiseProductObject A U :=
  rfl

/-- The product of skyscraper sheaves with prescribed abelian-group fibres. -/
noncomputable def abelianSheafSkyscraperProduct {X : TopCat.{v}}
    (A : X → AddCommGrpCat.{v}) :
    TopCat.Sheaf AddCommGrpCat.{v} X :=
  limit (Discrete.functor (fun x : X =>
    (abelianSkyscraperSheafFunctor x).obj (A x)))

/- The source's fibrewise injective product, written as the product of the
   skyscraper sheaves `iₓ,* J(Fₓ)`. -/
noncomputable abbrev abelianSheafInjectiveProduct {X : TopCat.{v}}
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    TopCat.Sheaf AddCommGrpCat.{v} X :=
  abelianSheafSkyscraperProduct
    (fun x : X => abelianGroupInjectiveObject (abelianSheafStalk F x))

noncomputable def abelianSheafSkyscraperProduct_isProduct
    {X : TopCat.{v}} (A : X → AddCommGrpCat.{v}) :
    IsLimit (limit.cone (Discrete.functor (fun x : X =>
      (abelianSkyscraperSheafFunctor x).obj (A x)))) :=
  limit.isLimit _

/-- The product universal property of the source's injective product. -/
noncomputable def abelianSheafInjectiveProduct_isProduct
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    IsLimit (limit.cone (Discrete.functor (fun x : X =>
      (abelianSkyscraperSheafFunctor x).obj
        (abelianGroupInjectiveObject (abelianSheafStalk F x))))) :=
  abelianSheafSkyscraperProduct_isProduct
    (fun x : X => abelianGroupInjectiveObject (abelianSheafStalk F x))

/-- The pointwise description of the product of skyscraper sheaves. -/
theorem abelianSheafSkyscraperProduct_pointwise_formula
    {X : TopCat.{v}} (A : X → AddCommGrpCat.{v}) (U : Opens X) :
    Nonempty
      ((abelianSheafSkyscraperProduct A).presheaf.obj (op U) ≅
        abelianSheafPointwiseProductObject A U) := by
  classical
  let D : Discrete X ⥤ TopCat.Sheaf AddCommGrpCat.{v} X :=
    Discrete.functor (fun x : X => (abelianSkyscraperSheafFunctor x).obj (A x))
  let F : TopCat.Sheaf AddCommGrpCat.{v} X ⥤
      TopCat.Presheaf AddCommGrpCat.{v} X :=
    TopCat.Sheaf.forget AddCommGrpCat.{v} X
  let G : TopCat.Presheaf AddCommGrpCat.{v} X ⥤ AddCommGrpCat.{v} :=
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{v}).obj (op U)
  have hPreservesD : PreservesLimit D F :=
    preservesLimit_of_createsLimit_and_hasLimit D F
  have hPreservesDG : PreservesLimit (D ⋙ F) G :=
    evaluation_preservesLimit (D ⋙ F) (op U)
  have hF : IsLimit (F.mapCone (limit.cone D)) :=
    @isLimitOfPreserves _ _ _ _ _ _ _ F _ (limit.isLimit D) hPreservesD
  have hG : IsLimit (G.mapCone (F.mapCone (limit.cone D))) :=
    @isLimitOfPreserves _ _ _ _ _ _ _ G _ hF hPreservesDG
  let B : X → AddCommGrpCat.{v} :=
    fun x => G.obj (F.obj (D.obj (Discrete.mk x)))
  have hB (x : X) (hx : x ∈ U) : B x = A x := by
    change (if x ∈ U then A x else ⊤_ AddCommGrpCat) = A x
    rw [if_pos hx]
  have hB0 (x : X) (hx : ¬x ∈ U) : B x = ⊤_ AddCommGrpCat := by
    change (if x ∈ U then A x else ⊤_ AddCommGrpCat) = ⊤_ AddCommGrpCat
    rw [if_neg hx]
  let P : AddCommGrpCat.{v} := abelianSheafPointwiseProductObject A U
  let q (x : X) (hx : x ∈ U) : P ⟶ A x :=
    AddCommGrpCat.ofHom {
      toFun := fun s => s ⟨x, hx⟩
      map_zero' := by simp
      map_add' := by simp }
  let p (x : X) : P ⟶ B x :=
    if hx : x ∈ U then
      q x hx ≫ eqToHom (hB x hx).symm
    else
      terminal.from P ≫ eqToHom (hB0 x hx).symm
  let E : Discrete X ⥤ AddCommGrpCat.{v} := (D ⋙ F) ⋙ G
  let cU : Cone E :=
    { pt := P
      π :=
        { app := fun j => p j.as
          naturality := by
            intro U V i
            let e : U = V := Discrete.ext i.down.down
            have hf : i = eqToHom e := Subsingleton.elim _ _
            rw [hf]
            cases e
            simp [E, p] } }
  have hcU : IsLimit cU := by
    let l (s : Cone E) : s.pt ⟶ P :=
      AddCommGrpCat.ofHom {
        toFun := fun z x =>
          ConcreteCategory.hom
            (s.π.app (Discrete.mk x.1) ≫ eqToHom (hB x.1 x.2)) z
        map_zero' := by
          apply funext
          intro x
          simp
        map_add' := by
          intro a b
          apply funext
          intro x
          simp }
    refine { lift := fun s => l s, fac := ?_, uniq := ?_ }
    · rintro s ⟨j⟩
      by_cases hj : j ∈ U
      · let e : B j ≅ A j := eqToIso (hB j hj)
        apply (cancel_mono e.hom).1
        change (l s ≫ p j) ≫ e.hom =
          s.π.app (Discrete.mk j) ≫ e.hom
        simp [p, e, hj, Category.assoc]
        apply AddCommGrpCat.hom_ext
        ext z
        change ConcreteCategory.hom
            (s.π.app (Discrete.mk j) ≫ eqToHom (hB j hj)) z =
          ConcreteCategory.hom
            (s.π.app (Discrete.mk j) ≫ eqToHom (hB j hj)) z
        rfl
      · have hterm : IsTerminal (B j) :=
          IsTerminal.ofIso terminalIsTerminal (eqToIso (hB0 j hj).symm)
        exact hterm.hom_ext _ _
    · intro s m hm
      apply AddCommGrpCat.hom_ext
      ext z
      apply funext
      intro x
      have hx0 := congrArg
        (fun f : s.pt ⟶ B x.1 => f ≫ eqToHom (hB x.1 x.2))
        (hm (Discrete.mk x.1))
      have hx2 := hx0
      simp [cU, p, Category.assoc] at hx2
      have hx1 := congrArg
        (fun f : s.pt ⟶ A x.1 => ConcreteCategory.hom f z) hx2
      change (ConcreteCategory.hom m z) x =
        ConcreteCategory.hom (eqToHom (hB x.1 x.2))
          (ConcreteCategory.hom (s.π.app (Discrete.mk x.1)) z)
      exact hx1
  exact ⟨hG.conePointUniqueUpToIso hcU⟩

/-! The pointwise product sheaf is the product of the skyscraper sheaves. -/
theorem abelianSheafPointwiseProduct_skyscraperProduct_iso
    {X : TopCat.{v}} (A : X → AddCommGrpCat.{v}) :
    Nonempty (abelianSheafPointwiseProduct A ≅
      abelianSheafSkyscraperProduct A) := by
  classical
  let D₀ : Discrete X ⥤ TopCat.Sheaf AddCommGrpCat.{v} X :=
    Discrete.functor (fun x : X => (abelianSkyscraperSheafFunctor x).obj (A x))
  let F : TopCat.Sheaf AddCommGrpCat.{v} X ⥤
      TopCat.Presheaf AddCommGrpCat.{v} X :=
    TopCat.Sheaf.forget AddCommGrpCat.{v} X
  let D : Discrete X ⥤ TopCat.Presheaf AddCommGrpCat.{v} X := D₀ ⋙ F
  let P : TopCat.Presheaf AddCommGrpCat.{v} X :=
    abelianSheafPointwiseProductPresheaf A
  let B (x : X) (U : Opens X) : AddCommGrpCat.{v} :=
    (D.obj (Discrete.mk x)).obj (op U)
  have hB (x : X) (U : Opens X) (hx : x ∈ U) : B x U = A x := by
    change (if x ∈ U then A x else ⊤_ AddCommGrpCat) = A x
    rw [if_pos hx]
  have hB0 (x : X) (U : Opens X) (hx : ¬x ∈ U) :
      B x U = ⊤_ AddCommGrpCat := by
    change (if x ∈ U then A x else ⊤_ AddCommGrpCat) = ⊤_ AddCommGrpCat
    rw [if_neg hx]
  have hmapB (x : X) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
      (hxU : x ∈ U.unop) (hxV : x ∈ V.unop) :
      (D.obj (Discrete.mk x)).map i ≫ eqToHom (hB x V.unop hxV) =
        eqToHom (hB x U.unop hxU) := by
    have hUobj :
        (if h : x ∈ U.unop then A x else ⊤_ AddCommGrpCat) = A x := by
      change (D.obj (Discrete.mk x)).obj U = A x
      exact hB x U.unop hxU
    have hVobj :
        (if h : x ∈ V.unop then A x else ⊤_ AddCommGrpCat) = A x := by
      change (D.obj (Discrete.mk x)).obj V = A x
      exact hB x V.unop hxV
    have hh :
        (skyscraperPresheaf x (A x)).map i ≫ eqToHom hVobj =
          eqToHom hUobj := by
      dsimp [skyscraperPresheaf]
      rw [dif_pos hxV]
      simp only [eqToHom_trans]
    have hbase :
        (D.obj (Discrete.mk x)).map i ≫ eqToHom hVobj =
          eqToHom hUobj := by
      change (skyscraperPresheaf x (A x)).map i ≫ eqToHom hVobj =
        eqToHom hUobj
      exact hh
    have hVeq : hVobj = hB x V.unop hxV := Subsingleton.elim _ _
    have hUeq : hUobj = hB x U.unop hxU := Subsingleton.elim _ _
    rw [hVeq, hUeq] at hbase
    exact hbase
  let q (x : X) (U : (Opens X)ᵒᵖ) (hx : x ∈ U.unop) :
      P.obj U ⟶ A x :=
    AddCommGrpCat.ofHom {
      toFun := fun s => s ⟨x, hx⟩
      map_zero' := by simp
      map_add' := by simp }
  have hq (x : X) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
      (hxU : x ∈ U.unop) (hxV : x ∈ V.unop) :
      P.map i ≫ q x V hxV = q x U hxU := by
    apply AddCommGrpCat.hom_ext
    ext s
    dsimp [q, P, abelianSheafPointwiseProductPresheaf]
    change s (i.unop ⟨x, hxV⟩) = s ⟨x, hxU⟩
    congr 1
  let p (x : X) (U : (Opens X)ᵒᵖ) : P.obj U ⟶ B x U.unop :=
    if hx : x ∈ U.unop then
      q x U hx ≫ eqToHom (hB x U.unop hx).symm
    else
      terminal.from (P.obj U) ≫ eqToHom (hB0 x U.unop hx).symm
  let hpNat (x : X) : P ⟶ D.obj (Discrete.mk x) :=
    { app := fun U => p x U
      naturality := by
        intro U V i
        by_cases hxV : x ∈ V.unop
        · have hxU : x ∈ U.unop := i.unop.le hxV
          let eV : B x V.unop ≅ A x := eqToIso (hB x V.unop hxV)
          apply (cancel_mono eV.hom).1
          simp [p, hxU, hxV, eV, Category.assoc]
          rw [hmapB x i hxU hxV]
          rw [← hq x i hxU hxV]
          simp
        · have hterm : IsTerminal (B x V.unop) :=
              IsTerminal.ofIso terminalIsTerminal (eqToIso (hB0 x V.unop hxV).symm)
          exact hterm.hom_ext _ _ }
  let G : (Opens X)ᵒᵖ →
      (TopCat.Presheaf AddCommGrpCat.{v} X ⥤ AddCommGrpCat.{v}) :=
    fun U => (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{v}).obj U
  let E (U : (Opens X)ᵒᵖ) : Discrete X ⥤ AddCommGrpCat.{v} := D ⋙ G U
  let cP : Cone D :=
    { pt := P
      π :=
        { app := fun j => hpNat j.as
          naturality := by
            intro i j f
            let e : i = j := Discrete.ext f.down.down
            have hf : f = eqToHom e := Subsingleton.elim _ _
            rw [hf]
            cases e
            rfl } }
  let cU (U : (Opens X)ᵒᵖ) : Cone (E U) := (G U).mapCone cP
  have hcU (U : (Opens X)ᵒᵖ) : IsLimit (cU U) := by
    have hBE (x : X) (hx : x ∈ U.unop) :
        (E U).obj (Discrete.mk x) = A x := by
      change B x U.unop = A x
      exact hB x U.unop hx
    have hBE0 (x : X) (hx : ¬x ∈ U.unop) :
        (E U).obj (Discrete.mk x) = ⊤_ AddCommGrpCat := by
      change B x U.unop = ⊤_ AddCommGrpCat
      exact hB0 x U.unop hx
    let l (s : Cone (E U)) : s.pt ⟶ P.obj U :=
      AddCommGrpCat.ofHom {
        toFun := fun z y =>
          ConcreteCategory.hom
            (s.π.app (Discrete.mk y.1) ≫ eqToHom (hBE y.1 y.2)) z
        map_zero' := by
          apply funext
          intro y
          simp
        map_add' := by
          intro a b
          apply funext
          intro y
          simp }
    have hfac (s : Cone (E U)) (j : X) (hj : j ∈ U.unop) :
        (l s ≫ (cU U).π.app (Discrete.mk j)) ≫ eqToHom (hBE j hj) =
          s.π.app (Discrete.mk j) ≫ eqToHom (hBE j hj) := by
      dsimp [cU, G, cP, hpNat]
      simp only [p, dif_pos hj]
      have hEq : hB j U.unop hj = hBE j hj := Subsingleton.elim _ _
      rw [hEq]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      apply AddCommGrpCat.hom_ext
      ext z
      rfl
    refine { lift := fun s => l s, fac := ?_, uniq := ?_ }
    · rintro s ⟨j⟩
      by_cases hj : j ∈ U.unop
      · let e : (E U).obj (Discrete.mk j) ≅ A j := eqToIso (hBE j hj)
        apply (cancel_mono e.hom).1
        simpa [e] using hfac s j hj
      · have hterm : IsTerminal ((E U).obj (Discrete.mk j)) :=
          IsTerminal.ofIso terminalIsTerminal (eqToIso (hBE0 j hj).symm)
        exact hterm.hom_ext _ _
    · intro s m hm
      apply AddCommGrpCat.hom_ext
      ext z
      apply funext
      intro y
      have hy0 := congrArg
        (fun f : s.pt ⟶ (E U).obj (Discrete.mk y.1) =>
          f ≫ eqToHom (hBE y.1 y.2))
        (hm (Discrete.mk y.1))
      dsimp [cU, G, cP, hpNat] at hy0
      simp only [p, dif_pos y.2] at hy0
      have hEq : hB y.1 U.unop y.2 = hBE y.1 y.2 := Subsingleton.elim _ _
      rw [hEq] at hy0
      simp [Category.assoc] at hy0
      have hy2 := congrArg
        (fun f : s.pt ⟶ A y.1 => ConcreteCategory.hom f z) hy0
      change (ConcreteCategory.hom m z) y =
        ConcreteCategory.hom (eqToHom (hBE y.1 y.2))
          (ConcreteCategory.hom (s.π.app (Discrete.mk y.1)) z)
      change (ConcreteCategory.hom m z) y =
        ConcreteCategory.hom (eqToHom (hBE y.1 y.2))
          (ConcreteCategory.hom (s.π.app (Discrete.mk y.1)) z) at hy2
      exact hy2
  have hcP : IsLimit cP := by
    apply evaluationJointlyReflectsLimits cP
    intro U
    exact hcU U
  have hPreservesD₀ : PreservesLimit D₀ F :=
    preservesLimit_of_createsLimit_and_hasLimit D₀ F
  have hlim : IsLimit (F.mapCone (limit.cone D₀)) :=
    @isLimitOfPreserves _ _ _ _ _ _ _ F _ (limit.isLimit D₀) hPreservesD₀
  let ePresheaf : P ≅ F.obj (limit D₀) :=
    (hlim.conePointUniqueUpToIso hcP).symm
  exact ⟨ObjectProperty.isoMk (P := TopCat.Presheaf.IsSheaf) ePresheaf⟩

/-! The pointwise description of the selected injective product. -/
theorem abelianSheafInjectiveProduct_pointwise_formula
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X)
    (U : Opens X) :
    Nonempty
      ((abelianSheafInjectiveProduct F).presheaf.obj (op U) ≅
        abelianSheafPointwiseProductObject
          (fun x : X => abelianGroupInjectiveObject (abelianSheafStalk F x)) U) := by
  simpa [abelianSheafInjectiveProduct] using
    (abelianSheafSkyscraperProduct_pointwise_formula
      (fun x : X => abelianGroupInjectiveObject (abelianSheafStalk F x)) U)

/-! ## The canonical map into the product -/

/-- The map from a sheaf to the product of the skyscraper embeddings, with
component at `x` given by the unit of the stalk/skyscraper adjunction. -/
noncomputable def abelianSheafInjectiveEmbedding
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    F ⟶ abelianSheafInjectiveProduct F :=
  limit.lift
    (Discrete.functor (fun x : X =>
      (abelianSkyscraperSheafFunctor x).obj
        (abelianGroupInjectiveObject (abelianSheafStalk F x))))
    (Fan.mk F (fun x =>
      (abelianStalkSkyscraperAdjunction x).unit.app F ≫
        (abelianSkyscraperSheafFunctor x).map
          (abelianGroupInjectiveMap (abelianSheafStalk F x))))

theorem abelianSheafInjectiveEmbedding_projection
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X) (x : X) :
    abelianSheafInjectiveEmbedding F ≫
        limit.π (Discrete.functor (fun y : X =>
          (abelianSkyscraperSheafFunctor y).obj
            (abelianGroupInjectiveObject (abelianSheafStalk F y))))
          (Discrete.mk x) =
      (abelianStalkSkyscraperAdjunction x).unit.app F ≫
        (abelianSkyscraperSheafFunctor x).map
          (abelianGroupInjectiveMap (abelianSheafStalk F x)) := by
  unfold abelianSheafInjectiveEmbedding abelianSheafInjectiveProduct
    abelianSheafSkyscraperProduct
  rw [limit.lift_π]
  rfl

/-- The stalk/skyscraper Hom equivalence used to prove that each skyscraper
with injective fibre is injective. -/
noncomputable def abelianStalkSkyscraperHomEquiv
    {X : TopCat.{v}} (x : X) (F : TopCat.Sheaf AddCommGrpCat.{v} X)
    (I : AddCommGrpCat.{v}) :
    (abelianSheafStalk F x ⟶ I) ≃
      (F ⟶ (abelianSkyscraperSheafFunctor x).obj I) :=
  (abelianStalkSkyscraperAdjunction x).homEquiv F I

/-! ## Injectivity interfaces -/

/-- A skyscraper sheaf with injective stalk is injective. -/
theorem abelianSkyscraperSheaf_injective
    {X : TopCat.{v}} (x : X) (I : AddCommGrpCat.{v})
    (hI : Injective I) :
    Injective ((abelianSkyscraperSheafFunctor x).obj I) := by
  exact (abelianStalkSkyscraperAdjunction x).map_injective I hI

/-! The pointwise product of injective fibres is injective. -/
theorem abelianSheafPointwiseProduct_injective
    {X : TopCat.{v}} (A : X → AddCommGrpCat.{v})
    (hA : ∀ x : X, Injective (A x)) :
    Injective (abelianSheafPointwiseProduct A) := by
  rcases abelianSheafPointwiseProduct_skyscraperProduct_iso A with ⟨e⟩
  apply Injective.of_iso e.symm
  simpa [abelianSheafSkyscraperProduct] using
    (@product_injective
      (TopCat.Sheaf AddCommGrpCat.{v} X) _ _ X
      (fun x : X => (abelianSkyscraperSheafFunctor x).obj (A x)) _
      (fun x => abelianSkyscraperSheaf_injective x (A x) (hA x)))

/-! The product of skyscrapers with injective fibres is injective. -/
theorem abelianSheafSkyscraperProduct_injective
    {X : TopCat.{v}} (A : X → AddCommGrpCat.{v})
    (hA : ∀ x : X, Injective (A x)) :
    Injective (abelianSheafSkyscraperProduct A) := by
  have hSkyscraper : ∀ x : X, Injective
      ((abelianSkyscraperSheafFunctor x).obj (A x)) :=
    fun x => abelianSkyscraperSheaf_injective x (A x) (hA x)
  simpa [abelianSheafSkyscraperProduct] using
    (@product_injective
      (TopCat.Sheaf AddCommGrpCat.{v} X) _ _ X
      (fun x : X => (abelianSkyscraperSheafFunctor x).obj (A x)) _
      hSkyscraper)

/-- The product of the injective skyscraper sheaves is injective. -/
theorem abelianSheafInjectiveProduct_injective
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    Injective (abelianSheafInjectiveProduct F) := by
  apply abelianSheafSkyscraperProduct_injective
  intro x
  exact abelianGroupInjectiveObject_injective (abelianSheafStalk F x)

/-- The canonical map into the product is a monomorphism. -/
theorem abelianSheafInjectiveEmbedding_mono
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    Mono (abelianSheafInjectiveEmbedding F) := by
  rw [TopCat.Presheaf.mono_iff_stalk_mono]
  intro x
  let L := TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x
  let p : abelianSheafInjectiveProduct F ⟶
      (abelianSkyscraperSheafFunctor x).obj
        (abelianGroupInjectiveObject (abelianSheafStalk F x)) :=
    limit.π (Discrete.functor (fun y : X =>
      (abelianSkyscraperSheafFunctor y).obj
        (abelianGroupInjectiveObject (abelianSheafStalk F y)))) (Discrete.mk x)
  let j := abelianGroupInjectiveMap (abelianSheafStalk F x)
  let _ : Mono j := abelianGroupInjectiveMap_mono _
  apply mono_of_mono_fac (h := j)
  change L.map (abelianSheafInjectiveEmbedding F) ≫
    L.map p ≫ (abelianStalkSkyscraperAdjunction x).counit.app
      (abelianGroupInjectiveObject (abelianSheafStalk F x)) = j
  rw [← Category.assoc, ← L.map_comp,
    abelianSheafInjectiveEmbedding_projection]
  rw [Functor.map_comp, Category.assoc]
  change L.map ((abelianStalkSkyscraperAdjunction x).unit.app F) ≫
    (TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map
      ((abelianSkyscraperSheafFunctor x).map
        (abelianGroupInjectiveMap (abelianSheafStalk F x))) ≫
      (abelianStalkSkyscraperAdjunction x).counit.app
        (abelianGroupInjectiveObject (abelianSheafStalk F x)) = j
  have hnat := (abelianStalkSkyscraperAdjunction x).counit_naturality
    (abelianGroupInjectiveMap (abelianSheafStalk F x))
  rw [hnat]
  change
    ((TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map
        ((abelianStalkSkyscraperAdjunction x).unit.app F) ≫
      (abelianStalkSkyscraperAdjunction x).counit.app
        ((TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).obj F)) ≫ j = j
  simpa only [Category.id_comp] using
    congrArg (fun f => f ≫ j)
      ((abelianStalkSkyscraperAdjunction x).left_triangle_components F)

/-! ## Enough injectives -/

/-- Abelian sheaves on a topological space have enough injectives. -/
theorem abelian_sheaves_have_enough_injectives {X : TopCat.{v}} :
    EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{v} X) := by
  refine ⟨?_⟩
  intro F
  refine ⟨abelianSheafInjectiveProduct F,
    abelianSheafInjectiveProduct_injective F,
    abelianSheafInjectiveEmbedding F,
    abelianSheafInjectiveEmbedding_mono F⟩

/-- Abelian sheaves on a topological space have functorial injective
embeddings. -/
theorem abelian_sheaves_have_functorial_injective_embeddings
    {X : TopCat.{v}} :
    HasFunctorialInjectiveEmbeddings
      (C := TopCat.Sheaf AddCommGrpCat.{v} X) := by
  let d := MorphismProperty.functorialFactorizationData
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{v} X))
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{v} X)).rlp
  let z : TopCat.Sheaf AddCommGrpCat.{v} X ⥤
      Arrow (TopCat.Sheaf AddCommGrpCat.{v} X) :=
    { obj M := Arrow.mk (0 : M ⟶ (0 : TopCat.Sheaf AddCommGrpCat.{v} X))
      map {M N} f :=
        Arrow.homMk f (𝟙 (0 : TopCat.Sheaf AddCommGrpCat.{v} X)) (by simp)
      map_id M := by
        apply Arrow.hom_ext <;> simp
      map_comp f g := by
        apply Arrow.hom_ext <;> simp }
  let J : TopCat.Sheaf AddCommGrpCat.{v} X ⥤
      Arrow (TopCat.Sheaf AddCommGrpCat.{v} X) :=
    { obj M := Arrow.mk (d.i.app (z.obj M))
      map {M N} f :=
        Arrow.homMk f (d.Z.map (z.map f)) (d.i.naturality (z.map f))
      map_id M := by
        apply Arrow.hom_ext
        · change (𝟙 M) = 𝟙 M
          rfl
        · change d.Z.map (z.map (𝟙 M)) = 𝟙 _
          rw [z.map_id, d.Z.map_id]
      map_comp f g := by
        apply Arrow.hom_ext
        · change f ≫ g = f ≫ g
          rfl
        · change d.Z.map (z.map (f ≫ g)) =
            d.Z.map (z.map f) ≫ d.Z.map (z.map g)
          rw [z.map_comp, d.Z.map_comp] }
  have hJleft : J ⋙ Arrow.leftFunc =
      𝟭 (TopCat.Sheaf AddCommGrpCat.{v} X) := by
    apply CategoryTheory.Functor.hext
    · intro M
      rfl
    · intro M N f
      rfl
  have hJmono : ∀ M : TopCat.Sheaf AddCommGrpCat.{v} X, Mono (J.obj M).hom := by
    intro M
    change Mono (d.i.app (z.obj M))
    exact d.hi _
  have hJinjective : ∀ M : TopCat.Sheaf AddCommGrpCat.{v} X,
      Injective (J.obj M).right := by
    intro M
    change Injective (d.Z.obj (z.obj M))
    change Injective
      (IsGrothendieckAbelian.monoMapFactorizationDataRlp
        (C := TopCat.Sheaf AddCommGrpCat.{v} X)
        (0 : M ⟶ (0 : TopCat.Sheaf AddCommGrpCat.{v} X))).Z
    infer_instance
  exact ⟨J, hJleft, hJmono, hJinjective⟩

end

end Formalization.Books.Injectives.Unit04
