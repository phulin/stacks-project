import Formalization.Books.Categories.Unit03.Opposite
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Hypercoverings, Chapter 2: Semi-representable objects

The source section is formalized with Mathlib's `FormalCoproduct` category.  Its
objects are indexed families of objects of a category and its morphisms are
exactly a function on indices together with one morphism in the original
category over each index.  The source's unbounded ``big'' category is recorded
by the universe-polymorphic abbreviation `SemiRepresentable`; the concrete
functors in this file use the hom-set universe of the base category.
-/

namespace Formalization.Books.Hypercovering.Unit02

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit03
open Opposite

universe w v u

noncomputable section

/-! ## Definition of semi-representable objects -/

/-- The category of semi-representable objects with `w`-small index families.

This is Mathlib's canonical `FormalCoproduct` category; in particular, its
`Hom` structure is the source's pair consisting of an index map and component
morphisms. -/
abbrev SemiRepresentable (C : Type u) [Category.{v} C] :=
  FormalCoproduct.{w} C

/-- The semi-representable objects over `X`, namely semi-representable objects
in the slice category `C/X`. -/
abbrev SemiRepresentableOver (C : Type u) [Category.{v} C] (X : C) :=
  SemiRepresentable.{v} (Over X)

/-- The presheaf category over the representable presheaf `h_X`. -/
abbrev PresheafOver (C : Type u) [Category.{v} C] (X : C) :=
  Over (representablePresheaf X)

/-! ## The forgetful functor on objects over `X` -/

/-- Forget the maps to `X` from a semi-representable object over `X`. -/
def semiRepresentableOverForget {C : Type u} [Category.{v} C] (X : C) :
    SemiRepresentableOver C X ⥤ SemiRepresentable.{v} C where
  obj K :=
    { I := K.I
      obj := fun i => (K.obj i).left }
  map {K L} f :=
    { f := f.f
      φ := fun i => (f.φ i).left }
  map_id K := by
    exact FormalCoproduct.hom_ext rfl (fun i => by simp)
  map_comp f g := by
    exact FormalCoproduct.hom_ext rfl (fun i => by simp)

/-! ## The functor to presheaves -/

/-- The functor associating to a semi-representable object the coproduct of
the corresponding representable presheaves. -/
abbrev semiRepresentablePresheafFunctor {C : Type u} [Category.{v} C] :
    SemiRepresentable.{v} C ⥤ Presheaf C :=
  FormalCoproduct.yoneda

/- The displayed formula in the source is definitional for the canonical
`FormalCoproduct.yoneda` construction. -/
@[simp]
theorem semiRepresentablePresheafFunctor_obj
    {C : Type u} [Category.{v} C] (K : SemiRepresentable.{v} C) :
    (semiRepresentablePresheafFunctor (C := C)).obj K =
      ∐ fun i : K.I => representablePresheaf (K.obj i) :=
  rfl

/-! ## The functor over `h_X` -/

/-- The map of representable presheaves induced by an object of `C/X`. -/
def representablePresheafMapOfOver {C : Type u} [Category.{v} C]
    {X : C} (U : Over X) :
    representablePresheaf U.left ⟶ representablePresheaf X :=
  (functorOfPoints (C := C)).map U.hom

/-- The underlying presheaf of a semi-representable object over `X`. -/
abbrev semiRepresentableOverUnderlying {C : Type u} [Category.{v} C]
    (X : C) :
    SemiRepresentableOver C X ⥤ Presheaf C :=
  semiRepresentableOverForget X ⋙ semiRepresentablePresheafFunctor

/-- The canonical map from the underlying presheaf of a family over `X` to
`h_X`, assembled from the maps of its representable summands. -/
def semiRepresentableOverStructureMap {C : Type u} [Category.{v} C]
    (X : C) (K : SemiRepresentableOver C X) :
    (semiRepresentableOverUnderlying X).obj K ⟶ representablePresheaf X :=
  Sigma.desc fun i => representablePresheafMapOfOver (K.obj i)

@[simp]
theorem semiRepresentableOverStructureMap_ι
    {C : Type u} [Category.{v} C] {X : C}
    (K : SemiRepresentableOver C X) (i : K.I) :
    Sigma.ι (fun i : K.I => representablePresheaf (K.obj i).left) i ≫
        semiRepresentableOverStructureMap X K =
      representablePresheafMapOfOver (K.obj i) := by
  exact Sigma.ι_desc _ _

/-- The functor from semi-representable objects over `X` to presheaves over
`h_X`.  The target `Over (h_X)` is the source's
`PSh(C)/h_X`. -/
def semiRepresentableOverPresheafFunctor {C : Type u} [Category.{v} C]
    (X : C) :
    SemiRepresentableOver C X ⥤ PresheafOver C X :=
  Functor.toOver (semiRepresentableOverUnderlying X) (representablePresheaf X)
    (fun K => semiRepresentableOverStructureMap X K) (by
      intro K L f
      refine Sigma.hom_ext _ _ (fun i => ?_)
      change K.I at i
      change
        (Sigma.ι (fun j : K.I => representablePresheaf (K.obj j).left) i ≫
            (Sigma.desc fun j : K.I =>
              (functorOfPoints (C := C)).map (f.φ j).left ≫
                Sigma.ι (fun j : L.I => representablePresheaf (L.obj j).left) (f.f j)) ≫
              Sigma.desc (fun j : L.I => representablePresheafMapOfOver (L.obj j))) =
          Sigma.ι (fun j : K.I => representablePresheaf (K.obj j).left) i ≫
            Sigma.desc (fun j : K.I => representablePresheafMapOfOver (K.obj j))
      simp only [Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
      simpa only [representablePresheafMapOfOver, Functor.map_comp] using
        congrArg (fun h => (functorOfPoints (C := C)).map h) (f.φ i).w)

/- The upper-left-to-lower-left part of the source's square is recovered by
forgetting the target map in the slice. -/
@[simp]
theorem semiRepresentableOverPresheafFunctor_forget
    {C : Type u} [Category.{v} C] {X : C} :
    semiRepresentableOverPresheafFunctor X ⋙
        (Over.forget (representablePresheaf X) :
          PresheafOver C X ⥤ Presheaf C) =
      semiRepresentableOverUnderlying X :=
  rfl

/-! ## Limits and colimits -/

/-- `SR(C)` has the coproducts represented by disjoint unions of families. -/
theorem semiRepresentable_has_coproducts
    {C : Type u} [Category.{v} C] :
    HasCoproducts.{v} (SemiRepresentable.{v} C) := by
  infer_instance

/-- The functor to presheaves commutes with coproducts. -/
theorem semiRepresentablePresheafFunctor_preserves_coproducts
    {C : Type u} [Category.{v} C] (J : Type v) :
    PreservesColimitsOfShape (Discrete J)
      (semiRepresentablePresheafFunctor (C := C)) := by
  infer_instance

@[simp]
private theorem semiRepresentablePresheafFunctor_map_ι
    {C : Type u} [Category.{v} C] {K L : SemiRepresentable.{v} C}
    (f : K ⟶ L) (i : K.I) :
    Sigma.ι (fun j : K.I => representablePresheaf (K.obj j)) i ≫
        (semiRepresentablePresheafFunctor (C := C)).map f =
      yoneda.map (f.φ i) ≫
        Sigma.ι (fun j : L.I => representablePresheaf (L.obj j)) (f.f i) := by
  simp [semiRepresentablePresheafFunctor, FormalCoproduct.yoneda,
    FormalCoproduct.eval, Function.comp_def]

/-- The functor to presheaves commutes with all limits which exist. -/
theorem semiRepresentablePresheafFunctor_preserves_limits
    {C : Type u} [Category.{v} C] :
    PreservesLimits (semiRepresentablePresheafFunctor (C := C)) := by
  refine ⟨fun {J} _ => ?_⟩
  refine ⟨fun {K} => ?_⟩
  apply preservesLimit_of_evaluation (semiRepresentablePresheafFunctor (C := C)) K
  intro U
  let e :
      (semiRepresentablePresheafFunctor (C := C) ⋙
          (evaluation (Cᵒᵖ) (Type v)).obj U) ≅
        (coyoneda.obj (op ((FormalCoproduct.incl C).obj U.unop))) :=
    NatIso.ofComponents (fun K =>
      (sigmaObjIso (fun i : K.I => representablePresheaf (K.obj i)) U) ≪≫
        (Types.coproductIso (fun i : K.I =>
          (representablePresheaf (K.obj i)).obj U)) ≪≫
          Equiv.toIso (FormalCoproduct.inclHomEquiv U.unop K).symm) (by
        intro K L f
        let qK :
            (semiRepresentablePresheafFunctor (C := C) ⋙
                (evaluation (Cᵒᵖ) (Type v)).obj U).obj K ≅
              (Σ i : K.I, U.unop ⟶ K.obj i) :=
          sigmaObjIso (fun i : K.I => representablePresheaf (K.obj i)) U ≪≫
            Types.coproductIso (fun i : K.I =>
              (representablePresheaf (K.obj i)).obj U)
        let qL :
            (semiRepresentablePresheafFunctor (C := C) ⋙
                (evaluation (Cᵒᵖ) (Type v)).obj U).obj L ≅
              (Σ i : L.I, U.unop ⟶ L.obj i) :=
          sigmaObjIso (fun i : L.I => representablePresheaf (L.obj i)) U ≪≫
          Types.coproductIso (fun i : L.I =>
              (representablePresheaf (L.obj i)).obj U)
        have hq :
            ∀ (i : K.I) (x : U.unop ⟶ K.obj i),
              qL.hom ((semiRepresentablePresheafFunctor (C := C) ⋙
                (evaluation (Cᵒᵖ) (Type v)).obj U).map f (qK.inv ⟨i, x⟩)) =
                ⟨f.f i, x ≫ f.φ i⟩ := by
          intro i x
          have hK :
              (↾ fun y : U.unop ⟶ K.obj i => ⟨i, y⟩) ≫ qK.inv =
                (Sigma.ι (fun i : K.I => representablePresheaf (K.obj i)) i).app U := by
            dsimp [qK]
            rw [← Category.assoc,
              Types.coproductIso_mk_comp_inv
                (fun i : K.I => (representablePresheaf (K.obj i)).obj U) i,
              ι_comp_sigmaObjIso_inv]
          have hF :
              (Sigma.ι (fun i : K.I => representablePresheaf (K.obj i)) i).app U ≫
                  ((evaluation (Cᵒᵖ) (Type v)).obj U).map
                    (semiRepresentablePresheafFunctor.map f) =
                (yoneda.map (f.φ i)).app U ≫
                  (Sigma.ι (fun i : L.I => representablePresheaf (L.obj i)) (f.f i)).app U := by
            change
              (Sigma.ι (fun i : K.I => representablePresheaf (K.obj i)) i).app U ≫
                  (Sigma.desc (fun i =>
                    yoneda.map (f.φ i) ≫
                      Sigma.ι (fun i : L.I => representablePresheaf (L.obj i)) (f.f i))).app U =
                _
            simp only [← NatTrans.comp_app, Sigma.ι_desc]
          have hL :
              (Sigma.ι (fun i : L.I => representablePresheaf (L.obj i)) (f.f i)).app U ≫
                  qL.hom =
                (↾ fun y : U.unop ⟶ L.obj (f.f i) => ⟨f.f i, y⟩) := by
            dsimp [qL]
            rw [ι_comp_sigmaObjIso_hom_assoc,
              Types.coproductIso_ι_comp_hom
                (fun i : L.I => (representablePresheaf (L.obj i)).obj U) (f.f i)]
          have hcomp :
              ((↾ fun y : U.unop ⟶ K.obj i => ⟨i, y⟩) ≫ qK.inv) ≫
                  (((evaluation (Cᵒᵖ) (Type v)).obj U).map
                    (semiRepresentablePresheafFunctor.map f) ≫ qL.hom) =
                (↾ fun y : U.unop ⟶ K.obj i => ⟨f.f i, y ≫ f.φ i⟩) := by
            calc
              _ = (Sigma.ι (fun i : K.I => representablePresheaf (K.obj i)) i).app U ≫
                    (((evaluation (Cᵒᵖ) (Type v)).obj U).map
                      (semiRepresentablePresheafFunctor.map f) ≫ qL.hom) := by rw [hK]; rfl
              _ = ((Sigma.ι (fun i : K.I => representablePresheaf (K.obj i)) i).app U ≫
                    ((evaluation (Cᵒᵖ) (Type v)).obj U).map
                      (semiRepresentablePresheafFunctor.map f)) ≫ qL.hom :=
                (Category.assoc _ _ _).symm
              _ = ((yoneda.map (f.φ i)).app U ≫
                    (Sigma.ι (fun i : L.I => representablePresheaf (L.obj i)) (f.f i)).app U) ≫
                    qL.hom := by rw [hF]; rfl
              _ = (yoneda.map (f.φ i)).app U ≫
                    ((Sigma.ι (fun i : L.I => representablePresheaf (L.obj i)) (f.f i)).app U ≫
                      qL.hom) := Category.assoc _ _ _
              _ = (↾ fun y : U.unop ⟶ K.obj i => ⟨f.f i, y ≫ f.φ i⟩) := by
                rw [hL]
                rfl
          change qL.hom (((evaluation (Cᵒᵖ) (Type v)).obj U).map
            (semiRepresentablePresheafFunctor.map f) (qK.inv ⟨i, x⟩)) = _
          exact congrArg (fun g => g x) hcomp
        change
          (semiRepresentablePresheafFunctor (C := C) ⋙
              (evaluation (Cᵒᵖ) (Type v)).obj U).map f ≫ qL.hom ≫
              (FormalCoproduct.inclHomEquiv U.unop L).symm.toIso.hom =
            qK.hom ≫ (FormalCoproduct.inclHomEquiv U.unop K).symm.toIso.hom ≫
              (coyoneda.obj (op ((FormalCoproduct.incl C).obj U.unop))).map f
        rw [← cancel_epi qK.inv]
        ext x
        rcases x with ⟨i, x⟩
        · let a := qL.hom ((semiRepresentablePresheafFunctor (C := C) ⋙
              (evaluation (Cᵒᵖ) (Type v)).obj U).map f (qK.inv ⟨i, x⟩))
          let b := qK.hom (qK.inv ⟨i, x⟩)
          change
            ((FormalCoproduct.inclHomEquiv U.unop L).symm a).f _ =
              f.f (((FormalCoproduct.inclHomEquiv U.unop K).symm b).f _)
          have hb : b = ⟨i, x⟩ := by
            change qK.hom (qK.inv ⟨i, x⟩) = ⟨i, x⟩
            exact congrArg (fun g => g ⟨i, x⟩) qK.inv_hom_id
          have ha : a = ⟨f.f i, x ≫ f.φ i⟩ := by
            change qL.hom (((evaluation (Cᵒᵖ) (Type v)).obj U).map
              (semiRepresentablePresheafFunctor.map f) (qK.inv ⟨i, x⟩)) = _
            exact hq i x
          rw [ha, hb]
          rfl
        · rcases x with ⟨i, x⟩
          rename_i j
          let a := qL.hom ((semiRepresentablePresheafFunctor (C := C) ⋙
            (evaluation (Cᵒᵖ) (Type v)).obj U).map f (qK.inv ⟨i, x⟩))
          let b := qK.hom (qK.inv ⟨i, x⟩)
          have ha : a = ⟨f.f i, x ≫ f.φ i⟩ := by
            change qL.hom (((evaluation (Cᵒᵖ) (Type v)).obj U).map
              (semiRepresentablePresheafFunctor.map f) (qK.inv ⟨i, x⟩)) = _
            exact hq i x
          have hb :
              b = ⟨i, x⟩ := by
            change qK.hom (qK.inv ⟨i, x⟩) = ⟨i, x⟩
            exact congrArg (fun g => g ⟨i, x⟩) qK.inv_hom_id
          have hhom :
              (FormalCoproduct.inclHomEquiv U.unop L).symm
                  a =
                (FormalCoproduct.inclHomEquiv U.unop K).symm
                    b ≫ f := by
            rw [ha, hb]
            rfl
          exact (FormalCoproduct.hom_ext_iff _ _).1 hhom |>.2 j
        )
  exact preservesLimit_of_natIso K e.symm

/-- Fibre products in `C` induce fibre products in `SR(C)`. -/
theorem semiRepresentable_has_fibre_products
    {C : Type u} [Category.{v} C] [HasPullbacks C] :
    HasPullbacks (SemiRepresentable.{v} C) := by
  infer_instance

/-- Products of pairs in `C` induce products of pairs in `SR(C)`. -/
theorem semiRepresentable_has_binary_products
    {C : Type u} [Category.{v} C] [HasBinaryProducts C] :
    HasBinaryProducts (SemiRepresentable.{v} C) := by
  let _ : ∀ {X Y : SemiRepresentable.{v} C}, HasLimit (pair X Y) := by
    intro X Y
    let P : SemiRepresentable.{v} C :=
      { I := X.I × Y.I
        obj := fun i => X.obj i.1 ⨯ Y.obj i.2 }
    let p : P ⟶ X :=
      { f := Prod.fst
        φ := fun i => prod.fst }
    let q : P ⟶ Y :=
      { f := Prod.snd
        φ := fun i => prod.snd }
    let s : BinaryFan X Y := BinaryFan.mk p q
    refine ⟨⟨s, ?_⟩⟩
    refine BinaryFan.IsLimit.mk s
      (fun {T} f g =>
        { f := fun i => (f.f i, g.f i)
          φ := fun i => prod.lift (f.φ i) (g.φ i) }) ?_ ?_ ?_
    · intro T f g
      refine FormalCoproduct.hom_ext ?_ ?_
      · funext i
        rfl
      · intro i
        simpa [s, p] using (prod.lift_fst (f.φ i) (g.φ i))
    · intro T f g
      refine FormalCoproduct.hom_ext ?_ ?_
      · funext i
        rfl
      · intro i
        simpa [s, q] using (prod.lift_snd (f.φ i) (g.φ i))
    · intro T f g m h₁ h₂
      have prod_fst_eqToHom :
          ∀ {A A' B B' : C} (hA : A = A') (hB : B = B'),
            eqToHom (by rw [hA, hB] : (A ⨯ B : C) = (A' ⨯ B' : C)) ≫
                (prod.fst : (A' ⨯ B' : C) ⟶ A') =
              (prod.fst : (A ⨯ B : C) ⟶ A) ≫ eqToHom hA := by
        intro A A' B B' hA hB
        subst A'
        subst B'
        simp
      have prod_snd_eqToHom :
          ∀ {A A' B B' : C} (hA : A = A') (hB : B = B'),
            eqToHom (by rw [hA, hB] : (A ⨯ B : C) = (A' ⨯ B' : C)) ≫
                (prod.snd : (A' ⨯ B' : C) ⟶ B') =
              (prod.snd : (A ⨯ B : C) ⟶ B) ≫ eqToHom hB := by
        intro A A' B B' hA hB
        subst A'
        subst B'
        simp
      refine FormalCoproduct.hom_ext ?_ ?_
      · funext i
        apply Prod.ext
        · simpa [s, p, Function.comp_def] using
            congrFun (congrArg (fun h => h.f) h₁) i
        · simpa [s, q, Function.comp_def] using
            congrFun (congrArg (fun h => h.f) h₂) i
      · intro i
        apply prod.hom_ext
        · have h := (FormalCoproduct.hom_ext_iff' (m ≫ s.fst) f).1 h₁ i
          simp [s, p] at h
          have h' := (FormalCoproduct.hom_ext_iff' (m ≫ s.snd) g).1 h₂ i
          simp [s, q] at h'
          rcases h with ⟨h₁i, h₁φ⟩
          rcases h' with ⟨h₂i, h₂φ⟩
          rw [prod.lift_fst]
          rw [Category.assoc,
            prod_fst_eqToHom (congrArg X.obj h₁i) (congrArg Y.obj h₂i)]
          simpa [Category.assoc] using h₁φ
        · have h := (FormalCoproduct.hom_ext_iff' (m ≫ s.fst) f).1 h₁ i
          simp [s, p] at h
          have h' := (FormalCoproduct.hom_ext_iff' (m ≫ s.snd) g).1 h₂ i
          simp [s, q] at h'
          rcases h with ⟨h₁i, h₁φ⟩
          rcases h' with ⟨h₂i, h₂φ⟩
          rw [prod.lift_snd]
          rw [Category.assoc,
            prod_snd_eqToHom (congrArg X.obj h₁i) (congrArg Y.obj h₂i)]
          simpa [Category.assoc] using h₂φ
  exact hasBinaryProducts_of_hasLimit_pair _

/-- Equalizers in `C` induce equalizers in `SR(C)`. -/
theorem semiRepresentable_has_equalizers
    {C : Type u} [Category.{v} C] [HasEqualizers C] :
    HasEqualizers (SemiRepresentable.{v} C) := by
  let _ : ∀ {X Y : SemiRepresentable.{v} C} {f g : X ⟶ Y},
      HasLimit (parallelPair f g) := by
    intro X Y f g
    let E : SemiRepresentable.{v} C :=
      { I := {i : X.I // f.f i = g.f i}
        obj := fun i =>
          equalizer (f.φ i.1)
            (g.φ i.1 ≫ eqToHom (congrArg Y.obj i.2).symm) }
    let e : E ⟶ X :=
      { f := fun i => i.1
        φ := fun i => equalizer.ι (f.φ i.1)
          (g.φ i.1 ≫ eqToHom (congrArg Y.obj i.2).symm) }
    have he : e ≫ f = e ≫ g := by
      apply (FormalCoproduct.hom_ext_iff' (e ≫ f) (e ≫ g)).2
      intro i
      refine ⟨i.2, ?_⟩
      dsimp [e]
      rw [equalizer.condition (f.φ i.1)
          (g.φ i.1 ≫ eqToHom (congrArg Y.obj i.2).symm)]
      simp [Category.assoc]
    let s : Fork f g := Fork.ofι e he
    let j : ∀ t : Fork f g, t.pt.I → E.I := fun t i =>
      ⟨t.ι.f i, by
        have h := congrArg (fun k => k.f i) t.condition
        simpa using h⟩
    let lift : ∀ t : Fork f g, t.pt ⟶ E := fun t =>
      { f := j t
        φ := fun i => equalizer.lift (t.ι.φ i) (by
          have h :=
            (FormalCoproduct.hom_ext_iff' (t.ι ≫ f) (t.ι ≫ g)).1
              t.condition i
          rcases h with ⟨hidx, hφ⟩
          have hφ' :
              (t.ι.φ i ≫ f.φ (t.ι.f i)) ≫
                  eqToHom (congrArg Y.obj hidx) =
                t.ι.φ i ≫ g.φ (t.ι.f i) := by
            simpa using hφ
          dsimp [j]
          rw [← Category.assoc, ← hφ']
          simp) }
    refine ⟨⟨s, ?_⟩⟩
    refine Fork.IsLimit.mk s (fun t => lift t) ?_ ?_
    · intro t
      apply (FormalCoproduct.hom_ext_iff' (lift t ≫ e) t.ι).2
      intro i
      refine ⟨rfl, ?_⟩
      simp [lift, e, j]
    · intro t m hm
      apply (FormalCoproduct.hom_ext_iff' m (lift t)).2
      intro i
      have hfac : lift t ≫ e = t.ι := by
        apply (FormalCoproduct.hom_ext_iff' (lift t ≫ e) t.ι).2
        intro k
        refine ⟨rfl, ?_⟩
        simp [lift, e, j]
      have hme : m ≫ e = lift t ≫ e := by
        have hm' : m ≫ e = t.ι := by simpa [s] using hm
        exact hm'.trans hfac.symm
      have h :=
        (FormalCoproduct.hom_ext_iff' (m ≫ e) (lift t ≫ e)).1 hme i
      rcases h with ⟨hidx, hφ⟩
      have hmf : m.f i = (lift t).f i := by
        apply Subtype.ext
        simpa [e, lift, j] using hidx
      refine ⟨hmf, ?_⟩
      have e_naturality :
          ∀ {a b : E.I} (h : a = b),
            eqToHom (congrArg E.obj h) ≫ e.φ b =
              e.φ a ≫ eqToHom (congrArg X.obj (congrArg Subtype.val h)) := by
        intro a b h
        subst b
        simp
      apply equalizer.hom_ext
      rw [Category.assoc, e_naturality hmf]
      simpa [e, lift, j, Category.assoc] using hφ
  exact hasEqualizers_of_hasLimit_parallelPair _

/-- A final object of `C` gives a final semi-representable object. -/
theorem semiRepresentable_has_terminal
    {C : Type u} [Category.{v} C] [HasTerminal C] :
    HasTerminal (SemiRepresentable.{v} C) := by
  infer_instance

/-- `SR(C/X)` has coproducts. -/
theorem semiRepresentableOver_has_coproducts
    {C : Type u} [Category.{v} C] (X : C) :
    HasCoproducts.{v} (SemiRepresentableOver C X) := by
  infer_instance

/-- The functor from `SR(C/X)` to `PSh(C)/h_X` commutes with coproducts. -/
theorem semiRepresentableOverPresheafFunctor_preserves_coproducts
    {C : Type u} [Category.{v} C] (X : C) (J : Type v) :
    PreservesColimitsOfShape (Discrete J)
      (semiRepresentableOverPresheafFunctor X) := by
  letI : ∀ (K : J → SemiRepresentableOver C X),
      PreservesColimit (Discrete.functor K)
        (semiRepresentableOverForget X) := by
    intro K
    refine ⟨fun hc => ⟨?_⟩⟩
    let F := semiRepresentableOverForget X
    let A : SemiRepresentable.{v} C :=
      { I := Σ j : J, (K j).I
        obj := fun i => (F.obj (K i.1)).obj i.2 }
    let c : Cocone (Discrete.functor K ⋙ F) :=
      Cocone.mk A
        (Discrete.natTrans (fun j : Discrete J =>
          (FormalCoproduct.cofan J (fun j => F.obj (K j))).inj j.as))
    have hstd : IsColimit c := by
      let desc : ∀ s : Cocone (Discrete.functor K ⋙ F),
          c.pt ⟶ s.pt := fun s =>
        { f := fun i => (s.ι.app ⟨i.1⟩).f i.2
          φ := fun i => (s.ι.app ⟨i.1⟩).φ i.2 }
      refine { desc := desc, fac := ?_, uniq := ?_ }
      · intro s j
        rcases j with ⟨j⟩
        refine FormalCoproduct.hom_ext (h₁ := ?_) (h₂ := ?_)
        · funext i
          rfl
        · intro i
          dsimp [c, desc, FormalCoproduct.cofan, Discrete.natTrans]
          change (𝟙 _ ≫ (s.ι.app ⟨j⟩).φ i) ≫ eqToHom _ = _
          simp
      · intro s m h
        have hm_f : m.f = (desc s).f := by
          funext i
          dsimp [c, A] at i
          rcases i with ⟨j, i⟩
          have hi :=
            (FormalCoproduct.hom_ext_iff'
              (c.ι.app ⟨j⟩ ≫ m) (s.ι.app ⟨j⟩)).1
              (h ⟨j⟩) i
          rcases hi with ⟨hidx, hφ⟩
          change m.f ⟨j, i⟩ = (s.ι.app ⟨j⟩).f i at hidx
          exact hidx
        apply FormalCoproduct.hom_ext hm_f
        intro i
        dsimp [c, A] at i
        rcases i with ⟨j, i⟩
        have hi :=
          (FormalCoproduct.hom_ext_iff'
            (c.ι.app ⟨j⟩ ≫ m) (s.ι.app ⟨j⟩)).1
            (h ⟨j⟩) i
        rcases hi with ⟨hidx, hφ⟩
        dsimp [c, A, FormalCoproduct.cofan, Discrete.natTrans,
          FormalCoproduct.category] at hφ
        change (𝟙 _ ≫ m.φ ⟨j, i⟩) ≫ eqToHom _ =
          (s.ι.app ⟨j⟩).φ i at hφ
        change m.φ ⟨j, i⟩ ≫ eqToHom _ = (desc s).φ ⟨j, i⟩
        simpa [desc] using hφ
    let α : c ≅ F.mapCocone (FormalCoproduct.cofan J K) := by
      refine Cocone.ext (φ := ?_) (w := ?_)
      · dsimp [c, F, semiRepresentableOverForget, FormalCoproduct.cofan]
        exact Iso.refl _
      · intro j
        rcases j with ⟨j⟩
        refine FormalCoproduct.hom_ext (h₁ := ?_) (h₂ := ?_)
        · funext i
          rfl
        · intro i
          dsimp [F, semiRepresentableOverForget] at i
          dsimp [c, A, F, semiRepresentableOverForget, FormalCoproduct.cofan,
            Discrete.natTrans]
          simp
    exact IsColimit.ofIsoColimit hstd
      (α ≪≫ (Cocone.functoriality _ _).mapIso
        ((FormalCoproduct.isColimitCofan J K).uniqueUpToIso hc))
  letI : PreservesColimitsOfShape (Discrete J)
      (semiRepresentableOverForget X) :=
    preservesColimitsOfShape_of_discrete _
  letI : PreservesColimitsOfShape (Discrete J)
      (semiRepresentablePresheafFunctor (C := C)) :=
    semiRepresentablePresheafFunctor_preserves_coproducts (C := C) J
  have h_under : PreservesColimitsOfShape (Discrete J)
      (semiRepresentableOverUnderlying X) := by
    infer_instance
  letI : PreservesColimitsOfShape (Discrete J)
      (semiRepresentableOverPresheafFunctor X ⋙
        (Over.forget (representablePresheaf X) :
          PresheafOver C X ⥤ Presheaf C)) := by
    simpa only [semiRepresentableOverPresheafFunctor_forget] using h_under
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (semiRepresentableOverPresheafFunctor X)
    (Over.forget (representablePresheaf X))

/-- If `C` has fibre products, then `SR(C/X)` has finite limits. -/
theorem semiRepresentableOver_has_finite_limits
    {C : Type u} [Category.{v} C] (X : C) [HasPullbacks C] :
    HasFiniteLimits (SemiRepresentableOver C X) := by
  let _ : HasPullbacks (Over X) := inferInstance
  let _ : HasTerminal (Over X) := Over.over_hasTerminal X
  exact hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- If `C` has fibre products, the functor to `PSh(C)/h_X` commutes with
finite limits. -/
theorem semiRepresentableOverPresheafFunctor_preserves_finite_limits
    {C : Type u} [Category.{v} C] (X : C) [HasPullbacks C] :
    PreservesFiniteLimits (semiRepresentableOverPresheafFunctor X) := by
  letI : HasTerminal (Over X) := Over.over_hasTerminal X
  letI : HasTerminal (SemiRepresentableOver C X) :=
    (FormalCoproduct.isTerminalIncl (⊤_ (Over X)) terminalIsTerminal).hasTerminal
  letI : HasTerminal (PresheafOver C X) :=
    Over.over_hasTerminal (representablePresheaf X)
  have hterm :
      (semiRepresentableOverPresheafFunctor X).obj
          (⊤_ (SemiRepresentableOver C X)) ≅
        (⊤_ (PresheafOver C X)) := by
    let e0 :=
      (((FormalCoproduct.evalCompInclIsoId C (Presheaf C)).app
        (functorOfPoints (C := C))).app X)
    let eT : (⊤_ (SemiRepresentableOver C X)) ≅
        (FormalCoproduct.incl (Over X)).obj (Over.mk (𝟙 X)) :=
      terminalIsoIsTerminal
        (FormalCoproduct.isTerminalIncl (Over.mk (𝟙 X)) Over.mkIdTerminal)
    let e0' := (semiRepresentableOverUnderlying X).mapIso eT ≪≫ e0
    let eP : Over.mk (𝟙 (representablePresheaf X)) ≅
        (⊤_ (PresheafOver C X)) :=
      (terminalIsoIsTerminal
        (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (representablePresheaf X))))).symm
    let eleft := e0' ≪≫ (Over.forget (representablePresheaf X)).mapIso eP
    refine Over.isoMk eleft ?_
    change (e0'.hom ≫ eP.hom.left) ≫ (⊤_ (PresheafOver C X)).hom =
      semiRepresentableOverStructureMap X (⊤_ (SemiRepresentableOver C X))
    rw [Category.assoc, eP.hom.w]
    have he0comp (j : ((FormalCoproduct.incl C).obj X).I) :
        Sigma.ι
          (fun j => functorOfPoints.obj (((FormalCoproduct.incl C).obj X).obj j)) j ≫
          e0.hom = 𝟙 (functorOfPoints.obj X) := by
      cases j
      rw [show e0.hom = Sigma.desc (fun j =>
          𝟙 (functorOfPoints.obj (((FormalCoproduct.incl C).obj X).obj j))) by rfl]
      exact Sigma.ι_desc _ _
    have heTcomp (i : (⊤_ (SemiRepresentableOver C X)).I) :
        (eT.hom.φ i).left = ((⊤_ (SemiRepresentableOver C X)).obj i).hom := by
      have h := Over.Hom.w (eT.hom.φ i)
      change (eT.hom.φ i).left ≫ 𝟙 X =
        ((⊤_ (SemiRepresentableOver C X)).obj i).hom at h
      exact (Category.comp_id (eT.hom.φ i).left).symm.trans h
    refine Sigma.hom_ext _ _ (fun i => ?_)
    dsimp [e0', Functor.mapIso, Iso.trans]
    rw [← Category.assoc]
    simp [Category.assoc, Category.comp_id, Sigma.ι_desc,
      semiRepresentableOverStructureMap,
      representablePresheafMapOfOver,
      e0', semiRepresentableOverUnderlying,
      semiRepresentablePresheafFunctor, FormalCoproduct.yoneda,
      FormalCoproduct.eval, Functor.comp_map]
    have he0comp' (j :
        ((semiRepresentableOverForget X).obj
          ((FormalCoproduct.incl (Over X)).obj (Over.mk (𝟙 X)))).I) :
        Sigma.ι
            (fun j => functorOfPoints.obj
              (((semiRepresentableOverForget X).obj
                ((FormalCoproduct.incl (Over X)).obj (Over.mk (𝟙 X)))).obj j)) j ≫
          e0.hom = 𝟙 (functorOfPoints.obj X) := by
      cases j
      rw [show e0.hom = Sigma.desc (fun j =>
          𝟙 (functorOfPoints.obj (((FormalCoproduct.incl C).obj X).obj j))) by rfl]
      exact Sigma.ι_desc _ _
    have htarget : ∀ (j k :
        ((semiRepresentableOverForget X).obj
          ((FormalCoproduct.incl (Over X)).obj (Over.mk (𝟙 X)))).I), j = k := by
      intro j k
      dsimp [semiRepresentableOverForget] at j k
      change PUnit at j
      change PUnit at k
      cases j
      cases k
      rfl
    let j0 :
        ((semiRepresentableOverForget X).obj
          ((FormalCoproduct.incl (Over X)).obj (Over.mk (𝟙 X)))).I := by
      dsimp [semiRepresentableOverForget]
      change PUnit
      exact PUnit.unit
    let i0 : ((semiRepresentableOverForget X).obj
        (⊤_ (SemiRepresentableOver C X))).I :=
      ((semiRepresentableOverForget X).map eT.inv).f j0
    have hm := htarget
      (((semiRepresentableOverForget X).map eT.hom).f i)
      (((semiRepresentableOverForget X).map eT.hom).f i0)
    have hi := congrArg (((semiRepresentableOverForget X).map eT.inv).f) hm
    have hcomp :
        ((semiRepresentableOverForget X).map eT.inv).f ∘
            ((semiRepresentableOverForget X).map eT.hom).f = id := by
      change ((semiRepresentableOverForget X).map eT.hom ≫
        (semiRepresentableOverForget X).map eT.inv).f = id
      rw [← (semiRepresentableOverForget X).map_comp, eT.hom_inv_id]
      rw [(semiRepresentableOverForget X).map_id]
      rfl
    change (((semiRepresentableOverForget X).map eT.inv).f ∘
      ((semiRepresentableOverForget X).map eT.hom).f) i =
      (((semiRepresentableOverForget X).map eT.inv).f ∘
        ((semiRepresentableOverForget X).map eT.hom).f) i0 at hi
    have hi' : i = i0 := by
      rw [hcomp] at hi
      simpa using hi
    rw [hi']
    simp [semiRepresentableOverForget, FormalCoproduct.incl,
      FormalCoproduct.isTerminalIncl, terminalIsoIsTerminal,
      semiRepresentableOverStructureMap, representablePresheafMapOfOver,
      Category.assoc, he0comp']
  letI : PreservesLimit (Functor.empty (SemiRepresentableOver C X))
      (semiRepresentableOverPresheafFunctor X) :=
    preservesTerminal_of_iso (semiRepresentableOverPresheafFunctor X) hterm
  letI : PreservesLimitsOfShape (Discrete PEmpty)
      (semiRepresentableOverPresheafFunctor X) := by
    exact preservesLimitsOfShape_pempty_of_preservesTerminal _
  letI : PreservesLimits (semiRepresentablePresheafFunctor (C := C)) :=
    semiRepresentablePresheafFunctor_preserves_limits (C := C)
  letI : PreservesLimitsOfShape WalkingCospan
      (semiRepresentableOverPresheafFunctor X) := by
    refine ⟨fun {K} => ?_⟩
    let f : K.obj WalkingCospan.left ⟶ K.obj WalkingCospan.one :=
      K.map WalkingCospan.Hom.inl
    let g : K.obj WalkingCospan.right ⟶ K.obj WalkingCospan.one :=
      K.map WalkingCospan.Hom.inr
    let pb : ∀ i : Function.Pullback f.f g.f,
        PullbackCone (f.φ i.1.1 ≫ eqToHom (by rw [i.2])) (g.φ i.1.2) :=
      fun i => pullback.cone _ _
    let t : PullbackCone f g := FormalCoproduct.pullbackCone f g pb
    have ht : IsLimit t :=
      FormalCoproduct.isLimitPullbackCone f g pb (fun i => pullback.isLimit _ _)
    have h_cospan : PreservesLimit (cospan f g)
        (semiRepresentableOverPresheafFunctor X) := by
      apply preservesLimit_of_preserves_limit_cone ht
      apply isLimitOfReflects (Over.forget (representablePresheaf X))
      let f' := (semiRepresentableOverForget X).map f
      let g' := (semiRepresentableOverForget X).map g
      have hf : f'.f = f.f := rfl
      have hg : g'.f = g.f := rfl
      let j : ∀ i : Function.Pullback f'.f g'.f,
          Function.Pullback f.f g.f :=
        fun i =>
          ⟨i.1, by
            change f.f i.1.1 = g.f i.1.2
            exact i.2⟩
      have hdiag : ∀ i : Function.Pullback f'.f g'.f,
          cospan
                (f'.φ i.1.1 ≫
                  eqToHom
                    (show ((semiRepresentableOverForget X).obj
                        (K.obj WalkingCospan.one)).obj (f'.f i.1.1) =
                        ((semiRepresentableOverForget X).obj
                          (K.obj WalkingCospan.one)).obj (g'.f i.1.2) by
                      exact congrArg
                        (((semiRepresentableOverForget X).obj
                          (K.obj WalkingCospan.one)).obj) i.2))
                (g'.φ i.1.2) =
              cospan
                ((Over.forget X).map
                  (f.φ (j i).1.1 ≫
                    eqToHom
                      (show (K.obj WalkingCospan.one).obj (f.f (j i).1.1) =
                          (K.obj WalkingCospan.one).obj (g.f (j i).1.2) by
                        exact congrArg (K.obj WalkingCospan.one).obj (j i).2)))
                ((Over.forget X).map (g.φ (j i).1.2)) := by
        intro i
        let i' : Function.Pullback f.f g.f := j i
        change
          cospan
                (f'.φ i.1.1 ≫
                  eqToHom
                    (show ((semiRepresentableOverForget X).obj
                        (K.obj WalkingCospan.one)).obj (f'.f i.1.1) =
                        ((semiRepresentableOverForget X).obj
                          (K.obj WalkingCospan.one)).obj (g'.f i.1.2) by
                      exact congrArg
                        (((semiRepresentableOverForget X).obj
                          (K.obj WalkingCospan.one)).obj) i.2))
                (g'.φ i.1.2) =
              cospan
                ((Over.forget X).map
                  (f.φ i'.1.1 ≫
                    eqToHom
                      (show (K.obj WalkingCospan.one).obj (f.f i'.1.1) =
                          (K.obj WalkingCospan.one).obj (g.f i'.1.2) by
                        exact congrArg (K.obj WalkingCospan.one).obj i'.2)))
                ((Over.forget X).map (g.φ i'.1.2))
        dsimp [f', g', semiRepresentableOverForget]
        apply CategoryTheory.Functor.hext (h_obj := ?_) (h_map := ?_)
        · intro j
          rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl
        · intro j k q
          rcases j with (⟨⟩ | ⟨(⟨⟩ | ⟨⟩)⟩)
          · rcases k with (⟨⟩ | ⟨(⟨⟩ | ⟨⟩)⟩)
            · have hq : q = 𝟙 _ := Subsingleton.elim _ _
              subst q
              rfl
            · cases q
            · cases q
          · rcases k with (⟨⟩ | ⟨(⟨⟩ | ⟨⟩)⟩)
            · have hq : q = WalkingCospan.Hom.inl := Subsingleton.elim _ _
              subst q
              simp only [cospan_map_inl]
              change
                (f.φ i'.1.1).left ≫ eqToHom _ ≍
                  (f.φ i'.1.1 ≫ eqToHom _).left
              simp only [Over.comp_left, Over.eqToHom_left]
              rfl
            · have hq : q = 𝟙 _ := Subsingleton.elim _ _
              subst q
              rfl
            · cases q
          · rcases k with (⟨⟩ | ⟨(⟨⟩ | ⟨⟩)⟩)
            · have hq : q = WalkingCospan.Hom.inr := Subsingleton.elim _ _
              subst q
              simp only [cospan_map_inr]
              change
                (g.φ i'.1.2).left ≍
                  (g.φ i'.1.2).left
              rfl
            · cases q
            · have hq : q = 𝟙 _ := Subsingleton.elim _ _
              subst q
              rfl
      let pb' : ∀ i : Function.Pullback f'.f g'.f,
          PullbackCone (f'.φ i.1.1 ≫ eqToHom (by rw [i.2])) (g'.φ i.1.2) :=
        fun i =>
          (Cone.postcompose (eqToIso (hdiag i)).inv).obj
            ((pb (j i)).map (Over.forget X))
      have hpb' : ∀ i, IsLimit (pb' i) := by
        intro i
        have hpb : IsLimit (pb (j i)) := pullback.isLimit _ _
        have hmap : IsLimit ((Over.forget X).mapCone (pb (j i))) :=
          isLimitOfPreserves (Over.forget X) hpb
        have hmap' : IsLimit ((pb (j i)).map (Over.forget X)) :=
          (PullbackCone.isLimitMapConeEquiv (pb (j i)) (Over.forget X)).1 hmap
        exact (IsLimit.postcomposeHomEquiv (eqToIso (hdiag i)).symm
          ((pb (j i)).map (Over.forget X))).symm hmap'
      let t' : PullbackCone f' g' := FormalCoproduct.pullbackCone f' g' pb'
      have ht' : IsLimit t' :=
        FormalCoproduct.isLimitPullbackCone f' g' pb' hpb'
      have ht'F : IsLimit
          ((semiRepresentablePresheafFunctor (C := C)).mapCone t') :=
        isLimitOfPreserves (semiRepresentablePresheafFunctor (C := C)) ht'
      let e :
          ((cospan f g ⋙ semiRepresentableOverPresheafFunctor X) ⋙
              Over.forget (representablePresheaf X)) ≅
            cospan f' g' ⋙ semiRepresentablePresheafFunctor := by
        refine NatIso.ofComponents (fun j => ?_) ?_
        · rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl
        · intro j k q
          rcases j with (⟨⟩ | ⟨(⟨⟩ | ⟨⟩)⟩)
          · rcases k with (⟨⟩ | ⟨(⟨⟩ | ⟨⟩)⟩)
            · have hq : q = 𝟙 _ := Subsingleton.elim _ _
              subst q
              rfl
            · cases q
            · cases q
          · rcases k with (⟨⟩ | ⟨(⟨⟩ | ⟨⟩)⟩)
            · have hq : q = WalkingCospan.Hom.inl := Subsingleton.elim _ _
              subst q
              rfl
            · have hq : q = 𝟙 _ := Subsingleton.elim _ _
              subst q
              rfl
            · cases q
          · rcases k with (⟨⟩ | ⟨(⟨⟩ | ⟨⟩)⟩)
            · have hq : q = WalkingCospan.Hom.inr := Subsingleton.elim _ _
              subst q
              rfl
            · cases q
            · have hq : q = 𝟙 _ := Subsingleton.elim _ _
              subst q
              rfl
      have ht'F' : IsLimit
          ((Cone.postcompose e.inv).obj
            ((semiRepresentablePresheafFunctor (C := C)).mapCone t')) :=
        (IsLimit.postcomposeInvEquiv e
          ((semiRepresentablePresheafFunctor (C := C)).mapCone t')).symm ht'F
      have hmap {q : WalkingCospan} (i : t'.pt.I) :
          Sigma.ι (fun i => yoneda.obj (t'.pt.obj i)) i ≫
              (semiRepresentablePresheafFunctor (C := C)).map (t'.π.app q) =
            yoneda.map ((t'.π.app q).φ i) ≫
              Sigma.ι
                (fun i =>
                  yoneda.obj (((cospan f' g').obj q).obj i))
                ((t'.π.app q).f i) := by
        exact semiRepresentablePresheafFunctor_map_ι (t'.π.app q) i
      apply IsLimit.ofIsoLimit ht'F'
      refine Cone.ext (eqToIso ?_) ?_
      · rfl
      · intro j
        rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;>
          simp [e, t, semiRepresentableOverPresheafFunctor,
            semiRepresentableOverUnderlying, semiRepresentableOverForget,
            semiRepresentablePresheafFunctor_map_ι,
            NatTrans.comp_app, Functor.map_comp, Sigma.ι_desc,
            Category.assoc] <;>
          apply Sigma.hom_ext <;>
          intro U <;>
          dsimp [Functor.mapCone, Cone.functoriality, Cone.postcompose]
          all_goals
            conv_lhs =>
              rw [← Category.assoc]
            rw [hmap U]
    exact preservesLimit_of_iso_diagram (semiRepresentableOverPresheafFunctor X)
      (diagramIsoCospan K).symm

end

end Formalization.Books.Hypercovering.Unit02
