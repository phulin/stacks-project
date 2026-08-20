import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.Subcategory
import Formalization.Books.Derived.Unit11.DerivedCategories

/-!
# Derived Categories, Chapter 12: the canonical delta-functor

The canonical connecting morphism in the derived category is Mathlib's
DerivedCategory.triangleOfSESδ. This file records the source construction
and its bounded, truncation, comparison, and vanishing-composition interfaces.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit03
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit09
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Derived.Unit12

/-! ## The obstruction in the homotopy category -/

/-- A short exact sequence which is not split. -/
def HasNonsplitShortExactSequence
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∃ S : ShortComplex C, S.ShortExact ∧ ¬ Nonempty S.Splitting

/-- The homotopy-category functor on cochain complexes. -/
noncomputable abbrev homotopyCanonicalFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    CochainComplex C ℤ ⥤ HomotopyCategory C (.up ℤ) :=
  HomotopyCategory.quotient C (.up ℤ)

/-- The single-complex calculation used in the nonsplit-extension warning. -/
theorem homotopy_single_shift_hom_eq_zero
    (C : Type u) [Category.{v} C] [Abelian C] (A B : C) :
    ∀ f : (HomotopyCategory.singleFunctor C 0).obj B ⟶
      (shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).obj
        ((HomotopyCategory.singleFunctor C 0).obj A),
    f = 0 := by
  change ∀ f : (HomotopyCategory.quotient C (.up ℤ)).obj
      ((CochainComplex.singleFunctor C 0).obj B) ⟶
      (shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj A)),
    f = 0
  intro f
  let e := HomotopyCategory.shift_quotient_obj
    ((CochainComplex.singleFunctor C 0).obj A) (1 : ℤ)
  have hf : f ≫ eqToHom e = 0 := by
    obtain ⟨g, hg⟩ :=
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective
        (f ≫ eqToHom e)
    have hg0 : g = 0 := by
      ext i
      by_cases hi : i = 0
      · subst hi
        exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 B 1
          (by norm_num)).eq_of_tgt _ _
      · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 B i hi).eq_of_src _ _
    rw [← hg, hg0]
    exact (HomotopyCategory.quotient C (.up ℤ)).map_zero _ _
  apply (cancel_mono (eqToHom e)).1
  simpa only [zero_comp] using hf

/-- A delta-functor structure on the homotopy-category functor would split every
short exact sequence of objects. -/
theorem homotopy_delta_functor_forces_splitting
    {C : Type u} [Category.{v} C] [Abelian C]
    (G : DeltaFunctor (homotopyCanonicalFunctor C))
    {S : ShortComplex C} (hS : S.ShortExact) :
    Nonempty S.Splitting := by
  let S' := S.map (CochainComplex.singleFunctor C 0)
  let _ : PreservesFiniteLimits (CochainComplex.singleFunctor C 0) := by
    dsimp [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    infer_instance
  let _ : PreservesFiniteColimits (CochainComplex.singleFunctor C 0) := by
    dsimp [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    infer_instance
  have hS' : S'.ShortExact := hS.map_of_exact (CochainComplex.singleFunctor C 0)
  let T := DeltaFunctor.imageTriangle (homotopyCanonicalFunctor C) G S' hS'
  have hT : T ∈ distTriang (HomotopyCategory C (.up ℤ)) :=
    DeltaFunctor.imageTriangle_distinguished (homotopyCanonicalFunctor C) G S' hS'
  have hδ : T.mor₃ = 0 := by
    dsimp [T, DeltaFunctor.imageTriangle]
    exact homotopy_single_shift_hom_eq_zero C S.X₁ S.X₃ _
  obtain ⟨s', hs'⟩ := T.coyoneda_exact₃ hT (𝟙 T.obj₃) (by simp [hδ])
  obtain ⟨s, rfl⟩ :=
    (HomotopyCategory.quotient C (.up ℤ)).map_surjective s'
  have hcomp :
      (HomotopyCategory.quotient C (.up ℤ)).map (s ≫ S'.g) =
        (HomotopyCategory.quotient C (.up ℤ)).map (𝟙 S'.X₃) := by
    simpa only [Functor.map_comp, Functor.map_id] using
      (show (HomotopyCategory.quotient C (.up ℤ)).map s ≫
          (HomotopyCategory.quotient C (.up ℤ)).map S'.g =
        (HomotopyCategory.quotient C (.up ℤ)).map (𝟙 S'.X₃) from
        by simpa [T, DeltaFunctor.imageTriangle, homotopyCanonicalFunctor,
          Triangle.mk] using hs'.symm)
  have ho : Homotopy (s ≫ S'.g) (𝟙 S'.X₃) :=
    HomotopyCategory.homotopyOfEq _ _ hcomp
  have hs0 : s.f 0 ≫ S'.g.f 0 = 𝟙 _ := by
    have hdz (i j : ℤ) : S'.X₃.d i j = 0 := by
      change ((HomologicalComplex.single C (.up ℤ) 0).obj S.X₃).d i j = 0
      exact HomologicalComplex.single_obj_d (c := .up ℤ) 0 S.X₃ i j
    have hdnext : (dNext (C := S'.X₃) (D := S'.X₃) 0) ho.hom = 0 := by
      simp [dNext, hdz]
    have hprev : (prevD (C := S'.X₃) (D := S'.X₃) 0) ho.hom = 0 := by
      simp [prevD, hdz]
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, hdnext, hprev,
      zero_add, add_zero] using ho.comm 0
  let s₀ : S.X₃ ⟶ S.X₂ :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃).inv ≫
      s.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₂).hom
  have hs₀ : s₀ ≫ S.g = 𝟙 S.X₃ := by
    dsimp [S', ShortComplex.map] at hs0
    change s.f 0 ≫
        ((HomologicalComplex.single C (.up ℤ) 0).map S.g).f 0 =
      𝟙 (((HomologicalComplex.single C (.up ℤ) 0).obj S.X₃).X 0) at hs0
    rw [HomologicalComplex.single_map_f_self] at hs0
    apply (cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃).inv).1
    dsimp [s₀]
    have h' := congrArg
      (fun x =>
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃).inv ≫ x) hs0
    have reassoc5 {W X Y Z V U : C} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
        (d : Z ⟶ V) (e : V ⟶ U) :
        (((a ≫ (b ≫ c)) ≫ d) ≫ e) = a ≫ b ≫ c ≫ d ≫ e := by
      simp only [Category.assoc]
    convert h' using 1
    · exact reassoc5
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃).inv (s.f 0)
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₂).hom S.g
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃).inv
    · rw [Category.id_comp, Category.comp_id]
  exact ⟨ShortComplex.Splitting.ofExactOfSection S hS.exact s₀ hs₀ hS.mono_f⟩

/-- Hence the homotopy-category functor is not a delta-functor whenever a
nonsplit short exact sequence exists. -/
theorem homotopyCanonicalFunctor_not_deltaFunctor_of_nonsplit
    (C : Type u) [Category.{v} C] [Abelian C]
    (hC : HasNonsplitShortExactSequence C) :
    ¬ Nonempty (DeltaFunctor (homotopyCanonicalFunctor C)) := by
  rintro ⟨G⟩
  obtain ⟨S, hS, hns⟩ := hC
  exact hns (homotopy_delta_functor_forces_splitting G hS)

/-! ## The mapping-cone construction -/

/-- The mapping-cone projection associated with a short complex. -/
noncomputable def coneToShortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (CochainComplex C ℤ)) :
    CochainComplex.mappingCone S.f ⟶ S.X₃ :=
  CochainComplex.mappingCone.descShortComplex S

/-- The mapping-cone component is the standard biproduct of the target and the
shifted source, in the order used in the textbook. -/
noncomputable def mappingConeComponentIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (n : ℤ) :
    (CochainComplex.mappingCone S.f).X n ≅
      S.X₂.X n ⊞ S.X₁.X (n + 1) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod S.f n (n + 1) rfl ≪≫
    biprod.braiding _ _

@[reassoc (attr := simp)]
theorem coneToShortExact_comp_inclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} :
    CochainComplex.mappingCone.inr S.f ≫ coneToShortExact S = S.g :=
  CochainComplex.mappingCone.inr_descShortComplex S

/-- The mapping-cone projection is a quasi-isomorphism for a short exact
sequence of complexes. -/
theorem coneToShortExact_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    QuasiIso (coneToShortExact S) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex hS

theorem coneToShortExact_derived_isIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    IsIso (DerivedCategory.Q.map (coneToShortExact S)) := by
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact coneToShortExact_quasiIso hS

/-- The kernel of q is the cone of the identity on the first complex. -/
theorem coneToShortExact_kernel_iso_mappingCone_identity
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    Nonempty
      (kernel (coneToShortExact S) ≅
        CochainComplex.mappingCone (𝟙 S.X₁)) := by
  let k : CochainComplex.mappingCone (𝟙 S.X₁) ⟶ CochainComplex.mappingCone S.f :=
    CochainComplex.mappingCone.desc (𝟙 S.X₁)
      (CochainComplex.mappingCone.inl S.f)
      (S.f ≫ CochainComplex.mappingCone.inr S.f) (by simp)
  have hk : k ≫ coneToShortExact S = 0 := by
    ext n
    apply CochainComplex.mappingCone.ext_from (𝟙 S.X₁) (n + 1) n rfl
    · simp [k, coneToShortExact]
    · simp [k, coneToShortExact, Category.assoc]
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
        congrArg (fun h => h.f n) S.zero
  have hc : IsLimit (KernelFork.ofι k hk) := by
    apply HomologicalComplex.isLimitOfEval
    intro n
    refine (isLimitMapConeForkEquiv' (HomologicalComplex.eval C (.up ℤ) n) hk).symm.toFun ?_
    have hq : (coneToShortExact S).f n =
        (CochainComplex.mappingCone.snd S.f).v n n (add_zero n) ≫ S.g.f n := by
      change (CochainComplex.mappingCone.desc S.f 0 S.g (by simp)).f n = _
      simpa [CochainComplex.mappingCone.snd] using
        (CochainComplex.mappingCone.desc_f S.f 0 S.g (by simp) n (n + 1) rfl)
    have hfn : IsLimit (KernelFork.ofι (S.f.f n) (by
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          congrArg (fun h => h.f n) S.zero)) := by
      convert (hS.map_of_exact (HomologicalComplex.eval C (.up ℤ) n)).fIsKernel using 1
      · change parallelPair (S.g.f n) 0 =
          parallelPair ((HomologicalComplex.eval C (.up ℤ) n).map S.g) 0
        simp [HomologicalComplex.eval]
        rfl
      · rfl
    let liftAt : ∀ {W' : C}
        (g' : W' ⟶ (CochainComplex.mappingCone S.f).X n)
        (_ : g' ≫ (coneToShortExact S).f n = 0),
        W' ⟶ (CochainComplex.mappingCone (𝟙 S.X₁)).X n :=
      fun {W'} g' eq' =>
        let b : W' ⟶ S.X₁.X n := hfn.lift (KernelFork.ofι
          (g' ≫ (CochainComplex.mappingCone.snd S.f).v n n (add_zero n)) (by
            rw [Category.assoc, ← hq]
            exact eq'))
        (g' ≫ (CochainComplex.mappingCone.fst S.f).1.v n (n + 1) rfl) ≫
            (CochainComplex.mappingCone.inl (𝟙 S.X₁)).v (n + 1) n (by simp) +
          b ≫
            (CochainComplex.mappingCone.inr (𝟙 S.X₁)).f n
    have hkn : k.f n ≫ (coneToShortExact S).f n = 0 := by
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
        congrArg (fun h => h.f n) hk
    have hkfst :
        k.f n ≫ (CochainComplex.mappingCone.fst S.f).1.v n (n + 1) rfl =
          (CochainComplex.mappingCone.fst (𝟙 S.X₁)).1.v n (n + 1) rfl := by
      apply CochainComplex.mappingCone.ext_from (𝟙 S.X₁) (n + 1) n rfl
      · simp [k]
      · simp [k]
    have hksnd :
        k.f n ≫ (CochainComplex.mappingCone.snd S.f).v n n (add_zero n) =
          (CochainComplex.mappingCone.snd (𝟙 S.X₁)).v n n (add_zero n) ≫ S.f.f n := by
      apply CochainComplex.mappingCone.ext_from (𝟙 S.X₁) (n + 1) n rfl
      · simp [k]
      · simp [k]
    refine KernelFork.IsLimit.ofι (k.f n) hkn liftAt ?_ ?_
    · intro W' g' eq'
      dsimp [liftAt]
      apply CochainComplex.mappingCone.ext_to S.f n (n + 1) rfl
      · simp [k, Category.assoc]
      · simp only [add_comp, Category.assoc]
        rw [hksnd]
        simp
        simpa only [Fork.app_zero_eq_ι, Fork.ι_ofι] using
          (hfn.fac (KernelFork.ofι
            (g' ≫ (CochainComplex.mappingCone.snd S.f).v n n (add_zero n)) (by
              rw [Category.assoc, ← hq]
              exact eq')) WalkingParallelPair.zero)
    · intro W' g' eq' m hm
      apply CochainComplex.mappingCone.ext_to (𝟙 S.X₁) n (n + 1) rfl
      · have hm' := congrArg
          (fun x => x ≫ (CochainComplex.mappingCone.fst S.f).1.v n (n + 1) rfl) hm
        rw [Category.assoc, hkfst] at hm'
        simpa [liftAt, Category.assoc] using hm'
      · have hm' := congrArg
          (fun x => x ≫ (CochainComplex.mappingCone.snd S.f).v n n (add_zero n)) hm
        rw [Category.assoc, hksnd] at hm'
        have hmb : m ≫ (CochainComplex.mappingCone.snd (𝟙 S.X₁)).v n n (add_zero n) =
            hfn.lift (KernelFork.ofι
              (g' ≫ (CochainComplex.mappingCone.snd S.f).v n n (add_zero n)) (by
                rw [Category.assoc, ← hq]
                exact eq')) := by
          exact hfn.uniq
            (KernelFork.ofι
              (g' ≫ (CochainComplex.mappingCone.snd S.f).v n n (add_zero n)) (by
                rw [Category.assoc, ← hq]
                exact eq'))
            (m ≫ (CochainComplex.mappingCone.snd (𝟙 S.X₁)).v n n (add_zero n)) (by
              intro j
              rcases j with (_ | _)
              · simpa using hm'
              · simpa [Category.assoc] using congrArg (fun x => x ≫ S.g.f n) hm')
        simpa [liftAt, Category.assoc] using hmb
  exact ⟨(hc.conePointUniqueUpToIso (kernelIsKernel _)).symm⟩

/-- The kernel of the mapping-cone projection is represented by the acyclic
cone of the identity. -/
theorem mappingCone_identity_acyclic
    (C : Type u) [Category.{v} C] [Abelian C]
    (A : CochainComplex C ℤ) :
    (CochainComplex.mappingCone (𝟙 A)).Acyclic := by
  rw [Formalization.Books.Homology.Unit13.cochain_acyclic_iff_cohomology_isZero]
  intro n
  apply (IsZero.iff_id_eq_zero _).2
  rw [← HomologicalComplex.homologyMap_id (K := CochainComplex.mappingCone (𝟙 A)) n]
  rw [(CochainComplex.mappingCone.homotopyToZeroOfId A).homologyMap_eq n]
  exact HomologicalComplex.homologyMap_zero _ _ n

/-- The mapping-cone triangle is distinguished already in the homotopy
category, before applying the derived localization. -/
theorem mappingConeTriangleh_distinguished
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    CochainComplex.mappingCone.triangleh f ∈
      distTriang (HomotopyCategory C (.up ℤ)) :=
  coneTriangleh_distinguished f

/-! ## The canonical connecting morphism and delta-functor -/

/-- The source connecting morphism, expressed using the canonical cone triangle
and the localization commutation isomorphism. -/
noncomputable def canonicalDerivedDelta
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    (DerivedCategory.Q (C := C)).obj S.X₃ ⟶
      ((DerivedCategory.Q (C := C)).obj S.X₁)⟦(1 : ℤ)⟧ :=
  letI : QuasiIso (coneToShortExact S) := coneToShortExact_quasiIso hS
  inv (DerivedCategory.Q.map (coneToShortExact S)) ≫
    DerivedCategory.Q.map ((CochainComplex.mappingCone.triangle S.f).mor₃) ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁

/-- The cone formula is Mathlib's canonical connecting morphism. -/
theorem canonicalDerivedDelta_eq_triangleOfSESδ
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    canonicalDerivedDelta hS = DerivedCategory.triangleOfSESδ hS := by
  rfl

/-- The distinguished triangle attached to a short exact sequence of complexes. -/
noncomputable def canonicalDerivedTriangle
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    Triangle (DerivedCategory C) :=
  Triangle.mk (DerivedCategory.Q.map S.f) (DerivedCategory.Q.map S.g)
    (canonicalDerivedDelta hS)

theorem canonicalDerivedTriangle_distinguished
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    canonicalDerivedTriangle hS ∈ distTriang (DerivedCategory C) := by
  change DerivedCategory.triangleOfSES hS ∈ distTriang (DerivedCategory C)
  exact DerivedCategory.triangleOfSES_distinguished hS

/-- The canonical triangle is the cone triangle after localization. -/
noncomputable def canonicalDerivedTriangleIsoCone
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    canonicalDerivedTriangle hS ≅
      (DerivedCategory.Q (C := C)).mapTriangle.obj
        (CochainComplex.mappingCone.triangle S.f) :=
  let e : canonicalDerivedTriangle hS = DerivedCategory.triangleOfSES hS := by
    dsimp [canonicalDerivedTriangle, DerivedCategory.triangleOfSES]
    rw [canonicalDerivedDelta_eq_triangleOfSESδ hS]
  eqToIso e ≪≫ DerivedCategory.triangleOfSESIso hS

/-- Naturality of the connecting morphism for a morphism of short exact
sequences. -/
theorem canonicalDerivedDelta_naturality
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    canonicalDerivedDelta h₁ ≫
        (DerivedCategory.Q.map φ.τ₁)⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map φ.τ₃ ≫ canonicalDerivedDelta h₂ := by
  rw [canonicalDerivedDelta_eq_triangleOfSESδ h₁,
    canonicalDerivedDelta_eq_triangleOfSESδ h₂]
  exact DerivedCategory.triangleOfSESδ_naturality h₁ h₂ φ

/-- The cone map induced by a morphism of short exact sequences. -/
noncomputable def mappingConeMapOfShortComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂) :
    CochainComplex.mappingCone S₁.f ⟶ CochainComplex.mappingCone S₂.f :=
  CochainComplex.mappingCone.map S₁.f S₂.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm

theorem mappingConeMapOfShortComplex_desc_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂) :
    mappingConeMapOfShortComplex φ ≫ coneToShortExact S₂ =
      coneToShortExact S₁ ≫ φ.τ₃ :=
  by
    simpa [mappingConeMapOfShortComplex, coneToShortExact] using
      (CochainComplex.mappingCone.descShortComplex_naturality φ)

/-- The cone triangle map satisfies the third commutative square used in the
naturality proof. -/
noncomputable def mappingConeTriangleMapOfShortComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂) :
    CochainComplex.mappingCone.triangle S₁.f ⟶
      CochainComplex.mappingCone.triangle S₂.f :=
  CochainComplex.mappingCone.triangleMap S₁.f S₂.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm

theorem mappingConeTriangleMapOfShortComplex_comm₃
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂) :
    (mappingConeTriangleMapOfShortComplex φ).hom₃ ≫
        (CochainComplex.mappingCone.triangle S₂.f).mor₃ =
      (CochainComplex.mappingCone.triangle S₁.f).mor₃ ≫
        (φ.τ₁)⟦(1 : ℤ)⟧' :=
  (mappingConeTriangleMapOfShortComplex φ).comm₃.symm

/-- The canonical delta-functor on all cochain complexes. -/
noncomputable def canonicalDerivedDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    DeltaFunctor (DerivedCategory.Q (C := C)) where
  delta := fun S hS => canonicalDerivedDelta hS
  distinguished := fun S hS => canonicalDerivedTriangle_distinguished hS
  naturality := by
    intro S₁ S₂ φ h₁ h₂
    exact (canonicalDerivedDelta_naturality h₁ h₂ φ).symm

/-! ## Bounded variants -/

/- The existing DeltaFunctor structure is parameterized by an abelian source
category.  The bounded full subcategories are abelian because boundedness is
stable under the finite limits and colimits used for kernels and cokernels.
These three closure interfaces are the only missing subcategory instances in
the imported API. -/

theorem cochainPlus_containsZero
    (C : Type u) [Category.{v} C] [Abelian C] :
    (CochainComplex.plus C).ContainsZero := by
  refine ⟨⟨(0 : CochainComplex C ℤ), isZero_zero (CochainComplex C ℤ), ?_⟩⟩
  refine ⟨0, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (HomologicalComplex.eval C (.up ℤ) i).map_isZero
    (isZero_zero (CochainComplex C ℤ))

theorem cochainPlus_isClosedUnderKernels
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderKernels (CochainComplex.plus C) := by
  constructor
  intro _ ⟨f, k, hk, hf⟩
  apply (CochainComplex.plus C).prop_of_isLimit hk
  intro j
  rcases j with (_ | _)
  · exact hf.1
  · exact hf.2

theorem cochainPlus_isClosedUnderCokernels
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderCokernels (CochainComplex.plus C) := by
  constructor
  intro _ ⟨f, k, hk, hf⟩
  apply (CochainComplex.plus C).prop_of_isColimit hk
  intro j
  rcases j with (_ | _)
  · exact hf.1
  · exact hf.2

theorem cochainPlus_isClosedUnderFiniteProducts
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderFiniteProducts (CochainComplex.plus C) := by
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

theorem boundedAbove_containsZero
    (C : Type u) [Category.{v} C] [Abelian C] :
    (boundedAboveProperty C).ContainsZero := by
  refine ⟨⟨(0 : CochainComplex C ℤ), isZero_zero (CochainComplex C ℤ), ?_⟩⟩
  refine ⟨0, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (HomologicalComplex.eval C (.up ℤ) i).map_isZero
    (isZero_zero (CochainComplex C ℤ))

theorem boundedAbove_isClosedUnderKernels
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderKernels (boundedAboveProperty C) := by
  constructor
  rintro _ @⟨X₁, X₂, f, k, hk, ⟨⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩⟩
  refine ⟨max n₁ n₂, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [IsZero.iff_id_eq_zero]
  exact (isLimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) hk).hom_ext
    (fun j ↦ by
      rcases j with (_ | _)
      · apply (@CochainComplex.isZero_of_isStrictlyLE C _ _ X₁ n₁ i
        (lt_of_le_of_lt (le_max_left _ _) hi) hn₁).eq_of_tgt
      · apply (@CochainComplex.isZero_of_isStrictlyLE C _ _ X₂ n₂ i
        (lt_of_le_of_lt (le_max_right _ _) hi) hn₂).eq_of_tgt)

theorem boundedAbove_isClosedUnderCokernels
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderCokernels (boundedAboveProperty C) := by
  constructor
  rintro _ @⟨X₁, X₂, f, k, hk, ⟨⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩⟩
  refine ⟨max n₁ n₂, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [IsZero.iff_id_eq_zero]
  exact (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) hk).hom_ext
    (fun j ↦ by
      rcases j with (_ | _)
      · apply (@CochainComplex.isZero_of_isStrictlyLE C _ _ X₁ n₁ i
        (lt_of_le_of_lt (le_max_left _ _) hi) hn₁).eq_of_src
      · apply (@CochainComplex.isZero_of_isStrictlyLE C _ _ X₂ n₂ i
        (lt_of_le_of_lt (le_max_right _ _) hi) hn₂).eq_of_src)

theorem boundedAbove_isClosedUnderFiniteProducts
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderFiniteProducts (boundedAboveProperty C) := by
  refine ⟨fun J _ ↦ ?_⟩
  constructor
  intro _ ⟨p⟩
  let _ := Fintype.ofFinite (Discrete J)
  choose n hn using p.prop_diag_obj
  let s := Finset.image n (Finset.univ : Finset (Discrete J)) ∪ {0}
  have hs : s.Nonempty := by
    dsimp [s]
    exact ⟨0, by simp⟩
  have hn' : ∀ j, (p.diag.obj j).IsStrictlyLE (s.max' hs) := by
    intro j
    exact (p.diag.obj j).isStrictlyLE_of_le (n j) (s.max' hs)
      (Finset.le_max' s (n j) (by
        apply Finset.mem_union_left
        exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩))
  refine ⟨s.max' hs, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [IsZero.iff_id_eq_zero]
  apply (isLimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) p.isLimit).hom_ext
  intro j
  have hzero : IsZero ((p.diag.obj j).X i) := by
    exact @CochainComplex.isZero_of_isStrictlyLE C _ _ (p.diag.obj j) (s.max' hs) i hi (hn' j)
  have hπ : (p.π.app j).f i = 0 := by
    apply hzero.eq_of_tgt
  change 𝟙 _ ≫ (p.π.app j).f i = 0 ≫ (p.π.app j).f i
  rw [hπ]
  simp only [comp_zero]

theorem bounded_containsZero
    (C : Type u) [Category.{v} C] [Abelian C] :
    (boundedProperty C).ContainsZero := by
  refine ⟨⟨(0 : CochainComplex C ℤ), isZero_zero (CochainComplex C ℤ), ?_⟩⟩
  refine ⟨0, 0, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (HomologicalComplex.eval C (.up ℤ) i).map_isZero
      (isZero_zero (CochainComplex C ℤ))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (HomologicalComplex.eval C (.up ℤ) i).map_isZero
      (isZero_zero (CochainComplex C ℤ))

theorem bounded_isClosedUnderKernels
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderKernels (boundedProperty C) := by
  constructor
  rintro _ @⟨X₁, X₂, f, k, hk,
    ⟨p₁, q₁, hp₁, hq₁⟩, ⟨p₂, q₂, hp₂, hq₂⟩⟩
  refine ⟨min p₁ p₂, max q₁ q₂, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isLimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) hk).hom_ext
      (fun j ↦ by
        rcases j with (_ | _)
        · apply (@CochainComplex.isZero_of_isStrictlyGE C _ _ X₁ p₁ i
          (lt_of_lt_of_le hi (min_le_left _ _)) hp₁).eq_of_tgt
        · apply (@CochainComplex.isZero_of_isStrictlyGE C _ _ X₂ p₂ i
          (lt_of_lt_of_le hi (min_le_right _ _)) hp₂).eq_of_tgt)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isLimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) hk).hom_ext
      (fun j ↦ by
        rcases j with (_ | _)
        · apply (@CochainComplex.isZero_of_isStrictlyLE C _ _ X₁ q₁ i
          (lt_of_le_of_lt (le_max_left _ _) hi) hq₁).eq_of_tgt
        · apply (@CochainComplex.isZero_of_isStrictlyLE C _ _ X₂ q₂ i
          (lt_of_le_of_lt (le_max_right _ _) hi) hq₂).eq_of_tgt)

theorem bounded_isClosedUnderCokernels
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderCokernels (boundedProperty C) := by
  constructor
  rintro _ @⟨X₁, X₂, f, k, hk,
    ⟨p₁, q₁, hp₁, hq₁⟩, ⟨p₂, q₂, hp₂, hq₂⟩⟩
  refine ⟨min p₁ p₂, max q₁ q₂, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) hk).hom_ext
      (fun j ↦ by
        rcases j with (_ | _)
        · apply (@CochainComplex.isZero_of_isStrictlyGE C _ _ X₁ p₁ i
          (lt_of_lt_of_le hi (min_le_left _ _)) hp₁).eq_of_src
        · apply (@CochainComplex.isZero_of_isStrictlyGE C _ _ X₂ p₂ i
          (lt_of_lt_of_le hi (min_le_right _ _)) hp₂).eq_of_src)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) hk).hom_ext
      (fun j ↦ by
        rcases j with (_ | _)
        · apply (@CochainComplex.isZero_of_isStrictlyLE C _ _ X₁ q₁ i
          (lt_of_le_of_lt (le_max_left _ _) hi) hq₁).eq_of_src
        · apply (@CochainComplex.isZero_of_isStrictlyLE C _ _ X₂ q₂ i
          (lt_of_le_of_lt (le_max_right _ _) hi) hq₂).eq_of_src)

theorem bounded_isClosedUnderFiniteProducts
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderFiniteProducts (boundedProperty C) := by
  refine ⟨fun J _ ↦ ?_⟩
  constructor
  intro _ ⟨p⟩
  let _ := Fintype.ofFinite (Discrete J)
  choose n hn using p.prop_diag_obj
  choose m hm using hn
  let s := Finset.image n (Finset.univ : Finset (Discrete J)) ∪ {0}
  let t := Finset.image m (Finset.univ : Finset (Discrete J)) ∪ {0}
  have hs : s.Nonempty := by
    dsimp [s]
    exact ⟨0, by simp⟩
  have ht : t.Nonempty := by
    dsimp [t]
    exact ⟨0, by simp⟩
  have hn' : ∀ j, (p.diag.obj j).IsStrictlyGE (s.min' hs) := by
    intro j
    let _ : (p.diag.obj j).IsStrictlyGE (n j) := (hm j).1
    exact (p.diag.obj j).isStrictlyGE_of_ge (s.min' hs) (n j)
      (Finset.min'_le s (n j) (by
        apply Finset.mem_union_left
        exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩))
  have hm' : ∀ j, (p.diag.obj j).IsStrictlyLE (t.max' ht) := by
    intro j
    let _ : (p.diag.obj j).IsStrictlyLE (m j) := (hm j).2
    exact (p.diag.obj j).isStrictlyLE_of_le (m j) (t.max' ht)
      (Finset.le_max' t (m j) (by
        apply Finset.mem_union_left
        exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩))
  refine ⟨s.min' hs, t.max' ht, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    apply (isLimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) p.isLimit).hom_ext
    intro j
    have hzero : IsZero ((p.diag.obj j).X i) :=
      @CochainComplex.isZero_of_isStrictlyGE C _ _ (p.diag.obj j) (s.min' hs) i hi (hn' j)
    have hπ : (p.π.app j).f i = 0 := by
      apply hzero.eq_of_tgt
    change 𝟙 _ ≫ (p.π.app j).f i = 0 ≫ (p.π.app j).f i
    rw [hπ]
    simp only [comp_zero]
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    apply (isLimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) p.isLimit).hom_ext
    intro j
    have hzero : IsZero ((p.diag.obj j).X i) :=
      @CochainComplex.isZero_of_isStrictlyLE C _ _ (p.diag.obj j) (t.max' ht) i hi (hm' j)
    have hπ : (p.π.app j).f i = 0 := by
      apply hzero.eq_of_tgt
    change 𝟙 _ ≫ (p.π.app j).f i = 0 ≫ (p.π.app j).f i
    rw [hπ]
    simp only [comp_zero]

noncomputable instance compPlus_abelian
    (C : Type u) [Category.{v} C] [Abelian C] :
    Abelian (CompPlus C) := by
  letI : Abelian (CochainComplex C ℤ) :=
    Formalization.Books.Homology.Unit13.cochainComplex_abelian C
  letI : (CochainComplex.plus C).ContainsZero := cochainPlus_containsZero C
  letI : ObjectProperty.IsClosedUnderKernels (CochainComplex.plus C) :=
    cochainPlus_isClosedUnderKernels C
  letI : ObjectProperty.IsClosedUnderCokernels (CochainComplex.plus C) :=
    cochainPlus_isClosedUnderCokernels C
  letI : ObjectProperty.IsClosedUnderFiniteProducts (CochainComplex.plus C) :=
    cochainPlus_isClosedUnderFiniteProducts C
  infer_instance

noncomputable instance compMinus_abelian
    (C : Type u) [Category.{v} C] [Abelian C] :
    Abelian (CompMinus C) := by
  letI : Abelian (CochainComplex C ℤ) :=
    Formalization.Books.Homology.Unit13.cochainComplex_abelian C
  letI : (boundedAboveProperty C).ContainsZero := boundedAbove_containsZero C
  letI : ObjectProperty.IsClosedUnderKernels (boundedAboveProperty C) :=
    boundedAbove_isClosedUnderKernels C
  letI : ObjectProperty.IsClosedUnderCokernels (boundedAboveProperty C) :=
    boundedAbove_isClosedUnderCokernels C
  letI : ObjectProperty.IsClosedUnderFiniteProducts (boundedAboveProperty C) :=
    boundedAbove_isClosedUnderFiniteProducts C
  infer_instance

noncomputable instance compBounded_abelian
    (C : Type u) [Category.{v} C] [Abelian C] :
    Abelian (CompBounded C) := by
  letI : Abelian (CochainComplex C ℤ) :=
    Formalization.Books.Homology.Unit13.cochainComplex_abelian C
  letI : (boundedProperty C).ContainsZero := bounded_containsZero C
  letI : ObjectProperty.IsClosedUnderKernels (boundedProperty C) :=
    bounded_isClosedUnderKernels C
  letI : ObjectProperty.IsClosedUnderCokernels (boundedProperty C) :=
    bounded_isClosedUnderCokernels C
  letI : ObjectProperty.IsClosedUnderFiniteProducts (boundedProperty C) :=
    bounded_isClosedUnderFiniteProducts C
  infer_instance

noncomputable instance derivedPlus_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    AdditiveCategory (DPlus C) where
  toPreadditive := inferInstance
  toHasFiniteProducts := inferInstance

noncomputable instance derivedMinus_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    AdditiveCategory (DMinus C) where
  toPreadditive := inferInstance
  toHasFiniteProducts := inferInstance

noncomputable instance derivedBounded_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    AdditiveCategory (DBounded C) where
  toPreadditive := inferInstance
  toHasFiniteProducts := inferInstance

/-- The bounded-below complex-to-derived functor supplied by Mathlib. -/
noncomputable abbrev canonicalPlusFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    CompPlus C ⥤ DPlus C :=
  DerivedCategory.Plus.Q (C := C)

/-- The image of a bounded-above complex lies in the bounded-above derived
subcategory. -/
theorem canonicalMinusFunctor_obj_mem
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : CompMinus C) :
    derivedMinusProperty C
      (((boundedAboveProperty C).ι ⋙ DerivedCategory.Q (C := C)).obj X) := by
  obtain ⟨n, hn⟩ := X.property
  change ∃ n : ℤ, (DerivedCategory.TStructure.t (C := C)).IsLE
    (((boundedAboveProperty C).ι ⋙ DerivedCategory.Q (C := C)).obj X) n
  refine ⟨n, ⟨X.obj, Iso.refl _, by exact hn⟩⟩

/-- The bounded-above complex-to-derived functor, obtained by the canonical
full-subcategory lift. -/
noncomputable def canonicalMinusFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    CompMinus C ⥤ DMinus C :=
  (derivedMinusProperty C).lift
    ((boundedAboveProperty C).ι ⋙ DerivedCategory.Q (C := C))
    (canonicalMinusFunctor_obj_mem C)

/-- The image of a bounded complex lies in the bounded derived subcategory. -/
theorem canonicalBoundedFunctor_obj_mem
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : CompBounded C) :
    derivedBoundedProperty C
      (((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C)).obj X) := by
  obtain ⟨p, q, hp, hq⟩ := X.property
  change (derivedPlusProperty C
      (((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C)).obj X) ∧
    derivedMinusProperty C
      (((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C)).obj X))
  constructor
  · change ∃ n : ℤ, (DerivedCategory.TStructure.t (C := C)).IsGE
      (((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C)).obj X) n
    exact ⟨p, ⟨X.obj, Iso.refl _, by exact hp⟩⟩
  · change ∃ n : ℤ, (DerivedCategory.TStructure.t (C := C)).IsLE
      (((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C)).obj X) n
    exact ⟨q, ⟨X.obj, Iso.refl _, by exact hq⟩⟩

/-- The bounded complex-to-derived functor, obtained by the canonical
full-subcategory lift. -/
noncomputable def canonicalBoundedFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    CompBounded C ⥤ DBounded C :=
  (derivedBoundedProperty C).lift
    ((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C))
    (canonicalBoundedFunctor_obj_mem C)

/-- The canonical delta-functor structure on the bounded-below functor. -/
theorem canonicalPlusFunctor_isDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    Nonempty (DeltaFunctor (canonicalPlusFunctor C)) := by
  let _ : Abelian (CochainComplex C ℤ) :=
    Formalization.Books.Homology.Unit13.cochainComplex_abelian C
  let _ : (CochainComplex.plus C).ContainsZero := cochainPlus_containsZero C
  let _ : ObjectProperty.IsClosedUnderKernels (CochainComplex.plus C) :=
    cochainPlus_isClosedUnderKernels C
  let _ : ObjectProperty.IsClosedUnderCokernels (CochainComplex.plus C) :=
    cochainPlus_isClosedUnderCokernels C
  let _ : ObjectProperty.IsClosedUnderFiniteProducts (CochainComplex.plus C) :=
    cochainPlus_isClosedUnderFiniteProducts C
  have hlim : PreservesFiniteLimits (CochainComplex.Plus.ι C) := by
    rw [((Functor.preservesFiniteLimits_tfae (CochainComplex.Plus.ι C)).out 3 2 :)]
    intro X Y f
    exact (CochainComplex.plus C).preservesKernels_ι f
  have hcol : PreservesFiniteColimits (CochainComplex.Plus.ι C) := by
    rw [((Functor.preservesFiniteColimits_tfae (CochainComplex.Plus.ι C)).out 3 2 :)]
    intro X Y f
    exact (CochainComplex.plus C).preservesCokernels_ι f
  let _ : PreservesFiniteLimits (CochainComplex.Plus.ι C) := hlim
  let _ : PreservesFiniteColimits (CochainComplex.Plus.ι C) := hcol
  have hι : Formalization.Books.Categories.Unit23.IsExact (CochainComplex.Plus.ι C) :=
    ⟨hlim, hcol⟩
  obtain ⟨d⟩ := Formalization.Books.Derived.Unit04.exact_precomposition_deltaFunctor
    (DerivedCategory.Q (C := C)) (canonicalDerivedDeltaFunctor C)
    (CochainComplex.Plus.ι C) hι
  let e : canonicalPlusFunctor C ⋙ DerivedCategory.Plus.ι ≅
      CochainComplex.Plus.ι C ⋙ DerivedCategory.Q (C := C) :=
    Functor.isoWhiskerLeft (HomotopyCategory.Plus.quotient C)
        (DerivedCategory.Plus.QhCompιIsoιCompQh C) ≪≫
      Functor.isoWhiskerRight (HomotopyCategory.Plus.quotientCompιIso C)
        (DerivedCategory.Qh (C := C)) ≪≫
      Functor.isoWhiskerLeft (CochainComplex.Plus.ι C)
        (DerivedCategory.quotientCompQhIso C)
  let _ : (DerivedCategory.Plus.ι (C := C)).CommShift ℤ := by
    dsimp [DerivedCategory.Plus.ι]
    infer_instance
  let _ : (CochainComplex.Plus.ι C ⋙ DerivedCategory.Q (C := C)).CommShift ℤ := by
    infer_instance
  let _ : (canonicalPlusFunctor C).CommShift ℤ :=
    Functor.CommShift.ofComp e ℤ
  let _ : NatTrans.CommShift e.hom ℤ :=
    Functor.CommShift.ofComp_compatibility e ℤ
  let delta : ∀ (S : ShortComplex (CompPlus C)) (_ : S.ShortExact),
      (canonicalPlusFunctor C).obj S.X₃ ⟶
        ((shiftFunctor (DPlus C) (1 : ℤ)).obj
          ((canonicalPlusFunctor C).obj S.X₁)) :=
    fun S hS =>
      (DerivedCategory.TStructure.t (C := C)).plus.fullyFaithfulι.preimage
        (e.hom.app S.X₃ ≫ d.delta S hS ≫
          ((shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S.X₁)) ≫
          ((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).inv.app
            ((canonicalPlusFunctor C).obj S.X₁))
  let G : DeltaFunctor (canonicalPlusFunctor C) := {
    delta := delta
    distinguished := by
      intro S hS
      apply (Functor.map_distinguished_iff (DerivedCategory.Plus.ι (C := C)) _).1
      apply isomorphic_distinguished _ (d.distinguished S hS) _
      refine Triangle.isoMk _ _ (e.app S.X₁) (e.app S.X₂) (e.app S.X₃) ?_ ?_ ?_
      · exact e.hom.naturality S.f
      · exact e.hom.naturality S.g
      · change
          ((DerivedCategory.Plus.ι (C := C)).map (delta S hS) ≫
            ((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).hom.app
              ((canonicalPlusFunctor C).obj S.X₁)) ≫
            (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.hom.app S.X₁) =
          e.hom.app S.X₃ ≫ d.delta S hS
        dsimp [delta]
        simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
        rw [← Functor.map_comp, e.inv_hom_id_app]
        have hmap :=
          (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id
            ((CochainComplex.Plus.ι C ⋙ DerivedCategory.Q (C := C)).obj S.X₁)
        rw [hmap]
        simpa only [Category.assoc] using
          (Category.comp_id (e.hom.app S.X₃ ≫ d.delta S hS))
    naturality := by
      intro S₁ S₂ φ h₁ h₂
      apply (DerivedCategory.TStructure.t (C := C)).plus.fullyFaithfulι.map_injective
      rw [← cancel_mono
        (((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).hom.app
          ((canonicalPlusFunctor C).obj S₂.X₁))]
      dsimp [delta]
      rw [show ((canonicalPlusFunctor C).map φ.τ₃).hom =
        (DerivedCategory.Plus.ι (C := C)).map
          ((canonicalPlusFunctor C).map φ.τ₃) by rfl]
      rw [show ((shiftFunctor (DPlus C) (1 : ℤ)).map
          ((canonicalPlusFunctor C).map φ.τ₁)).hom =
        (DerivedCategory.Plus.ι (C := C)).map
          ((shiftFunctor (DPlus C) (1 : ℤ)).map
            ((canonicalPlusFunctor C).map φ.τ₁)) by rfl]
      simp only [Category.assoc]
      have hnat₃ :
          (DerivedCategory.Plus.ι (C := C)).map ((canonicalPlusFunctor C).map φ.τ₃) ≫
              e.hom.app S₂.X₃ =
            e.hom.app S₁.X₃ ≫
              (CochainComplex.Plus.ι C ⋙ DerivedCategory.Q (C := C)).map φ.τ₃ := by
        exact e.hom.naturality φ.τ₃
      rw [← Category.assoc, hnat₃]
      have hshift :
          (DerivedCategory.Plus.ι (C := C)).map
              ((shiftFunctor (DPlus C) (1 : ℤ)).map
                ((canonicalPlusFunctor C).map φ.τ₁)) =
            ((shiftFunctor (DerivedCategory.Plus C) (1 : ℤ) ⋙
              DerivedCategory.Plus.ι (C := C)).map
                ((canonicalPlusFunctor C).map φ.τ₁)) := by
        rfl
      rw [hshift]
      rw [((DerivedCategory.Plus.ι (C := C)).commShiftIso (1 : ℤ)).hom.naturality
        ((canonicalPlusFunctor C).map φ.τ₁)]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
      have hid :
          (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S₂.X₁) ≫
              𝟙 ((DerivedCategory.Plus.ι (C := C) ⋙
                shiftFunctor (DerivedCategory C) (1 : ℤ)).obj
                ((canonicalPlusFunctor C).obj S₂.X₁)) =
            (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S₂.X₁) := by
        exact Category.comp_id _
      rw [hid]
      have hcomp :
          ((DerivedCategory.Plus.ι (C := C) ⋙
            shiftFunctor (DerivedCategory C) (1 : ℤ)).map
              ((canonicalPlusFunctor C).map φ.τ₁)) =
            (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
              ((DerivedCategory.Plus.ι (C := C)).map
                ((canonicalPlusFunctor C).map φ.τ₁)) := by
        rfl
      rw [hcomp]
      rw [← Functor.map_comp, ← Functor.comp_map, ← e.inv.naturality φ.τ₁]
      rw [Functor.map_comp]
      have hd :
          e.hom.app S₁.X₃ ≫
              ((CochainComplex.Plus.ι C ⋙ DerivedCategory.Q (C := C)).map φ.τ₃ ≫
                d.delta S₂ h₂) ≫
              (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S₂.X₁) =
            e.hom.app S₁.X₃ ≫
              (d.delta S₁ h₁ ≫
                (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
                  ((CochainComplex.Plus.ι C ⋙ DerivedCategory.Q (C := C)).map φ.τ₁)) ≫
              (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S₂.X₁) := by
        rw [d.naturality φ h₁ h₂]
      simpa only [Category.assoc] using hd
  }
  exact ⟨G⟩

/-- The canonical delta-functor structure on the bounded-above functor. -/
theorem canonicalMinusFunctor_isDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    Nonempty (DeltaFunctor (canonicalMinusFunctor C)) := by
  let _ : Abelian (CochainComplex C ℤ) :=
    Formalization.Books.Homology.Unit13.cochainComplex_abelian C
  let _ : (boundedAboveProperty C).ContainsZero := boundedAbove_containsZero C
  let _ : ObjectProperty.IsClosedUnderKernels (boundedAboveProperty C) :=
    boundedAbove_isClosedUnderKernels C
  let _ : ObjectProperty.IsClosedUnderCokernels (boundedAboveProperty C) :=
    boundedAbove_isClosedUnderCokernels C
  let _ : ObjectProperty.IsClosedUnderFiniteProducts (boundedAboveProperty C) :=
    boundedAbove_isClosedUnderFiniteProducts C
  have hlim : PreservesFiniteLimits ((boundedAboveProperty C).ι) := by
    rw [((Functor.preservesFiniteLimits_tfae ((boundedAboveProperty C).ι)).out 3 2 :)]
    intro X Y f
    exact (boundedAboveProperty C).preservesKernels_ι f
  have hcol : PreservesFiniteColimits ((boundedAboveProperty C).ι) := by
    rw [((Functor.preservesFiniteColimits_tfae ((boundedAboveProperty C).ι)).out 3 2 :)]
    intro X Y f
    exact (boundedAboveProperty C).preservesCokernels_ι f
  let _ : PreservesFiniteLimits ((boundedAboveProperty C).ι) := hlim
  let _ : PreservesFiniteColimits ((boundedAboveProperty C).ι) := hcol
  have hι : Formalization.Books.Categories.Unit23.IsExact ((boundedAboveProperty C).ι) :=
    ⟨hlim, hcol⟩
  obtain ⟨d⟩ := Formalization.Books.Derived.Unit04.exact_precomposition_deltaFunctor
    (DerivedCategory.Q (C := C)) (canonicalDerivedDeltaFunctor C)
    ((boundedAboveProperty C).ι) hι
  let _ : (boundedAboveProperty C).IsStableUnderShift ℤ := by
    constructor
    intro n
    refine { le_shift := ?_ }
    rintro X ⟨i, hi⟩
    letI : X.IsStrictlyLE i := hi
    exact ⟨i - n, X.isStrictlyLE_shift i n _ (by omega)⟩
  let e : canonicalMinusFunctor C ⋙ DerivedCategory.Minus.ι ≅
      (boundedAboveProperty C).ι ⋙ DerivedCategory.Q (C := C) :=
    (derivedMinusProperty C).liftCompιIso
      ((boundedAboveProperty C).ι ⋙ DerivedCategory.Q (C := C))
      (canonicalMinusFunctor_obj_mem C)
  let _ : (DerivedCategory.Minus.ι (C := C)).CommShift ℤ := by
    dsimp [DerivedCategory.Minus.ι]
    infer_instance
  let _ : ((boundedAboveProperty C).ι ⋙ DerivedCategory.Q (C := C)).CommShift ℤ := by
    infer_instance
  let _ : (canonicalMinusFunctor C).CommShift ℤ :=
    Functor.CommShift.ofComp e ℤ
  let _ : NatTrans.CommShift e.hom ℤ :=
    Functor.CommShift.ofComp_compatibility e ℤ
  let delta : ∀ (S : ShortComplex (CompMinus C)) (_ : S.ShortExact),
      (canonicalMinusFunctor C).obj S.X₃ ⟶
        ((shiftFunctor (DMinus C) (1 : ℤ)).obj
          ((canonicalMinusFunctor C).obj S.X₁)) :=
    fun S hS =>
      (DerivedCategory.TStructure.t (C := C)).minus.fullyFaithfulι.preimage
        (e.hom.app S.X₃ ≫ d.delta S hS ≫
          ((shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S.X₁)) ≫
          ((DerivedCategory.Minus.ι (C := C)).commShiftIso (1 : ℤ)).inv.app
            ((canonicalMinusFunctor C).obj S.X₁))
  let G : DeltaFunctor (canonicalMinusFunctor C) := {
    delta := delta
    distinguished := by
      intro S hS
      apply (Functor.map_distinguished_iff (DerivedCategory.Minus.ι (C := C)) _).1
      apply isomorphic_distinguished _ (d.distinguished S hS) _
      refine Triangle.isoMk _ _ (e.app S.X₁) (e.app S.X₂) (e.app S.X₃) ?_ ?_ ?_
      · exact e.hom.naturality S.f
      · exact e.hom.naturality S.g
      · change
          ((DerivedCategory.Minus.ι (C := C)).map (delta S hS) ≫
            ((DerivedCategory.Minus.ι (C := C)).commShiftIso (1 : ℤ)).hom.app
              ((canonicalMinusFunctor C).obj S.X₁)) ≫
            (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.hom.app S.X₁) =
          e.hom.app S.X₃ ≫ d.delta S hS
        dsimp [delta]
        simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
        rw [← Functor.map_comp, e.inv_hom_id_app]
        have hmap :=
          (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id
            (((boundedAboveProperty C).ι ⋙ DerivedCategory.Q (C := C)).obj S.X₁)
        rw [hmap]
        simpa only [Category.assoc] using
          (Category.comp_id (e.hom.app S.X₃ ≫ d.delta S hS))
    naturality := by
      intro S₁ S₂ φ h₁ h₂
      apply (DerivedCategory.TStructure.t (C := C)).minus.fullyFaithfulι.map_injective
      rw [← cancel_mono
        (((DerivedCategory.Minus.ι (C := C)).commShiftIso (1 : ℤ)).hom.app
          ((canonicalMinusFunctor C).obj S₂.X₁))]
      dsimp [delta]
      rw [show ((canonicalMinusFunctor C).map φ.τ₃).hom =
        (DerivedCategory.Minus.ι (C := C)).map
          ((canonicalMinusFunctor C).map φ.τ₃) by rfl]
      rw [show ((shiftFunctor (DMinus C) (1 : ℤ)).map
          ((canonicalMinusFunctor C).map φ.τ₁)).hom =
        (DerivedCategory.Minus.ι (C := C)).map
          ((shiftFunctor (DMinus C) (1 : ℤ)).map
            ((canonicalMinusFunctor C).map φ.τ₁)) by rfl]
      simp only [Category.assoc]
      have hnat₃ :
          (DerivedCategory.Minus.ι (C := C)).map ((canonicalMinusFunctor C).map φ.τ₃) ≫
              e.hom.app S₂.X₃ =
            e.hom.app S₁.X₃ ≫
              ((boundedAboveProperty C).ι ⋙ DerivedCategory.Q (C := C)).map φ.τ₃ := by
        exact e.hom.naturality φ.τ₃
      rw [← Category.assoc, hnat₃]
      have hshift :
          (DerivedCategory.Minus.ι (C := C)).map
              ((shiftFunctor (DMinus C) (1 : ℤ)).map
                ((canonicalMinusFunctor C).map φ.τ₁)) =
            ((shiftFunctor (DMinus C) (1 : ℤ) ⋙
              DerivedCategory.Minus.ι (C := C)).map
                ((canonicalMinusFunctor C).map φ.τ₁)) := by
        rfl
      rw [hshift]
      rw [((DerivedCategory.Minus.ι (C := C)).commShiftIso (1 : ℤ)).hom.naturality
        ((canonicalMinusFunctor C).map φ.τ₁)]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
      have hid :
          (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S₂.X₁) ≫
              𝟙 ((DerivedCategory.Minus.ι (C := C) ⋙
                shiftFunctor (DerivedCategory C) (1 : ℤ)).obj
                ((canonicalMinusFunctor C).obj S₂.X₁)) =
            (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S₂.X₁) := by
        exact Category.comp_id _
      rw [hid]
      have hcomp :
          ((DerivedCategory.Minus.ι (C := C) ⋙
            shiftFunctor (DerivedCategory C) (1 : ℤ)).map
              ((canonicalMinusFunctor C).map φ.τ₁)) =
            (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
              ((DerivedCategory.Minus.ι (C := C)).map
                ((canonicalMinusFunctor C).map φ.τ₁)) := by
        rfl
      rw [hcomp]
      rw [← Functor.map_comp, ← Functor.comp_map, ← e.inv.naturality φ.τ₁]
      rw [Functor.map_comp]
      have hd :
          e.hom.app S₁.X₃ ≫
              (((boundedAboveProperty C).ι ⋙ DerivedCategory.Q (C := C)).map φ.τ₃ ≫
                d.delta S₂ h₂) ≫
              (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S₂.X₁) =
            e.hom.app S₁.X₃ ≫
              (d.delta S₁ h₁ ≫
                (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
                  (((boundedAboveProperty C).ι ⋙ DerivedCategory.Q (C := C)).map φ.τ₁)) ≫
              (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S₂.X₁) := by
        rw [d.naturality φ h₁ h₂]
      simpa only [Category.assoc] using hd
  }
  exact ⟨G⟩

/-- The canonical delta-functor structure on the bounded functor. -/
theorem canonicalBoundedFunctor_isDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    Nonempty (DeltaFunctor (canonicalBoundedFunctor C)) := by
  let _ : Abelian (CochainComplex C ℤ) :=
    Formalization.Books.Homology.Unit13.cochainComplex_abelian C
  let _ : (boundedProperty C).ContainsZero := bounded_containsZero C
  let _ : ObjectProperty.IsClosedUnderKernels (boundedProperty C) :=
    bounded_isClosedUnderKernels C
  let _ : ObjectProperty.IsClosedUnderCokernels (boundedProperty C) :=
    bounded_isClosedUnderCokernels C
  let _ : ObjectProperty.IsClosedUnderFiniteProducts (boundedProperty C) :=
    bounded_isClosedUnderFiniteProducts C
  have hlim : PreservesFiniteLimits ((boundedProperty C).ι) := by
    rw [((Functor.preservesFiniteLimits_tfae ((boundedProperty C).ι)).out 3 2 :)]
    intro X Y f
    exact (boundedProperty C).preservesKernels_ι f
  have hcol : PreservesFiniteColimits ((boundedProperty C).ι) := by
    rw [((Functor.preservesFiniteColimits_tfae ((boundedProperty C).ι)).out 3 2 :)]
    intro X Y f
    exact (boundedProperty C).preservesCokernels_ι f
  let _ : PreservesFiniteLimits ((boundedProperty C).ι) := hlim
  let _ : PreservesFiniteColimits ((boundedProperty C).ι) := hcol
  have hι : Formalization.Books.Categories.Unit23.IsExact ((boundedProperty C).ι) :=
    ⟨hlim, hcol⟩
  obtain ⟨d⟩ := Formalization.Books.Derived.Unit04.exact_precomposition_deltaFunctor
    (DerivedCategory.Q (C := C)) (canonicalDerivedDeltaFunctor C)
    ((boundedProperty C).ι) hι
  let _ : (boundedProperty C).IsStableUnderShift ℤ := by
    constructor
    intro n
    refine { le_shift := ?_ }
    rintro X ⟨p, q, hp, hq⟩
    letI : X.IsStrictlyGE p := hp
    letI : X.IsStrictlyLE q := hq
    exact ⟨p - n, q - n, X.isStrictlyGE_shift p n _ (by omega),
      X.isStrictlyLE_shift q n _ (by omega)⟩
  let e : canonicalBoundedFunctor C ⋙ DerivedCategory.Bounded.ι ≅
      (boundedProperty C).ι ⋙ DerivedCategory.Q (C := C) :=
    (derivedBoundedProperty C).liftCompιIso
      ((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C))
      (canonicalBoundedFunctor_obj_mem C)
  let _ : (DerivedCategory.Bounded.ι (C := C)).CommShift ℤ := by
    dsimp [DerivedCategory.Bounded.ι]
    infer_instance
  let _ : ((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C)).CommShift ℤ := by
    infer_instance
  let _ : (canonicalBoundedFunctor C).CommShift ℤ :=
    Functor.CommShift.ofComp e ℤ
  let _ : NatTrans.CommShift e.hom ℤ :=
    Functor.CommShift.ofComp_compatibility e ℤ
  let delta : ∀ (S : ShortComplex (CompBounded C)) (_ : S.ShortExact),
      (canonicalBoundedFunctor C).obj S.X₃ ⟶
        ((shiftFunctor (DBounded C) (1 : ℤ)).obj
          ((canonicalBoundedFunctor C).obj S.X₁)) :=
    fun S hS =>
      (DerivedCategory.TStructure.t (C := C)).bounded.fullyFaithfulι.preimage
        (e.hom.app S.X₃ ≫ d.delta S hS ≫
          ((shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S.X₁)) ≫
          ((DerivedCategory.Bounded.ι (C := C)).commShiftIso (1 : ℤ)).inv.app
            ((canonicalBoundedFunctor C).obj S.X₁))
  let G : DeltaFunctor (canonicalBoundedFunctor C) := {
    delta := delta
    distinguished := by
      intro S hS
      apply (Functor.map_distinguished_iff (DerivedCategory.Bounded.ι (C := C)) _).1
      apply isomorphic_distinguished _ (d.distinguished S hS) _
      refine Triangle.isoMk _ _ (e.app S.X₁) (e.app S.X₂) (e.app S.X₃) ?_ ?_ ?_
      · exact e.hom.naturality S.f
      · exact e.hom.naturality S.g
      · change
          ((DerivedCategory.Bounded.ι (C := C)).map (delta S hS) ≫
            ((DerivedCategory.Bounded.ι (C := C)).commShiftIso (1 : ℤ)).hom.app
              ((canonicalBoundedFunctor C).obj S.X₁)) ≫
            (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.hom.app S.X₁) =
          e.hom.app S.X₃ ≫ d.delta S hS
        dsimp [delta]
        simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
        rw [← Functor.map_comp, e.inv_hom_id_app]
        have hmap :=
          (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id
            (((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C)).obj S.X₁)
        rw [hmap]
        simpa only [Category.assoc] using
          (Category.comp_id (e.hom.app S.X₃ ≫ d.delta S hS))
    naturality := by
      intro S₁ S₂ φ h₁ h₂
      apply (DerivedCategory.TStructure.t (C := C)).bounded.fullyFaithfulι.map_injective
      rw [← cancel_mono
        (((DerivedCategory.Bounded.ι (C := C)).commShiftIso (1 : ℤ)).hom.app
          ((canonicalBoundedFunctor C).obj S₂.X₁))]
      dsimp [delta]
      rw [show ((canonicalBoundedFunctor C).map φ.τ₃).hom =
        (DerivedCategory.Bounded.ι (C := C)).map
          ((canonicalBoundedFunctor C).map φ.τ₃) by rfl]
      rw [show ((shiftFunctor (DBounded C) (1 : ℤ)).map
          ((canonicalBoundedFunctor C).map φ.τ₁)).hom =
        (DerivedCategory.Bounded.ι (C := C)).map
          ((shiftFunctor (DBounded C) (1 : ℤ)).map
            ((canonicalBoundedFunctor C).map φ.τ₁)) by rfl]
      simp only [Category.assoc]
      have hnat₃ :
          (DerivedCategory.Bounded.ι (C := C)).map ((canonicalBoundedFunctor C).map φ.τ₃) ≫
              e.hom.app S₂.X₃ =
            e.hom.app S₁.X₃ ≫
              ((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C)).map φ.τ₃ := by
        exact e.hom.naturality φ.τ₃
      rw [← Category.assoc, hnat₃]
      have hshift :
          (DerivedCategory.Bounded.ι (C := C)).map
              ((shiftFunctor (DBounded C) (1 : ℤ)).map
                ((canonicalBoundedFunctor C).map φ.τ₁)) =
            ((shiftFunctor (DBounded C) (1 : ℤ) ⋙
              DerivedCategory.Bounded.ι (C := C)).map
                ((canonicalBoundedFunctor C).map φ.τ₁)) := by
        rfl
      rw [hshift]
      rw [((DerivedCategory.Bounded.ι (C := C)).commShiftIso (1 : ℤ)).hom.naturality
        ((canonicalBoundedFunctor C).map φ.τ₁)]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
      have hid :
          (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S₂.X₁) ≫
              𝟙 ((DerivedCategory.Bounded.ι (C := C) ⋙
                shiftFunctor (DerivedCategory C) (1 : ℤ)).obj
                ((canonicalBoundedFunctor C).obj S₂.X₁)) =
            (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S₂.X₁) := by
        exact Category.comp_id _
      rw [hid]
      have hcomp :
          ((DerivedCategory.Bounded.ι (C := C) ⋙
            shiftFunctor (DerivedCategory C) (1 : ℤ)).map
              ((canonicalBoundedFunctor C).map φ.τ₁)) =
            (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
              ((DerivedCategory.Bounded.ι (C := C)).map
                ((canonicalBoundedFunctor C).map φ.τ₁)) := by
        rfl
      rw [hcomp]
      rw [← Functor.map_comp, ← Functor.comp_map, ← e.inv.naturality φ.τ₁]
      rw [Functor.map_comp]
      have hd :
          e.hom.app S₁.X₃ ≫
              (((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C)).map φ.τ₃ ≫
                d.delta S₂ h₂) ≫
              (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S₂.X₁) =
            e.hom.app S₁.X₃ ≫
              (d.delta S₁ h₁ ≫
                (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
                  (((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C)).map φ.τ₁)) ≫
              (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (e.inv.app S₂.X₁) := by
        rw [d.naturality φ h₁ h₂]
      simpa only [Category.assoc] using hd
  }
  exact ⟨G⟩

noncomputable def canonicalPlusDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    DeltaFunctor (canonicalPlusFunctor C) :=
  Classical.choice (canonicalPlusFunctor_isDeltaFunctor C)

noncomputable def canonicalMinusDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    DeltaFunctor (canonicalMinusFunctor C) :=
  Classical.choice (canonicalMinusFunctor_isDeltaFunctor C)

noncomputable def canonicalBoundedDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    DeltaFunctor (canonicalBoundedFunctor C) :=
  Classical.choice (canonicalBoundedFunctor_isDeltaFunctor C)

/-! ## Comparison triangles -/

/-- The morphism of canonical derived triangles induced by a morphism of short
exact sequences. -/
noncomputable def canonicalDerivedTriangleMap
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    canonicalDerivedTriangle h₁ ⟶ canonicalDerivedTriangle h₂ :=
  let e₁ : canonicalDerivedTriangle h₁ = DerivedCategory.triangleOfSES h₁ := by
    dsimp [canonicalDerivedTriangle, DerivedCategory.triangleOfSES]
    rw [canonicalDerivedDelta_eq_triangleOfSESδ h₁]
  let e₂ : canonicalDerivedTriangle h₂ = DerivedCategory.triangleOfSES h₂ := by
    dsimp [canonicalDerivedTriangle, DerivedCategory.triangleOfSES]
    rw [canonicalDerivedDelta_eq_triangleOfSESδ h₂]
  eqToHom e₁ ≫ DerivedCategory.triangleOfSES.map h₁ h₂ φ ≫ eqToHom e₂.symm

/-- If all three vertical maps of short exact sequences are quasi-isomorphisms,
then the induced triangle map is an isomorphism. -/
theorem canonicalDerivedTriangleMap_isIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (hφ₁ : QuasiIso φ.τ₁) (hφ₂ : QuasiIso φ.τ₂) (hφ₃ : QuasiIso φ.τ₃) :
    IsIso (canonicalDerivedTriangleMap h₁ h₂ φ) := by
  let t : DerivedCategory.triangleOfSES h₁ ⟶
      DerivedCategory.triangleOfSES h₂ :=
    DerivedCategory.triangleOfSES.map h₁ h₂ φ
  haveI : IsIso t.hom₂ := by
    change IsIso (DerivedCategory.Q.map φ.τ₂)
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hφ₂
  haveI : IsIso t.hom₃ := by
    change IsIso (DerivedCategory.Q.map φ.τ₃)
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hφ₃
  haveI : IsIso t.hom₁ := by
    change IsIso (DerivedCategory.Q.map φ.τ₁)
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hφ₁
  dsimp [canonicalDerivedTriangleMap]
  apply Triangle.isIso_of_isIsos
  · change IsIso (_ ≫ _ ≫ _)
    infer_instance
  · change IsIso (_ ≫ _ ≫ _)
    infer_instance
  · change IsIso (_ ≫ _ ≫ _)
    infer_instance

noncomputable def canonicalDerivedTriangleMapIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (hφ₁ : QuasiIso φ.τ₁) (hφ₂ : QuasiIso φ.τ₂) (hφ₃ : QuasiIso φ.τ₃) :
    canonicalDerivedTriangle h₁ ≅ canonicalDerivedTriangle h₂ := by
  letI : IsIso (canonicalDerivedTriangleMap h₁ h₂ φ) :=
    canonicalDerivedTriangleMap_isIso h₁ h₂ φ hφ₁ hφ₂ hφ₃
  exact asIso (canonicalDerivedTriangleMap h₁ h₂ φ)

/-- The cone triangle and the canonical triangle agree for a termwise split
short exact sequence, after passage to the derived category. -/
theorem canonicalDerivedTriangle_termwiseSplit_comparison
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B D : Formalization.Books.Derived.Unit09.BookComplex C}
    (S : TermwiseSplitExactSequence A B D) :
    Nonempty
      (canonicalDerivedTriangle
          (termwiseSplitShortComplex_shortExact C S) ≅
        (DerivedCategory.Q (C := C)).mapTriangle.obj
          (termwiseSplitTriangle S)) := by
  obtain ⟨e, _, _⟩ := same_up_to_isomorphisms_of_termwise_split S
  let q : Formalization.Books.Derived.Unit09.BookComplex C ⥤
      Formalization.Books.Derived.Unit09.BookHomotopyCategory C :=
    HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let eq : (DerivedCategory.Q (C := C)).mapTriangle.obj
      (CochainComplex.mappingCone.triangle S.f) ≅
      (DerivedCategory.Q (C := C)).mapTriangle.obj (termwiseSplitTriangle S) :=
    (Functor.mapTriangleIso (DerivedCategory.quotientCompQhIso C)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso q (DerivedCategory.Qh (C := C))).app _ ≪≫
      (DerivedCategory.Qh (C := C)).mapTriangle.mapIso e ≪≫
      (Functor.mapTriangleCompIso q (DerivedCategory.Qh (C := C))).symm.app _ ≪≫
      (Functor.mapTriangleIso (DerivedCategory.quotientCompQhIso C)).app _
  exact ⟨canonicalDerivedTriangleIsoCone (termwiseSplitShortComplex_shortExact C S) ≪≫ eq⟩

/-- The same comparison stated with the termwise-split triangle in the
homotopy category, followed by the derived localization. -/
theorem canonicalDerivedTriangle_termwiseSplit_K_comparison
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B D : Formalization.Books.Derived.Unit09.BookComplex C}
    (S : TermwiseSplitExactSequence A B D) :
    Nonempty
      (canonicalDerivedTriangle
          (termwiseSplitShortComplex_shortExact C S) ≅
        (DerivedCategory.Qh (C := C)).mapTriangle.obj
          (termwiseSplitTriangleh S)) := by
  obtain ⟨e, _, _⟩ := same_up_to_isomorphisms_of_termwise_split S
  let q : Formalization.Books.Derived.Unit09.BookComplex C ⥤
      Formalization.Books.Derived.Unit09.BookHomotopyCategory C :=
    HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let eq : (DerivedCategory.Q (C := C)).mapTriangle.obj
      (CochainComplex.mappingCone.triangle S.f) ≅
      (DerivedCategory.Qh (C := C)).mapTriangle.obj (termwiseSplitTriangleh S) :=
    (Functor.mapTriangleIso (DerivedCategory.quotientCompQhIso C)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso q (DerivedCategory.Qh (C := C))).app _ ≪≫
      (DerivedCategory.Qh (C := C)).mapTriangle.mapIso e
  exact ⟨canonicalDerivedTriangleIsoCone (termwiseSplitShortComplex_shortExact C S) ≪≫ eq⟩

/-! ## Truncation triangles -/

/-- The canonical t-structure used for all truncation statements. -/
abbrev canonicalTStructure
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    CategoryTheory.Triangulated.TStructure (DerivedCategory C) :=
  DerivedCategory.TStructure.t

/-- The source cohomology piece H^n(K)[-n], using the derived single functor
and the canonical derived homology functor. -/
noncomputable def canonicalCohomologyPiece
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (n : ℤ) : DerivedCategory C :=
  (DerivedCategory.singleFunctor C n).obj
    ((DerivedCategory.homologyFunctor C n).obj
      ((DerivedCategory.Q (C := C)).obj K))

/-- The truncation triangle built from the short exact truncation sequence and
the quotient-to-upper-truncation quasi-isomorphism. -/
noncomputable def canonicalTruncationTriangle
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) : Triangle (DerivedCategory C) :=
  let h := K.shortComplexTruncLE_shortExact a
  let e := K.shortComplexTruncLEX₃ToTruncGE a (a + 1) (by lia)
  Triangle.mk
    (DerivedCategory.Q.map (K.ιTruncLE a))
    (DerivedCategory.Q.map (K.πTruncGE (a + 1)))
    (inv (DerivedCategory.Q.map e) ≫
      (DerivedCategory.triangleOfSES h).mor₃)

theorem canonicalTruncationTriangle_distinguished
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    canonicalTruncationTriangle C K a ∈ distTriang (DerivedCategory C) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  exact (by
    let h := K.shortComplexTruncLE_shortExact a
    let e := K.shortComplexTruncLEX₃ToTruncGE a (a + 1) (by lia)
    refine isomorphic_distinguished (DerivedCategory.triangleOfSES h)
      (DerivedCategory.triangleOfSES_distinguished h)
      (canonicalTruncationTriangle C K a) (Iso.symm ?_)
    refine Triangle.isoMk _ _ (eqToIso rfl) (eqToIso rfl)
      (asIso (DerivedCategory.Q.map e)) ?_ ?_ ?_
    · dsimp [canonicalTruncationTriangle]
      simp only [Category.comp_id, Category.id_comp]
      rfl
    · dsimp [canonicalTruncationTriangle]
      simp only [Category.id_comp]
      change DerivedCategory.Q.map ((K.shortComplexTruncLE a).g) ≫
          DerivedCategory.Q.map e =
        DerivedCategory.Q.map (K.πTruncGE (a + 1))
      rw [← DerivedCategory.Q.map_comp]
      have hg :
          (K.shortComplexTruncLE a).g ≫ e = K.πTruncGE (a + 1) := by
        apply CochainComplex.g_shortComplexTruncLEX₃ToTruncGE
      rw [hg]
    · dsimp [canonicalTruncationTriangle]
      simp only [(shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id,
        Category.comp_id]
      rw [← Category.assoc]
      simp)

/-- The direct short-exact construction agrees with the canonical t-structure
truncation triangle. -/
theorem canonicalTruncationTriangle_isomorphic_to_tStructure
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      (canonicalTruncationTriangle C K a ≅
        ((canonicalTStructure C).triangleLEGE a (a + 1) rfl).obj
          ((DerivedCategory.Q (C := C)).obj K)) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  exact (by
    obtain ⟨e, _⟩ := (canonicalTStructure C).triangle_iso_exists
      (canonicalTruncationTriangle_distinguished C K a)
      ((canonicalTStructure C).triangleLEGE_distinguished a (a + 1) rfl _)
      (Iso.refl _) a (a + 1)
      (by
        change ((DerivedCategory.Q (C := C)).obj (K.truncLE a)).IsLE a
        rw [DerivedCategory.isLE_Q_obj_iff]
        infer_instance)
      (by
        change ((DerivedCategory.Q (C := C)).obj (K.truncGE (a + 1))).IsGE (a + 1)
        rw [DerivedCategory.isGE_Q_obj_iff]
        infer_instance)
      (by
        change (canonicalTStructure C).IsLE
          (((canonicalTStructure C).truncLE a).obj
            ((DerivedCategory.Q (C := C)).obj K)) a
        infer_instance)
      (by
        change (canonicalTStructure C).IsGE
          (((canonicalTStructure C).truncGE (a + 1)).obj
            ((DerivedCategory.Q (C := C)).obj K)) (a + 1)
        infer_instance)
    exact ⟨e⟩)

private noncomputable def singleFunctorCompHomologyFunctorIso'
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (n : ℤ) :
    DerivedCategory.singleFunctor C n ⋙ DerivedCategory.homologyFunctor C n ≅
      𝟭 C :=
  Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ C n) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors C n) ≪≫
      HomologicalComplex.homologyFunctorSingleIso C (ComplexShape.up ℤ) n

private theorem isIso_derived_homology_map_of_quasiIsoAt
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ)
    (hf : QuasiIsoAt f n) :
    IsIso ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.Q (C := C)).map f)) := by
  have hhom : IsIso (HomologicalComplex.homologyMap f n) :=
    (quasiIsoAt_iff_isIso_homologyMap f n).1 hf
  letI : IsIso (HomologicalComplex.homologyMap f n) := hhom
  letI : IsIso ((DerivedCategory.homologyFunctorFactors C n).hom.app K) := by
    infer_instance
  letI : IsIso
      ((DerivedCategory.homologyFunctor C n).map
        ((DerivedCategory.Q (C := C)).map f) ≫
          (DerivedCategory.homologyFunctorFactors C n).hom.app L) := by
    rw [DerivedCategory.homologyFunctorFactors_hom_naturality]
    exact
      (asIso ((DerivedCategory.homologyFunctorFactors C n).hom.app K) ≪≫
        (@asIso _ _ _ _ (HomologicalComplex.homologyMap f n) hhom)).isIso_hom
  exact IsIso.of_isIso_comp_right
    ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.Q (C := C)).map f))
    ((DerivedCategory.homologyFunctorFactors C n).hom.app L)

private theorem concreteHeartTruncation_iso_canonicalCohomologyPiece
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (n : ℤ) :
    Nonempty
      ((DerivedCategory.Q (C := C)).obj ((K.truncGE n).truncLE n) ≅
        canonicalCohomologyPiece C K n) := by
  let L := K.truncGE n
  let M := L.truncLE n
  have hK : QuasiIsoAt (K.πTruncGE n) n := by infer_instance
  have hM : QuasiIsoAt (L.ιTruncLE n) n := by infer_instance
  have hK' := isIso_derived_homology_map_of_quasiIsoAt C (K.πTruncGE n) n hK
  have hM' := isIso_derived_homology_map_of_quasiIsoAt C (L.ιTruncLE n) n hM
  have hGE : ((DerivedCategory.Q (C := C)).obj M).IsGE n := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    dsimp [M, L]
    infer_instance
  have hLE : ((DerivedCategory.Q (C := C)).obj M).IsLE n := by
    rw [DerivedCategory.isLE_Q_obj_iff]
    dsimp [M, L]
    infer_instance
  obtain ⟨Y, ⟨e⟩⟩ :=
    @DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE C _ _ _
      ((DerivedCategory.Q (C := C)).obj M) n hGE hLE
  let eMY : (DerivedCategory.homologyFunctor C n).obj
      ((DerivedCategory.Q (C := C)).obj M) ≅ Y :=
    (DerivedCategory.homologyFunctor C n).mapIso e ≪≫
      (singleFunctorCompHomologyFunctorIso' C n).app Y
  let eYK : Y ≅ (DerivedCategory.homologyFunctor C n).obj
      ((DerivedCategory.Q (C := C)).obj K) :=
    eMY.symm ≪≫
      (@asIso _ _ _ _
        ((DerivedCategory.homologyFunctor C n).map
          ((DerivedCategory.Q (C := C)).map (L.ιTruncLE n))) hM') ≪≫
      (@asIso _ _ _ _
        ((DerivedCategory.homologyFunctor C n).map
          ((DerivedCategory.Q (C := C)).map (K.πTruncGE n))) hK').symm
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor C n).mapIso eYK⟩

private theorem canonicalHeartTruncation_iso_canonicalCohomologyPiece
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (n : ℤ) :
    Nonempty
      (((canonicalTStructure C).truncLEGE n n).obj
          ((DerivedCategory.Q (C := C)).obj K) ≅
        canonicalCohomologyPiece C K n) := by
  obtain ⟨eK⟩ := canonicalTruncationTriangle_isomorphic_to_tStructure C K (n - 1)
  obtain ⟨eL⟩ := canonicalTruncationTriangle_isomorphic_to_tStructure C
    (K.truncGE n) n
  have hn : n - 1 + 1 = n := by lia
  have hobj : (canonicalTruncationTriangle C K (n - 1)).obj₃ =
      (DerivedCategory.Q (C := C)).obj (K.truncGE (n - 1 + 1)) := by
    dsimp [canonicalTruncationTriangle, Triangle.mk]
  let eG₀ : (canonicalTruncationTriangle C K (n - 1)).obj₃ ≅
      (((canonicalTStructure C).triangleLEGE (n - 1) (n - 1 + 1) rfl).obj
        ((DerivedCategory.Q (C := C)).obj K)).obj₃ := by
    exact Triangle.π₃.mapIso eK
  have hobj' : (canonicalTruncationTriangle C K (n - 1)).obj₃ =
      (DerivedCategory.Q (C := C)).obj (K.truncGE n) := by
    simpa [hn] using hobj
  let eG : (DerivedCategory.Q (C := C)).obj (K.truncGE n) ≅
      ((canonicalTStructure C).truncGE n).obj
        ((DerivedCategory.Q (C := C)).obj K) :=
    by simpa [hn] using (eqToIso hobj'.symm ≪≫ eG₀)
  let eM : (DerivedCategory.Q (C := C)).obj ((K.truncGE n).truncLE n) ≅
      ((canonicalTStructure C).truncLE n).obj
        ((DerivedCategory.Q (C := C)).obj (K.truncGE n)) :=
    Triangle.π₁.mapIso eL
  obtain ⟨eH⟩ := concreteHeartTruncation_iso_canonicalCohomologyPiece C K n
  exact ⟨(((canonicalTStructure C).truncLE n).mapIso eG).symm ≪≫
    eM.symm ≪≫ eH⟩

/-- The lower truncation step triangle, whose third object is the cohomology
piece in degree a + 1. -/
noncomputable def lowerTruncationStepTriangle
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) : Triangle (DerivedCategory C) :=
  ((canonicalTStructure C).triangleLEGE a (a + 1) rfl).obj
    (((canonicalTStructure C).truncLE (a + 1)).obj
      ((DerivedCategory.Q (C := C)).obj K))

theorem lowerTruncationStepTriangle_distinguished
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    lowerTruncationStepTriangle C K a ∈ distTriang (DerivedCategory C) :=
  (canonicalTStructure C).triangleLEGE_distinguished a (a + 1) rfl _

theorem lowerTruncationStepTriangle_third_is_cohomologyPiece
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      ((lowerTruncationStepTriangle C K a).obj₃ ≅
        canonicalCohomologyPiece C K (a + 1)) := by
  dsimp [lowerTruncationStepTriangle]
  obtain ⟨e⟩ := canonicalHeartTruncation_iso_canonicalCohomologyPiece C K (a + 1)
  exact ⟨((canonicalTStructure C).truncGELEIsoLEGE (a + 1) (a + 1)).app
    ((DerivedCategory.Q (C := C)).obj K) ≪≫ e⟩

theorem lowerTruncationStepTriangle_first_is_lowerTruncation
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      ((lowerTruncationStepTriangle C K a).obj₁ ≅
        ((canonicalTStructure C).truncLE a).obj
          ((DerivedCategory.Q (C := C)).obj K)) := by
  dsimp [lowerTruncationStepTriangle]
  exact ⟨@asIso _ _ _ _
    (((canonicalTStructure C).truncLE a).map
      (((canonicalTStructure C).truncLEι (a + 1)).app
        ((DerivedCategory.Q (C := C)).obj K)))
    (CategoryTheory.Triangulated.TStructure.isIso_truncLE_map_truncLEι_app
      (canonicalTStructure C) a (a + 1) (by lia)
        ((DerivedCategory.Q (C := C)).obj K))⟩

theorem lowerTruncationStepTriangle_second_is_nextLowerTruncation
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      ((lowerTruncationStepTriangle C K a).obj₂ ≅
        ((canonicalTStructure C).truncLE (a + 1)).obj
          ((DerivedCategory.Q (C := C)).obj K)) := by
  exact ⟨Iso.refl _⟩

/-- The upper truncation step triangle, whose first object is the cohomology
piece in degree a. -/
noncomputable def upperTruncationStepTriangle
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) : Triangle (DerivedCategory C) :=
  ((canonicalTStructure C).triangleLEGE a (a + 1) rfl).obj
    (((canonicalTStructure C).truncGE a).obj
      ((DerivedCategory.Q (C := C)).obj K))

theorem upperTruncationStepTriangle_distinguished
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    upperTruncationStepTriangle C K a ∈ distTriang (DerivedCategory C) :=
  (canonicalTStructure C).triangleLEGE_distinguished a (a + 1) rfl _

theorem upperTruncationStepTriangle_first_is_cohomologyPiece
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      ((upperTruncationStepTriangle C K a).obj₁ ≅
        canonicalCohomologyPiece C K a) := by
  dsimp [upperTruncationStepTriangle]
  exact canonicalHeartTruncation_iso_canonicalCohomologyPiece C K a

theorem upperTruncationStepTriangle_second_is_upperTruncation
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      ((upperTruncationStepTriangle C K a).obj₂ ≅
        ((canonicalTStructure C).truncGE a).obj
          ((DerivedCategory.Q (C := C)).obj K)) := by
  exact ⟨Iso.refl _⟩

theorem upperTruncationStepTriangle_third_is_nextUpperTruncation
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      ((upperTruncationStepTriangle C K a).obj₃ ≅
        ((canonicalTStructure C).truncGE (a + 1)).obj
          ((DerivedCategory.Q (C := C)).obj K)) := by
  sorry

/-! ## Vanishing compositions and truncation factorization -/

/-- The map of the reverse-indexed adjacent arrow K_{j+1} to K_j in a chain
written from K_n on the left to K_0 on the right. -/
def reverseAdjacentMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {n : ℕ} (F : ComposableArrows (CochainComplex C ℤ) n) (j : Fin n) :
    F.obj ⟨n - j.val - 1, by omega⟩ ⟶
      F.obj ⟨n - j.val, by omega⟩ :=
  F.map (homOfLE (by simp only [Fin.mk_le_mk]; omega))

/-- If H^i(K_0)=0 for i>0 and the maps on H^{-j} vanish, the composite
K_0 to K_n factors through tau<=-n K_n in the derived category. -/
theorem vanishingComposition_factorization
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {n : ℕ} (F : ComposableArrows (CochainComplex C ℤ) n)
    (h₀ : ∀ i : ℤ, 0 < i → IsZero (F.left.homology i))
    (h₁ : ∀ j : Fin n,
      HomologicalComplex.homologyMap (adjacentMap F j) (-(j.val : ℤ)) = 0) :
    ∃ u : (DerivedCategory.Q (C := C)).obj F.left ⟶
        (DerivedCategory.Q (C := C)).obj (F.right.truncLE (-(n : ℤ))),
      u ≫ DerivedCategory.Q.map (F.right.ιTruncLE (-(n : ℤ))) =
        DerivedCategory.Q.map F.hom := by
  sorry

/-- Dually, for a reverse-indexed chain with H^i(K_0)=0 for i<0 and
vanishing maps on H^j, the composite factors through tau>=n K_n. -/
theorem vanishingComposition_factorization_dual
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {n : ℕ} (F : ComposableArrows (CochainComplex C ℤ) n)
    (h₀ : ∀ i : ℤ, i < 0 → IsZero (F.right.homology i))
    (h₁ : ∀ j : Fin n,
      HomologicalComplex.homologyMap (reverseAdjacentMap F j) (j.val : ℤ) = 0) :
    ∃ u : (DerivedCategory.Q (C := C)).obj (F.left.truncGE (n : ℤ)) ⟶
        (DerivedCategory.Q (C := C)).obj F.right,
      DerivedCategory.Q.map (F.left.πTruncGE (n : ℤ)) ≫ u =
        DerivedCategory.Q.map F.hom := by
  sorry

end Formalization.Books.Derived.Unit12
