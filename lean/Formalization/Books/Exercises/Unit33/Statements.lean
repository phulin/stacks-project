import Formalization.Books.Exercises.Unit33.Core
import Formalization.Books.Modules.Unit10.QuasiCoherent
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ULift

/-!
# Exercises, Chapter 33: Schemes

The declarations below record the source's definition, remarks, and fourteen
numbered exercises in source order.  Proofs are deferred to the proving
stage; all example requests retain their mathematical data and exclusions.
-/

namespace Formalization.Books.Exercises.Unit33

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Opposite TopologicalSpace

universe u

noncomputable section

/-! ## Exercises `exercise-one-point` through `exercise-three-points` -/

/-- A one-point locally ringed space need not satisfy the local affine-cover
condition for schemes. -/
theorem exists_one_point_locallyRingedSpace_not_scheme :
    ∃ X : LocallyRingedSpace.{u},
      (∃ x : X, ∀ y : X, y = x) ∧ ¬ IsSchemeLocallyRingedSpace X := by
  let R := ULift.{u} (PowerSeries ℚ)
  letI : IsLocalRing R :=
    (ULift.ringEquiv.symm : PowerSeries ℚ ≃+* R).isLocalRing
  let Y : TopCat.{u} := TopCat.of (ULift.{u, 0} Unit)
  let G : Y.Presheaf CommRingCat :=
    (Functor.const (Opens Y)ᵒᵖ).obj (CommRingCat.of R)
  let F :=
    (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology Y) CommRingCat).obj G
  let X : LocallyRingedSpace.{u} :=
    { carrier := Y
      presheaf := F.1
      IsSheaf := F.2
      isLocalRing := fun x => by
        letI : ∀ (i j : (OpenNhds x)ᵒᵖ) (f : i ⟶ j),
            IsIso (((OpenNhds.inclusion x).op ⋙ G).map f) := by
          intro i j f
          dsimp [G]
          infer_instance
        let eG : (TopCat.Presheaf.stalkFunctor CommRingCat x).obj G ≅
            CommRingCat.of R :=
          colimitOfInitial ((OpenNhds.inclusion x).op ⋙ G)
        letI : IsLocalRing ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj G) :=
          eG.symm.commRingCatIsoToRingEquiv.isLocalRing
        letI : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
            (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) G)) :=
          TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
            (X := Y) x CommRingCat G
        let eF : (TopCat.Presheaf.stalkFunctor CommRingCat x).obj G ≅
            (TopCat.Presheaf.stalkFunctor CommRingCat x).obj F.1 :=
          (asIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
            (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) G)))
        exact eF.commRingCatIsoToRingEquiv.isLocalRing }
  let p : X := ULift.up ()
  let hpoint : ∀ y : X, y = p := by
    intro y
    cases y with
    | up z => cases z; rfl
  refine ⟨X, ⟨p, hpoint⟩, ?_⟩
  intro hX
  rcases hX p with ⟨U, hU, hUaff⟩
  have hUtop : U = (⊤ : Opens X) := by
    ext z
    constructor
    · intro hz
      trivial
    · intro hz
      cases z with
      | up z => cases z; exact hU
  rw [hUtop] at hUaff
  rcases hUaff with ⟨S, ⟨e⟩⟩
  let eX : X ≅ (Spec S).toLocallyRingedSpace :=
    X.restrictTopIso.symm ≪≫ e
  have hSsub : ∀ a b : PrimeSpectrum S, a = b := by
    intro a b
    have hab : eX.inv.base a = eX.inv.base b :=
      (hpoint (eX.inv.base a)).trans (hpoint (eX.inv.base b)).symm
    have ha : eX.hom.base (eX.inv.base a) = a := by
      have h := congrArg (fun f => f.base) eX.inv_hom_id
      exact congrArg (fun f => f a) h
    have hb : eX.hom.base (eX.inv.base b) = b := by
      have h := congrArg (fun f => f.base) eX.inv_hom_id
      exact congrArg (fun f => f b) h
    exact ha.symm.trans (congrArg (fun x => eX.hom.base x) hab) |>.trans hb
  letI : Unique (OpenNhds p) :=
    { default := ⊤
      uniq := by
        intro a
        apply Subtype.ext
        ext z
        constructor
        · intro hz
          trivial
        · intro hz
          cases z with
          | up z => cases z; exact a.2 }
  letI : ∀ (i j : (OpenNhds p)ᵒᵖ) (f : i ⟶ j),
      IsIso (((OpenNhds.inclusion p).op ⋙ X.presheaf).map f) := by
    intro i j f
    have hij : i = j := Subsingleton.elim _ _
    subst j
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    infer_instance
  let eTop :
      Formalization.Books.Schemes.Unit06.locallyRingedSpaceGlobalSections X ≅
        (TopCat.Presheaf.stalkFunctor CommRingCat p).obj X.presheaf :=
    by
      change X.presheaf.obj (op (⊤ : Opens X)) ≅ _
      let e₀ := (colimitOfInitial ((OpenNhds.inclusion p).op ⋙ X.presheaf)).symm
      let hbot : (⊥_ ((OpenNhds p)ᵒᵖ)).unop = (⊤ : OpenNhds p) :=
        Subsingleton.elim _ _
      apply (eqToIso ?_).trans e₀
      change X.presheaf.obj (op (⊤ : Opens X)) =
        X.presheaf.obj (op ((⊥_ ((OpenNhds p)ᵒᵖ)).unop).1)
      rw [hbot]
      rfl
  letI : ∀ (i j : (OpenNhds p)ᵒᵖ) (f : i ⟶ j),
      IsIso (((OpenNhds.inclusion p).op ⋙ G).map f) := by
    intro i j f
    dsimp [G]
    infer_instance
  let eG : (TopCat.Presheaf.stalkFunctor CommRingCat p).obj G ≅
      CommRingCat.of R :=
    colimitOfInitial ((OpenNhds.inclusion p).op ⋙ G)
  letI : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat p).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) G)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      (X := Y) p CommRingCat G
  let eStalk :
      (TopCat.Presheaf.stalkFunctor CommRingCat p).obj X.presheaf ≅
        CommRingCat.of R := by
    change (TopCat.Presheaf.stalkFunctor CommRingCat p).obj F.1 ≅ CommRingCat.of R
    exact (asIso ((TopCat.Presheaf.stalkFunctor CommRingCat p).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) G))).symm ≪≫ eG
  letI : IsIso (AlgebraicGeometry.LocallyRingedSpace.Γ.map eX.op.hom) := by
    infer_instance
  let eΓ :
      Formalization.Books.Schemes.Unit06.locallyRingedSpaceGlobalSections
          ((Spec S).toLocallyRingedSpace) ≅
        Formalization.Books.Schemes.Unit06.locallyRingedSpaceGlobalSections X :=
    asIso (AlgebraicGeometry.LocallyRingedSpace.Γ.map eX.op.hom)
  let eR : S ≅ CommRingCat.of R :=
    (Scheme.ΓSpecIso S).symm ≪≫ eΓ ≪≫ eTop ≪≫ eStalk
  have hRsub : ∀ a b : PrimeSpectrum R, a = b := by
    intro a b
    let eP := PrimeSpectrum.comapEquiv eR.commRingCatIsoToRingEquiv
    exact eP.symm.injective (hSsub (eP.symm a) (eP.symm b))
  let e₀ : R ≃+* PowerSeries ℚ := ULift.ringEquiv
  let P₀ : PrimeSpectrum (PowerSeries ℚ) :=
    ⟨⊥, Ideal.isPrime_bot⟩
  let Pₘ : PrimeSpectrum (PowerSeries ℚ) :=
    ⟨IsLocalRing.maximalIdeal _, Ideal.IsMaximal.isPrime
      (IsLocalRing.maximalIdeal.isMaximal _)⟩
  let q₀ : PrimeSpectrum R := (PrimeSpectrum.comapEquiv e₀).symm P₀
  let qₘ : PrimeSpectrum R := (PrimeSpectrum.comapEquiv e₀).symm Pₘ
  have hq : q₀ = qₘ := hRsub q₀ qₘ
  have hP : P₀ = Pₘ := (PrimeSpectrum.comapEquiv e₀).symm.injective hq
  have hI : (⊥ : Ideal (PowerSeries ℚ)) = IsLocalRing.maximalIdeal _ :=
    congrArg PrimeSpectrum.asIdeal hP
  exact IsDiscreteValuationRing.not_a_field _ hI.symm

/-- A two-point scheme is affine. -/
theorem two_point_scheme_is_affine (X : Scheme.{u})
    (hX : IsTwoPoint X) : IsAffine X := by
  rcases hX with ⟨x, y, hxy, hxyall⟩
  let f : Bool → X := fun b => if b then x else y
  have hf : Function.Surjective f := by
    intro z
    rcases hxyall z with rfl | rfl
    · exact ⟨true, by simp [f]⟩
    · exact ⟨false, by simp [f]⟩
  letI : Finite X := Finite.of_surjective f hf
  by_cases hxd : IsOpen ({x} : Set X)
  · by_cases hyd : IsOpen ({y} : Set X)
    · letI : DiscreteTopology X :=
        discreteTopology_iff_isOpen_singleton.mpr (fun z => by
          rcases hxyall z with rfl | rfl
          · exact hxd
          · exact hyd)
      infer_instance
    · obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUtop⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open
          (a := y) (by trivial) isOpen_univ
      have hUeq : U = (⊤ : X.Opens) := by
        ext z
        constructor
        · intro hzU
          simp
        · intro hz
          by_cases hzU : z ∈ U
          · exact hzU
          · have hzx : z = x := by
              rcases hxyall z with hzx | hzy
              · exact hzx
              · exact (hzU (hzy ▸ hyU)).elim
            subst z
            exfalso
            have hUsub : (U : Set X) ⊆ ({y} : Set X) := by
              intro w hw
              rcases hxyall w with hwx | hwy
              · exact (hzU (hwx ▸ hw)).elim
              · exact hwy
            have hUy : (U : Set X) = ({y} : Set X) :=
              Set.Subset.antisymm hUsub (by
                intro w hw
                rw [Set.mem_singleton_iff.mp hw]
                exact hyU)
            exact hyd (hUy ▸ U.isOpen)
      letI : IsAffine (U : Scheme) := hU
      letI : IsAffine ((⊤ : X.Opens) : Scheme) := by
        rw [← hUeq]
        infer_instance
      exact IsAffine.of_isIso X.topIso.inv
  · obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUtop⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (a := x) (by trivial) isOpen_univ
    have hUeq : U = (⊤ : X.Opens) := by
      ext z
      constructor
      · intro hzU
        simp
      · intro hz
        by_cases hzU : z ∈ U
        · exact hzU
        · have hzy : z = y := by
            rcases hxyall z with hzx | hzy
            · exact (hzU (hzx ▸ hxU)).elim
            · exact hzy
          subst z
          exfalso
          have hUsub : (U : Set X) ⊆ ({x} : Set X) := by
            intro w hw
            rcases hxyall w with hwx | hwy
            · exact hwx
            · exact (hzU (hwy ▸ hw)).elim
          have hUx : (U : Set X) = ({x} : Set X) :=
            Set.Subset.antisymm hUsub (by
              intro w hw
              rw [Set.mem_singleton_iff.mp hw]
              exact hxU)
          exact hxd (hUx ▸ U.isOpen)
    letI : IsAffine (U : Scheme) := hU
    letI : IsAffine ((⊤ : X.Opens) : Scheme) := by
      rw [← hUeq]
      infer_instance
    exact IsAffine.of_isIso X.topIso.inv

/-- A scheme with finite discrete underlying space is affine. -/
theorem finite_discrete_scheme_is_affine (X : Scheme.{u})
    (hX : IsFiniteDiscrete X) : IsAffine X := by
  letI : Finite X := hX.1
  letI : DiscreteTopology X := hX.2
  infer_instance

private theorem unit33_no_three_distinct_ulift_bool
    (i j l : ULift.{u} Bool) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : False := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  rcases l with ⟨l⟩
  cases i <;> cases j <;> cases l
  all_goals first | exact hij rfl | exact hil rfl | exact hjl rfl

/-- There is a non-affine scheme with exactly three points. -/
theorem exists_three_point_non_affine_scheme :
    ∃ X : Scheme.{u}, IsThreePoint X ∧ ¬ IsAffine X := by
  let k : Type u := ULift.{u} ℚ
  letI : Field k := inferInstance
  let A := PowerSeries k
  letI : IsDiscreteValuationRing A := inferInstance
  let M : Ideal A := IsLocalRing.maximalIdeal A
  have hMne : M ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  have hMprime : M.IsPrime :=
    Ideal.IsMaximal.isPrime (IsLocalRing.maximalIdeal.isMaximal A)
  have hunique : ∀ P : Ideal A, P ≠ ⊥ → P.IsPrime → P = M := by
    intro P hPne hPprime
    rcases (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime A).mp
        (inferInstance : IsDiscreteValuationRing A) with ⟨_, ⟨Q, hQ, hQunique⟩⟩
    exact (hQunique P ⟨hPne, hPprime⟩).trans (hQunique M ⟨hMne, hMprime⟩).symm
  let p₀ : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  let pₘ : PrimeSpectrum A := ⟨M, hMprime⟩
  have hp₀m : p₀ ≠ pₘ := by
    intro h
    have hI : (⊥ : Ideal A) = M := congrArg PrimeSpectrum.asIdeal h
    exact hMne hI.symm
  have hpoints : ∀ p : PrimeSpectrum A, p = p₀ ∨ p = pₘ := by
    intro p
    by_cases hp : p.asIdeal = ⊥
    · exact Or.inl (PrimeSpectrum.ext hp)
    · exact Or.inr (PrimeSpectrum.ext (hunique p.asIdeal hp p.2))
  let x : A := PowerSeries.X
  have hx_ne : x ≠ 0 := PowerSeries.X_ne_zero
  have hx_mem_M : x ∈ M := by
    rw [show M = IsLocalRing.maximalIdeal A from rfl,
      PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self x
  have hbasic : (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) = {p₀} := by
    ext p
    constructor
    · intro hp
      rcases hpoints p with rfl | rfl
      · rfl
      · exact (hp hx_mem_M).elim
    · intro hp
      rw [Set.mem_singleton_iff.mp hp]
      change x ∉ (⊥ : Ideal A)
      exact fun h => hx_ne (show x = 0 from h)
  let T : Scheme.{u} := Spec (CommRingCat.of A)
  let U : T.Opens := PrimeSpectrum.basicOpen x
  have hU : (U : Set T) = {p₀} := hbasic
  let D' : CategoryTheory.GlueData' Scheme.{u} :=
    { J := ULift.{u} Bool
      U := fun _ => T
      V := fun _ _ _ => U.toScheme
      f := fun _ _ _ => U.ι
      f_mono := by
        intro i j hij
        infer_instance
      f_hasPullback := by
        intro i j l hij hil
        infer_instance
      t := fun _ _ _ => 𝟙 U.toScheme
      t' := by
        intro i j l hij hil hjl
        exact (unit33_no_three_distinct_ulift_bool i j l hij hil hjl).elim
      t_fac := by
        intro i j l hij hil hjl
        exact (unit33_no_three_distinct_ulift_bool i j l hij hil hjl).elim
      t_inv := by
        intro i j hij
        simp
      cocycle := by
        intro i j l hij hil hjl
        exact (unit33_no_three_distinct_ulift_bool i j l hij hil hjl).elim }
  let D : Scheme.GlueData.{u} :=
    { toGlueData := CategoryTheory.GlueData.ofGlueData' D'
      f_open := by
        intro i j
        classical
        change IsOpenImmersion (D'.f' i j)
        dsimp [CategoryTheory.GlueData'.f']
        split_ifs with hij
        · infer_instance
        · infer_instance }
  let X : Scheme.{u} := D.glued
  let i0 : D.J := ULift.up false
  let i1 : D.J := ULift.up true
  have hi01 : i0 ≠ i1 := by
    intro h
    have h' : false = true := congrArg ULift.down h
    cases h'
  let pT0 : T := p₀
  let pTm : T := pₘ
  have hpT0U : pT0 ∈ U := by
    change x ∉ (p₀ : PrimeSpectrum A).asIdeal
    exact fun h => hx_ne (show x = 0 from h)
  letI : IsOpenImmersion (D.ι i0) :=
    Scheme.GlueData.ι_isOpenImmersion D i0
  letI : IsOpenImmersion (D.ι i1) :=
    Scheme.GlueData.ι_isOpenImmersion D i1
  have hDV01 : D.V (i0, i1) = U.toScheme := by
    simp [D, CategoryTheory.GlueData.ofGlueData', D', i0, i1, hi01]
  have hDV10 : D.V (i1, i0) = U.toScheme := by
    simp [D, CategoryTheory.GlueData.ofGlueData', D', i0, i1, hi01]
  let e01 : D.V (i0, i1) ≅ U.toScheme := eqToIso hDV01
  let e10 : D.V (i1, i0) ≅ U.toScheme := eqToIso hDV10
  have hf01 : D.f i0 i1 = e01.hom ≫ U.ι := by
    simp [D, CategoryTheory.GlueData.ofGlueData', D',
      CategoryTheory.GlueData'.f', i0, i1, hi01, e01, hDV01] <;>
      apply congrArg (fun f : D.V (i0, i1) ⟶ U.toScheme => f ≫ U.ι) <;>
      congr 1
  have hf10 : D.f i1 i0 = e10.hom ≫ U.ι := by
    simp [D, CategoryTheory.GlueData.ofGlueData', D',
      CategoryTheory.GlueData'.f', i0, i1, hi01, e10, hDV10] <;>
      apply congrArg (fun f : D.V (i1, i0) ⟶ U.toScheme => f ≫ U.ι) <;>
      congr 1
  have ht01 : D.t i0 i1 = e01.hom ≫ e10.inv := by
    simp [D, CategoryTheory.GlueData.ofGlueData', D',
      CategoryTheory.GlueData'.f', i0, i1, hi01, e01, e10, hDV01, hDV10,
      eqToHom_trans, Category.assoc]
    change eqToHom _ = eqToHom hDV01 ≫ eqToHom hDV10.symm
    rw [← eqToHom_trans]
  let q0 : (D.U i0).carrier := pT0
  let q1 : (D.U i1).carrier := pT0
  let r0 : (D.U i0).carrier := pTm
  let r1 : (D.U i1).carrier := pTm
  let g : X := D.ι i0 q0
  let c0 : X := D.ι i0 r0
  let c1 : X := D.ι i1 r1
  have hι0 : Function.Injective (D.ι i0).base :=
    (D.ι i0).isOpenEmbedding.injective
  have hι1 : Function.Injective (D.ι i1).base :=
    (D.ι i1).isOpenEmbedding.injective
  have hg_c0 : g ≠ c0 := by
    intro h
    apply hp₀m
    have h' : q0 = r0 := hι0 h
    exact (show (q0 : PrimeSpectrum A) = r0 from h')
  have hgeneric : D.ι i0 q0 = D.ι i1 q1 := by
    apply (D.ι_eq_iff i0 i1 q0 q1).2
    change ∃ z : D.V (i0, i1), D.f i0 i1 z = q0 ∧
      (D.t i0 i1 ≫ D.f i1 i0) z = q1
    let zU : U.toScheme := ⟨pT0, hpT0U⟩
    let z : D.V (i0, i1) := e01.inv zU
    refine ⟨z, ?_, ?_⟩
    · rw [hf01]
      change (e01.hom ≫ U.ι) z = q0
      rw [Scheme.Hom.comp_apply]
      dsimp [z]
      have hz : e01.hom (e01.inv zU) = zU := by
        rw [← Scheme.Hom.comp_apply, e01.inv_hom_id]
        rfl
      rw [hz]
      simp [q0, pT0, zU, D, D', CategoryTheory.GlueData.ofGlueData'] <;> rfl
    · rw [ht01, hf10]
      change ((e01.hom ≫ e10.inv) ≫ (e10.hom ≫ U.ι)) z = q1
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      dsimp [z]
      have hz10 : e10.hom (e10.inv (e01.hom (e01.inv zU))) =
          e01.hom (e01.inv zU) := by
        rw [← Scheme.Hom.comp_apply, e10.inv_hom_id]
        rfl
      have hz01 : e01.hom (e01.inv zU) = zU := by
        rw [← Scheme.Hom.comp_apply, e01.inv_hom_id]
        rfl
      rw [hz10, hz01]
      simp [q1, pT0, zU, D, D', CategoryTheory.GlueData.ofGlueData'] <;> rfl
  have hg_c1 : g ≠ c1 := by
    intro h
    apply hp₀m
    apply hι1
    exact hgeneric.symm.trans h
  have hc0_c1 : c0 ≠ c1 := by
    intro h
    have hrel := (D.ι_eq_iff i0 i1 r0 r1).mp h
    change ∃ z : D.V (i0, i1), D.f i0 i1 z = r0 ∧
      (D.t i0 i1 ≫ D.f i1 i0) z = r1 at hrel
    rcases hrel with ⟨z, hz0, hz1⟩
    let zU : U.toScheme := e01.hom z
    have hzpoint : zU.1 = pT0 := by
      have hzmem : zU.1 ∈ (U : Set T) := zU.property
      rw [hU] at hzmem
      simpa [pT0] using Set.mem_singleton_iff.mp hzmem
    have hz0' : zU.1 = r0 := by
      have hz0'' : (e01.hom ≫ U.ι) z = r0 := by
        rw [← hf01]
        exact hz0
      change (e01.hom z).1 = r0 at hz0''
      simpa [zU] using hz0''
    have hqr : q0 = r0 := by
      have hqrT : pT0 = pTm := hzpoint.symm.trans hz0'
      exact congrArg (fun p : T => (show (D.U i0).carrier from p)) hqrT
    exact hp₀m (show (q0 : PrimeSpectrum A) = r0 from hqr)
  have hcover : ∀ w : X, w = g ∨ w = c0 ∨ w = c1 := by
    intro w
    obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective w
    rcases hpoints z with hz | hz
    · rcases i with ⟨i⟩
      cases i
      · exact Or.inl (by simpa [g, i0, pT0, q0, hz, D, D'])
      · exact Or.inl (by simpa [g, i0, i1, pT0, q0, q1, hgeneric, hz, D, D'])
    · rcases i with ⟨i⟩
      cases i
      · exact Or.inr (Or.inl (by simpa [c0, i0, pTm, r0, hz, D, D']))
      · exact Or.inr (Or.inr (by simpa [c1, i1, pTm, r1, hz, D, D']))
  have hthree : IsThreePoint X :=
    ⟨g, c0, c1, hg_c0, hg_c1, hc0_c1, hcover⟩
  refine ⟨X, hthree, ?_⟩
  intro hX
  have hU0 : D.U i0 = T := by
    simp [D, CategoryTheory.GlueData.ofGlueData', D', i0]
  have hU1 : D.U i1 = T := by
    simp [D, CategoryTheory.GlueData.ofGlueData', D', i1]
  let e : D.U i0 ≅ D.U i1 := eqToIso (hU0.trans hU1.symm)
  let f0 : (D.U i0) ⟶ X := D.ι i0
  let f1 : (D.U i0) ⟶ X := e.hom ≫ D.ι i1
  have hf0m : f0 r0 = c0 := by rfl
  have hf1m : f1 r0 = c1 := by
    dsimp [f1, e, r0, r1, c1, D, D']
    rfl
  have htransition : D.f i0 i1 ≫ e.hom = D.t i0 i1 ≫ D.f i1 i0 := by
    simp [e, D, CategoryTheory.GlueData.ofGlueData', D',
      CategoryTheory.GlueData'.f', i0, i1, hi01, hDV01, hDV10,
      hU0, hU1, eqToHom_trans, Category.assoc]
    congr 1
  have hrestrict : D.f i0 i1 ≫ f0 = D.f i0 i1 ≫ f1 := by
    dsimp [f0, f1]
    rw [← D.glue_condition i0 i1]
    rw [← Category.assoc]
    rw [← htransition]
    simp [Category.assoc]
  have hUdense : Dense (U : Set T) := by
    rw [hU]
    change Dense ({p₀} : Set (PrimeSpectrum A))
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp [p₀]
  letI : IsAffine X := hX
  letI : IsReduced (D.U i0) := by
    rw [hU0]
    dsimp [T]
    infer_instance
  letI : IsDominant U.ι := Opens.isDominant_ι hUdense
  letI : IsDominant (D.f i0 i1) := by
    rw [hf01]
    exact MorphismProperty.RespectsIso.precomp
      (P := @IsDominant) e01.hom U.ι (Opens.isDominant_ι hUdense)
  have hfg : f0 = f1 :=
    ext_of_isDominant (D.f i0 i1) hrestrict
  have hcc : c0 = c1 := by
    calc
      c0 = f0 r0 := hf0m.symm
      _ = f1 r0 := congrArg (fun f : (D.U i0) ⟶ X => f r0) hfg
      _ = c1 := hf1m
  exact hc0_c1 hcc

/-! ## Exercise `exercise-quasi-compact-closed-point` -/

/-- A nonempty quasi-compact scheme has a closed point. -/
theorem quasiCompact_nonempty_scheme_has_closed_point (X : Scheme.{u})
    [AlgebraicGeometry.QuasiCompact (𝟙 X)] (hX : Nonempty X) :
    HasClosedPoint X := by
  sorry

/-! ## Remark `remark-open-immersion` -/

/-- Restriction to an open subset is a scheme and its canonical map is an
open immersion. -/
theorem openSubscheme_is_scheme_and_open_immersion
    (X : Scheme.{u}) (U : Opens X) :
    IsOpenImmersion (openSubschemeInclusion X U) := by
  infer_instance

/-- The source's general notion of open immersion is the canonical one up to
isomorphism, as represented by Mathlib's `IsOpenImmersion` predicate. -/
theorem open_immersion_predicate_is_canonical
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsOpenImmersion f ↔
      ∃ U : Opens Y, ∃ e : X ≅ openSubscheme Y U,
        e.hom ≫ openSubschemeInclusion Y U = f := by
  sorry

/-! ## Exercises `exercise-open-affine-not-affine` and
`exercise-morphism-does-not-extend` -/

/-- An affine scheme can have a non-affine open subscheme. -/
theorem exists_affine_scheme_nonaffine_open_subscheme :
    ∃ (X : Scheme.{u}) (U : Opens X),
      IsAffine X ∧ ¬ IsAffine (openSubscheme X U) := by
  sorry

/-- A morphism from an open subscheme of an affine scheme to an affine scheme
need not extend to the ambient affine scheme. -/
theorem exists_affine_morphism_not_extend :
    ∃ (X Y : Scheme.{u}) (U : Opens X),
      IsAffine X ∧ IsAffine Y ∧
        ∃ f : openSubscheme X U ⟶ Y,
          ∀ g : X ⟶ Y, openSubschemeInclusion X U ≫ g ≠ f := by
  sorry

/-! ## Exercise `exercise-closed-subscheme-does-not-extend` -/

/-- A closed subscheme of an open subscheme need not extend to the ambient
scheme. -/
theorem exists_closed_subscheme_not_extend :
    Nonempty ClosedSubschemeNonExtensionExample := by
  sorry

/-! ## Exercise `exercise-not-morphism-schemes` -/

/-- A morphism of ringed spaces from the spectrum of a field need not be a
morphism of locally ringed spaces. -/
theorem exists_ringedSpace_morphism_not_scheme_morphism :
    ∃ (X : Scheme.{u}) (K : Type u) (_ : Field K)
      (f : (Scheme.Spec.obj (op (CommRingCat.of K))).toRingedSpace ⟶ X.toRingedSpace),
      ¬ IsLocallyRingedSpaceMorphism f := by
  sorry

/-! ## Definition `definition-integral` and its exercise -/

/-- The textbook definition of an integral scheme is the source-facing
`IsIntegralScheme` predicate from the core file. -/
theorem integral_scheme_definition_unfolds (X : Scheme.{u}) :
    IsIntegralScheme X ↔
      (Nonempty X ∧
        ∀ (U : Opens X), (U : Set X).Nonempty →
          affineLocallyRingedSpaceOpen X.toLocallyRingedSpace U →
            IsDomain (schemeGlobalSections (openSubscheme X U) : Type u)) := by
  rfl

/-- Integral schemes admit morphisms with surjective maps on every stalk that
are nevertheless not closed immersions. -/
theorem exists_integral_stalk_surjective_not_closed_immersion :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y),
      IsIntegralScheme X ∧ IsIntegralScheme Y ∧
        (∀ x : X, Function.Surjective (Scheme.Hom.stalkMap f x).hom) ∧
          ¬ IsClosedImmersion f := by
  sorry

/-! ## Exercise `exercise-fibre-product-affines-not-affine` and its remark -/

/-- Affine schemes can have a non-affine fibre product over a non-separated
base. -/
theorem exists_affine_fibre_product_not_affine :
    ∃ (S X Y : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S),
      IsAffine X ∧ IsAffine Y ∧ ¬ IsAffine (pullback f g) := by
  sorry

/-- Over a separated base, the fibre product of two affine schemes is affine.
This is the assertion behind the intervening remark. -/
theorem affine_fibre_product_of_separated_base
    (S X Y : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffine X] [IsAffine Y] [AlgebraicGeometry.Scheme.IsSeparated S] :
    IsAffine (pullback f g) := by
  sorry

/-! ## Exercise `exercise-not-geometrically-integral` -/

/-- There is an integral one-dimensional finite-type scheme over `ℚ` whose
complex base change is not integral. -/
theorem exists_integral_curve_over_Q_not_geometrically_integral :
    ∃ (V : Scheme.{0}) (v : V ⟶ rationalSpectrum),
      IsIntegralScheme V ∧ SchemeDimension V = 1 ∧
        IsFiniteTypeMorphism v ∧
        ¬ IsIntegralScheme (pullback complexToRational v) := by
  sorry

/-! ## Exercise `exercise-not-geometrically-reduced` -/

/-- An integral one-dimensional finite-type scheme over a field can acquire
nilpotents after a finite field extension. -/
theorem exists_integral_curve_not_geometrically_reduced :
    ∃ (k k' : Type u) (_ : Field k) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k')
      (V : Scheme.{u})
      (v : V ⟶ Scheme.Spec.obj (op (CommRingCat.of k))),
      IsIntegralScheme V ∧ SchemeDimension V = 1 ∧
        IsFiniteTypeMorphism v ∧
          ¬ AlgebraicGeometry.IsReduced (fieldBaseChange k k' V v) := by
  sorry

/-! ## Remark `remark-affine-dimension` -/

/-- For an affine scheme, the scheme dimension agrees with the Krull
dimension of its coordinate ring. -/
theorem affine_scheme_dimension_eq_ring_krull_dimension
    (X : Scheme.{u}) [IsAffine X] :
    SchemeDimension X = RingKrullDimension (schemeGlobalSections X : Type u) := by
  sorry

end

end Formalization.Books.Exercises.Unit33
