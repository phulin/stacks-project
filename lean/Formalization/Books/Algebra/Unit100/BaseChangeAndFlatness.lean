import Formalization.Books.Algebra.Unit99.CriteriaForFlatness

/-!
# Commutative Algebra, Chapter 100: Base change and flatness

The commutative squares in the source are expressed by four ring homomorphisms
and an equality of their composites.  The localization hypothesis and the
base-changed module use the canonical interfaces from Chapter 99.
-/

namespace Formalization.Books.Algebra.Unit100

open Formalization.Books.Algebra.Unit99
open scoped TensorProduct

universe u

noncomputable section

private theorem flat_of_localized_module_of_flat
    {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M]
    [AddCommGroup N] [Module R N] [Module A N]
    (P : Submonoid A) (f : M →ₗ[A] N) [IsLocalizedModule P f]
    (hTowerM : IsScalarTower R A M) (hTowerN : IsScalarTower R A N)
    (hflat : Module.Flat R M) : Module.Flat R N := by
  letI := hTowerM
  letI := hTowerN
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  simp_rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := A)]
  intro Q _ _ N
  have hF : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) :=
    (Module.Flat.iff_lTensor_injectiveₛ.mp hflat) N
  have hmap := IsLocalizedModule.map_injective
    (S := P)
    (f := TensorProduct.AlgebraTensorModule.rTensor R N f)
    (g := TensorProduct.AlgebraTensorModule.rTensor R Q f)
    (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) hF
  simpa [IsLocalizedModule.map_lTensor] using hmap

/-! ## Base change and flatness -/

/--
Flatness moves up and down a local square whose upper-right corner is a
localization of the tensor product.  The two conjuncts are the source's
items (1) and (2).
-/
theorem base_change_flat_up_down
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h] [IsLocalHom k]
    (compat : h.comp f = k.comp g)
    (hlocal : IsTensorProductLocalization f g h k compat)
    (M : ModuleCat.{u} S) :
    (Module.Flat R ((ModuleCat.restrictScalars f).obj M) →
        Module.Flat R' (squareBaseChangedModule h k M)) ∧
    (Module.Flat R' (squareBaseChangedModule h k M) →
        RingHom.Flat g →
          Module.Flat R ((ModuleCat.restrictScalars f).obj M)) := by
  constructor
  · intro hM
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    letI : Algebra R S' := (h.comp f).toAlgebra
    letI : Algebra R' S' := k.toAlgebra
    letI : Algebra S S' := h.toAlgebra
    letI : Module R (M : Type u) := Module.compHom M f
    letI : IsScalarTower R S (M : Type u) := SMul.comp.isScalarTower f
    change Module.Flat R (M : Type u) at hM
    letI : Algebra S (TensorProduct R S R') := Algebra.TensorProduct.leftAlgebra
    letI : Algebra R' (TensorProduct R S R') := Algebra.TensorProduct.rightAlgebra
    letI : IsScalarTower S (TensorProduct R S R') (TensorProduct R S R') := by
      refine IsScalarTower.of_algebraMap_smul ?_
      intro s t
      simp [Algebra.smul_def]
    letI : Algebra (TensorProduct R S R') S' :=
      (tensorProductToSquareTarget f g h k compat).toAlgebra
    rcases hlocal with ⟨P, hP⟩
    have heqh :
        (tensorProductToSquareTarget f g h k compat).comp
            (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g) = h := by
      ext x
      simp [tensorProductToSquareTarget,
        Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap, RingHom.comp_apply]
    have heqk :
        (tensorProductToSquareTarget f g h k compat).comp
            (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) = k := by
      ext x
      simp [tensorProductToSquareTarget,
        Formalization.Books.Algebra.Unit14.baseChangeRingMap, RingHom.comp_apply]
    letI : IsScalarTower S (TensorProduct R S R') S' := by
      apply IsScalarTower.of_algebraMap_eq'
      change h = (tensorProductToSquareTarget f g h k compat).comp
        (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g)
      exact heqh.symm
    have hsource0 : Module.Flat R' (R' ⊗[R] (M : Type u)) := by
      exact Formalization.Books.Algebra.Unit39.flat_base_change hM
    letI : Module.Flat R' (R' ⊗[R] (M : Type u)) := hsource0
    letI : Module R' (TensorProduct R S R' ⊗[S] (M : Type u)) :=
      Module.compHom _ (algebraMap R' (TensorProduct R S R'))
    letI : IsScalarTower R' (TensorProduct R S R')
        (TensorProduct R S R' ⊗[S] (M : Type u)) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let e : (TensorProduct R S R' ⊗[S] (M : Type u)) ≃ₗ[R']
        (R' ⊗[R] (M : Type u)) :=
      Algebra.IsPushout.cancelBaseChange R R' S (TensorProduct R S R')
        (M : Type u)
    have hsource : Module.Flat R' (TensorProduct R S R' ⊗[S] (M : Type u)) :=
      Module.Flat.of_linearEquiv e
    letI : Module (TensorProduct R S R')
        (S' ⊗[S] (M : Type u)) :=
      Module.compHom _ (algebraMap (TensorProduct R S R') S')
    letI : Module R' (S' ⊗[S] (M : Type u)) :=
      Module.compHom _ k
    letI : IsScalarTower R' (TensorProduct R S R')
        (S' ⊗[S] (M : Type u)) := by
      refine IsScalarTower.of_algebraMap_smul ?_
      intro r x
      change (algebraMap (TensorProduct R S R') S'
          (algebraMap R' (TensorProduct R S R') r)) • x = k r • x
      have hk_r : algebraMap (TensorProduct R S R') S'
          (algebraMap R' (TensorProduct R S R') r) = k r := by
        change ((tensorProductToSquareTarget f g h k compat).comp
          (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)) r = k r
        exact DFunLike.congr_fun heqk r
      rw [hk_r]
    let gLoc : (TensorProduct R S R' ⊗[S] (M : Type u)) →ₗ[
        TensorProduct R S R'] (S' ⊗[S] (M : Type u)) :=
      TensorProduct.AlgebraTensorModule.rTensor S (M : Type u)
        (Algebra.linearMap (TensorProduct R S R') S')
    letI : IsLocalizedModule P
        (Algebra.linearMap (TensorProduct R S R') S') := inferInstance
    letI : IsLocalizedModule P gLoc := by
      exact IsLocalizedModule.rTensor (S := P) (N := (M : Type u))
        (g := Algebra.linearMap (TensorProduct R S R') S')
    have hsource_tower : IsScalarTower R' (TensorProduct R S R')
        (TensorProduct R S R' ⊗[S] (M : Type u)) := inferInstance
    have htarget : Module.Flat R' (S' ⊗[S] (M : Type u)) := by
      exact flat_of_localized_module_of_flat
        (R := R') (A := TensorProduct R S R')
        (M := TensorProduct R S R' ⊗[S] (M : Type u))
        (N := S' ⊗[S] (M : Type u)) P gLoc hsource_tower
        (inferInstance : IsScalarTower R' (TensorProduct R S R')
          (S' ⊗[S] (M : Type u))) hsource
    change Module.Flat R' (S' ⊗[S] (M : Type u))
    exact htarget
  · intro hM hg
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    letI : Algebra R S' := (h.comp f).toAlgebra
    letI : Algebra R' S' := k.toAlgebra
    letI : Algebra S S' := h.toAlgebra
    letI : Module R (M : Type u) := Module.compHom M f
    letI : IsScalarTower R S (M : Type u) := SMul.comp.isScalarTower f
    letI : Module R' (S' ⊗[S] (M : Type u)) :=
      Module.compHom _ k
    change Module.Flat R' (S' ⊗[S] (M : Type u)) at hM
    letI : Module.Flat R R' := hg
    letI : Module R (S' ⊗[S] (M : Type u)) :=
      Module.compHom _ (h.comp f)
    letI : IsScalarTower R R' (S' ⊗[S] (M : Type u)) :=
      IsScalarTower.of_algebraMap_smul (by
        intro r x
        change k (g r) • x = h (f r) • x
        have hc : k (g r) = h (f r) := by
          simpa [RingHom.comp_apply] using
            congrArg (fun q : R →+* S' => q r) compat.symm
        rw [hc])
    letI : Module.Flat R' (S' ⊗[S] (M : Type u)) := hM
    have htowerRR' : IsScalarTower R R' (S' ⊗[S] (M : Type u)) := inferInstance
    have hMdown : Module.Flat R (S' ⊗[S] (M : Type u)) := by
      exact @Module.Flat.trans R R' (S' ⊗[S] (M : Type u))
        _ _ _ _ _ _ htowerRR' inferInstance hM
    letI : Algebra S (TensorProduct R S R') := Algebra.TensorProduct.leftAlgebra
    letI : Algebra R' (TensorProduct R S R') := Algebra.TensorProduct.rightAlgebra
    letI : IsScalarTower S (TensorProduct R S R') (TensorProduct R S R') := by
      refine IsScalarTower.of_algebraMap_smul ?_
      intro s t
      simp [Algebra.smul_def]
    letI : Algebra (TensorProduct R S R') S' :=
      (tensorProductToSquareTarget f g h k compat).toAlgebra
    rcases hlocal with ⟨P, hP⟩
    have hbase : RingHom.Flat
        (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g) := by
      exact RingHom.Flat.isStableUnderBaseChange.tensorProduct S hg
    have ht : RingHom.Flat (tensorProductToSquareTarget f g h k compat) := by
      change Module.Flat (TensorProduct R S R') S'
      exact IsLocalization.flat S' P
    have hcomp : RingHom.Flat
        ((tensorProductToSquareTarget f g h k compat).comp
          (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g)) :=
      RingHom.Flat.comp hbase ht
    have heqh :
        (tensorProductToSquareTarget f g h k compat).comp
            (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g) = h := by
      ext x
      simp [tensorProductToSquareTarget,
        Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap, RingHom.comp_apply]
    have hflatS : RingHom.Flat h := by
      rw [← heqh]
      exact hcomp
    letI : IsScalarTower R S S' := by
      apply IsScalarTower.of_algebraMap_eq'
      rfl
    letI : Module.Flat S S' := hflatS
    have hfaith : RingHom.FaithfullyFlat h :=
      Formalization.Books.Algebra.Unit39.faithfullyFlat_of_localRingHom h hflatS
    letI : Module.FaithfullyFlat S S' := hfaith
    have hdesc := Formalization.Books.Algebra.Unit39.flatness_descends_more_general
      (R := R) (S := S) (S' := S') (M := (M : Type u)) hflatS
    exact (hdesc.2 hfaith).mpr hMdown

/-- The source's item (3): flatness of the upper horizontal map ascends. -/
theorem flat_ring_hom_base_change
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h] [IsLocalHom k]
    (compat : h.comp f = k.comp g)
    (hlocal : IsTensorProductLocalization f g h k compat) :
    RingHom.Flat f → RingHom.Flat k := by
  intro hf
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R S' := (h.comp f).toAlgebra
  letI : Algebra R' S' := k.toAlgebra
  letI : Module.Flat R S := hf
  letI : Algebra R' (TensorProduct R S R') := Algebra.TensorProduct.rightAlgebra
  have hbase : RingHom.Flat (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
    exact RingHom.Flat.isStableUnderBaseChange
      (R := R) (S := S) (R' := R') (S' := TensorProduct R S R') hf
  rcases hlocal with ⟨P, hP⟩
  letI : Algebra (TensorProduct R S R') S' :=
    (tensorProductToSquareTarget f g h k compat).toAlgebra
  have hk : RingHom.Flat (tensorProductToSquareTarget f g h k compat) := by
    change Module.Flat (TensorProduct R S R') S'
    exact IsLocalization.flat S' P
  have hcomp : RingHom.Flat
      ((tensorProductToSquareTarget f g h k compat).comp
        (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)) :=
    RingHom.Flat.comp hbase hk
  have heq :
      (tensorProductToSquareTarget f g h k compat).comp
        (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) = k := by
    ext x
    simp [tensorProductToSquareTarget,
      Formalization.Books.Algebra.Unit14.baseChangeRingMap, RingHom.comp_apply]
  rw [← heq]
  exact hcomp

/-- The source's item (4): flatness of the two right-hand maps descends. -/
theorem flat_ring_hom_base_change_down
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h] [IsLocalHom k]
    (compat : h.comp f = k.comp g)
    (hlocal : IsTensorProductLocalization f g h k compat) :
    RingHom.Flat k → RingHom.Flat g → RingHom.Flat f := by
  intro hk hg
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R S' := (h.comp f).toAlgebra
  letI : Algebra R' S' := k.toAlgebra
  letI : Algebra S S' := h.toAlgebra
  letI : Module R' (S' ⊗[S] S) := Module.compHom _ k
  letI : Module.Flat R' S' := hk
  letI : Module.Flat S S := Module.Flat.self
  letI : Module.Flat S' (S' ⊗[S] S) := Module.Flat.baseChange S S' S
  letI : IsScalarTower R' S' (S' ⊗[S] S) := by
    refine IsScalarTower.of_algebraMap_smul ?_
    intro r x
    change (algebraMap R' S' r) • x = k r • x
    simp [RingHom.algebraMap_toAlgebra]
  have htower : IsScalarTower R' S' (S' ⊗[S] S) := inferInstance
  have hM' : Module.Flat R' (S' ⊗[S] S) := by
    exact @Module.Flat.trans R' S' (S' ⊗[S] S)
      _ _ _ _ _ _ htower hk inferInstance
  have hresult :=
    (base_change_flat_up_down f g h k compat hlocal (ModuleCat.of S S)).2 hM' hg
  change Module.Flat R S at hresult
  exact hresult

/-!
## Another local criterion for flatness

The module in the conclusion is `squareBaseChangedModule h k M`, namely the
canonical `M ⊗_S S'` viewed as an `R'`-module.
-/

/--
The finite-module local criterion after a flat base change.  The equality of
ideals records the source's hypothesis
`\mathfrak m_R R' = \mathfrak m_{R'}`.
-/
theorem yet_another_variant_local_criterion_flatness
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    [IsNoetherianRing R'] [IsNoetherianRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h] [IsLocalHom k]
    (compat : h.comp f = k.comp g)
    (hlocal : IsTensorProductLocalization f g h k compat)
    (hflat_top : RingHom.Flat h) (hflat_bottom : RingHom.Flat g)
    (M : ModuleCat.{u} S) (hfinite : Module.Finite S M)
    (hmax : Ideal.map g (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal R')
    (hflat : Module.Flat R ((ModuleCat.restrictScalars f).obj M)) :
    Module.Flat R' (squareBaseChangedModule h k M) := by
  exact (base_change_flat_up_down f g h k compat hlocal M).1 hflat

end

end Formalization.Books.Algebra.Unit100
