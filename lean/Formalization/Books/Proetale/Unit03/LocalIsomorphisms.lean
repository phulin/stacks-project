import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Pro-étale Cohomology, Chapter 3: Local isomorphisms

This file records the definitions and statements in the source section
“Local isomorphisms”.  The algebraic predicates use Mathlib's canonical
localizations, affine schemes, étale and quasi-finite ring-map properties,
and localization maps at primes.
-/

namespace Formalization.Books.Proetale.Unit03

open Set Function CategoryTheory
open AlgebraicGeometry
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Definitions -/

/--
Mathlib's `Algebra.IsLocalIso` is the canonical algebraic formulation of the
source's local-isomorphism definition.  The wrapper below equips a bare ring
homomorphism with its canonical algebra structure before using that predicate.
-/
def IsLocalIsomorphism {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) : Prop :=
  letI : Algebra A B := φ.toAlgebra
  Algebra.IsLocalIso A B

/--
A ring map identifies local rings when its canonical map between the local
localizations at corresponding prime ideals is bijective.
-/
def IdentifiesLocalRings {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) : Prop :=
  ∀ q : PrimeSpectrum B,
    Function.Bijective
      (Localization.localRingHom (q.asIdeal.comap φ) q.asIdeal φ rfl)

/-! ## Elementary permanence properties -/

theorem baseChange_isLocalIsomorphism
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (φ : A →+* B) (ψ : A →+* A') (h : IsLocalIsomorphism φ) :
    letI := φ.toAlgebra
    letI := ψ.toAlgebra
    IsLocalIsomorphism
      (Algebra.TensorProduct.includeRight.toRingHom :
        A' →+* B ⊗[A] A') := by
  let _ : Algebra A B := φ.toAlgebra
  let _ : Algebra A A' := ψ.toAlgebra
  let _ : Algebra A' (B ⊗[A] A') := Algebra.TensorProduct.rightAlgebra
  change Algebra.IsLocalIso A B at h
  let _ : Algebra.IsLocalIso A B := h
  change Algebra.IsLocalIso A' (B ⊗[A] A')
  let _ : Algebra.IsLocalIso A' (A' ⊗[A] B) := inferInstance
  exact Algebra.IsLocalIso.of_algEquiv
    (R := A') (S := A' ⊗[A] B) (T := B ⊗[A] A')
    (Algebra.TensorProduct.commRight A A' B)

theorem baseChange_identifiesLocalRings
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (φ : A →+* B) (ψ : A →+* A') (h : IdentifiesLocalRings φ) :
    letI := φ.toAlgebra
    letI := ψ.toAlgebra
    IdentifiesLocalRings
      (Algebra.TensorProduct.includeRight.toRingHom :
        A' →+* B ⊗[A] A') := by
  let _ : Algebra A B := φ.toAlgebra
  let _ : Algebra A A' := ψ.toAlgebra
  let _ : Algebra A' (B ⊗[A] A') := Algebra.TensorProduct.rightAlgebra
  intro q
  let j : A' →+* B ⊗[A] A' :=
    Algebra.TensorProduct.includeRight.toRingHom
  let k : B →+* B ⊗[A] A' :=
    Algebra.TensorProduct.includeLeftRingHom
  let p : PrimeSpectrum B := ⟨q.asIdeal.comap k, inferInstance⟩
  let r : PrimeSpectrum A' := ⟨q.asIdeal.comap j, inferInstance⟩
  let I : Ideal A := p.asIdeal.comap φ
  have hbase : k.comp φ = j.comp ψ := by
    simpa [j, k, RingHom.algebraMap_toAlgebra] using
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        (R := A) (A := B) (B := A'))
  have hi : I = r.asIdeal.comap ψ := by
    simpa [I, p, r, j, k, Ideal.comap_comap] using
      congrArg (fun f : A →+* B ⊗[A] A' => q.asIdeal.comap f) hbase
  let e : Localization.AtPrime I →+* Localization.AtPrime p.asIdeal :=
    Localization.localRingHom I p.asIdeal φ rfl
  have he : Function.Bijective e := h p
  let er : Localization.AtPrime I ≃+* Localization.AtPrime p.asIdeal :=
    RingEquiv.ofBijective e he
  let a : Localization.AtPrime I →+* Localization.AtPrime r.asIdeal :=
    Localization.localRingHom I r.asIdeal ψ hi
  let β : Localization.AtPrime p.asIdeal →+* Localization.AtPrime r.asIdeal :=
    a.comp er.symm.toRingHom
  let bRing : B →+* Localization.AtPrime r.asIdeal :=
    β.comp (algebraMap B (Localization.AtPrime p.asIdeal))
  let aRing : A' →+* Localization.AtPrime r.asIdeal :=
    algebraMap A' (Localization.AtPrime r.asIdeal)
  have hba : bRing.comp φ = aRing.comp ψ := by
    ext x
    have hinner :
        er.symm (algebraMap B (Localization.AtPrime p.asIdeal) (φ x)) =
          algebraMap A (Localization.AtPrime I) x := by
      apply er.injective
      simp [er, e, Localization.localRingHom_to_map]
    change a (er.symm (algebraMap B (Localization.AtPrime p.asIdeal) (φ x))) =
      algebraMap A' (Localization.AtPrime r.asIdeal) (ψ x)
    rw [hinner]
    simp [a, Localization.localRingHom_to_map]
  let _ : Algebra A (Localization.AtPrime r.asIdeal) :=
    (aRing.comp (algebraMap A A')).toAlgebra
  let _ : SMul A (Localization.AtPrime r.asIdeal) :=
    (inferInstance : Algebra A (Localization.AtPrime r.asIdeal)).toSMul
  let _ : IsScalarTower A A (Localization.AtPrime r.asIdeal) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let bAlg : B →ₐ[A] Localization.AtPrime r.asIdeal :=
    { toRingHom := bRing
      commutes' := by
        intro x
        exact DFunLike.congr_fun hba x }
  let aAlg : A' →ₐ[A] Localization.AtPrime r.asIdeal :=
    { toRingHom := aRing
      commutes' := by
        intro x
        rfl }
  let mAlg : (B ⊗[A] A') →ₐ[A] Localization.AtPrime r.asIdeal :=
    Algebra.TensorProduct.lift bAlg aAlg (fun _ _ => Commute.all _ _)
  let l : Localization.AtPrime r.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom r.asIdeal q.asIdeal j rfl
  let nS : (B ⊗[A] A') →+* Localization.AtPrime q.asIdeal :=
    algebraMap (B ⊗[A] A') (Localization.AtPrime q.asIdeal)
  let c : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal k rfl
  have hca : c.comp e = l.comp a := by
    apply IsLocalization.ringHom_ext I.primeCompl
    ext x
    simp [c, e, l, a, Localization.localRingHom_to_map]
    exact congrArg nS (DFunLike.congr_fun hbase x)
  have hla : l.comp aRing = nS.comp j := by
    ext x
    simp [l, aRing, nS, Localization.localRingHom_to_map]
  have hck : nS.comp k = c.comp (algebraMap B (Localization.AtPrime p.asIdeal)) := by
    ext x
    simp [nS, c, Localization.localRingHom_to_map]
  have hlβ : l.comp β = c := by
    have hca' : l.comp a = c.comp er.toRingHom := by
      change l.comp a = c.comp e
      exact hca.symm
    calc
      l.comp β = (l.comp a).comp er.symm.toRingHom := by rfl
      _ = (c.comp er.toRingHom).comp er.symm.toRingHom := by rw [hca']
      _ = c := by
        ext x
        simp [RingHom.comp_apply]
  have hlm : l.comp mAlg.toRingHom = nS := by
    apply RingHom.ext
    intro x
    refine TensorProduct.induction_on (R := A) x ?_ ?_ ?_
    · simp [mAlg, nS]
    · intro b a'
      change l (bRing b * aRing a') = nS (b ⊗ₜ[A] a')
      have h1 :
          l (β (algebraMap B (Localization.AtPrime p.asIdeal) b)) =
            c (algebraMap B (Localization.AtPrime p.asIdeal) b) := by
        exact DFunLike.congr_fun hlβ _
      have h2 : l (aRing a') = nS (j a') := by
        exact DFunLike.congr_fun hla a'
      have h3 :
          nS (k b) = c (algebraMap B (Localization.AtPrime p.asIdeal) b) := by
        exact DFunLike.congr_fun hck b
      calc
        l (bRing b * aRing a') =
            l (β (algebraMap B (Localization.AtPrime p.asIdeal) b)) *
              l (aRing a') := by simp [bRing, map_mul]
        _ = c (algebraMap B (Localization.AtPrime p.asIdeal) b) *
              nS (j a') := by
          rw [h1, h2]
        _ = nS (k b) * nS (j a') := by
          rw [h3]
        _ = nS (b ⊗ₜ[A] a') := by
          rw [← map_mul]
          simp [j, k, Algebra.TensorProduct.tmul_mul_tmul]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
  let m : (B ⊗[A] A') →+* Localization.AtPrime r.asIdeal := mAlg.toRingHom
  have hm_unit : ∀ x : q.asIdeal.primeCompl, IsUnit (m x) := by
    intro x
    by_contra hmx
    let _ : IsLocalHom l := Localization.isLocalHom_localRingHom
      r.asIdeal q.asIdeal j rfl
    have hunit : IsUnit (nS x) :=
      IsLocalization.map_units (Localization.AtPrime q.asIdeal) x
    have hmap : IsUnit (l (m x)) := by
      change IsUnit ((l.comp mAlg.toRingHom) (x : B ⊗[A] A'))
      have hlmx := DFunLike.congr_fun hlm (x : B ⊗[A] A')
      rw [hlmx]
      exact hunit
    exact hmx (IsLocalHom.map_nonunit (f := l) (m x) hmap)
  let mloc : Localization.AtPrime q.asIdeal →+* Localization.AtPrime r.asIdeal :=
    IsLocalization.lift hm_unit
  have hmloc : mloc.comp nS = m := by
    change (IsLocalization.lift hm_unit).comp (algebraMap _ _) = m
    exact IsLocalization.lift_comp hm_unit
  have hinv₁ : mloc.comp l = RingHom.id _ := by
    apply IsLocalization.ringHom_ext r.asIdeal.primeCompl
    change (mloc.comp l).comp aRing = (RingHom.id _).comp aRing
    calc
      (mloc.comp l).comp aRing = mloc.comp (l.comp aRing) := by rfl
      _ = mloc.comp (nS.comp j) := by rw [hla]
      _ = (mloc.comp nS).comp j := by rfl
      _ = m.comp j := by rw [hmloc]
      _ = aRing := by
        ext x
        simp [m, mAlg, aRing, j]
        rfl
      _ = (RingHom.id _).comp aRing := by rfl
  have hinv₂ : l.comp mloc = RingHom.id _ := by
    apply IsLocalization.ringHom_ext q.asIdeal.primeCompl
    change (l.comp mloc).comp nS = (RingHom.id _).comp nS
    calc
      (l.comp mloc).comp nS = l.comp (mloc.comp nS) := by rfl
      _ = l.comp m := by rw [hmloc]
      _ = nS := hlm
      _ = (RingHom.id _).comp nS := by rfl
  constructor
  · intro x y hxy
    calc
      x = mloc (l x) := by
        have hx := DFunLike.congr_fun hinv₁ x
        change mloc (l x) = x at hx
        exact hx.symm
      _ = mloc (l y) := congrArg mloc hxy
      _ = y := by
        have hy := DFunLike.congr_fun hinv₁ y
        change mloc (l y) = y at hy
        exact hy
  · intro y
    refine ⟨mloc y, ?_⟩
    have hy := DFunLike.congr_fun hinv₂ y
    change l (mloc y) = y at hy
    exact hy

theorem comp_isLocalIsomorphism
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    (hφ : IsLocalIsomorphism φ) (hψ : IsLocalIsomorphism ψ) :
    IsLocalIsomorphism (ψ.comp φ) := by
  let _ : Algebra A B := φ.toAlgebra
  let _ : Algebra B C := ψ.toAlgebra
  let _ : Algebra A C := (ψ.comp φ).toAlgebra
  let _ : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (by intro x; rfl)
  change Algebra.IsLocalIso A B at hφ
  change Algebra.IsLocalIso B C at hψ
  change Algebra.IsLocalIso A C
  let _ : Algebra.IsLocalIso A B := hφ
  let _ : Algebra.IsLocalIso B C := hψ
  exact Algebra.IsLocalIso.trans (T := C) (R := A) (S := B)

theorem comp_identifiesLocalRings
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    (hφ : IdentifiesLocalRings φ) (hψ : IdentifiesLocalRings ψ) :
    IdentifiesLocalRings (ψ.comp φ) := by
  intro q
  let p : PrimeSpectrum B := ⟨q.asIdeal.comap ψ, inferInstance⟩
  have hp := hφ p
  have hq := hψ q
  have hi : (q.asIdeal.comap ψ).comap φ = q.asIdeal.comap (ψ.comp φ) :=
    Ideal.comap_comap φ ψ
  let e := Localization.localRingEquiv
    (q.asIdeal.comap (ψ.comp φ)) ((q.asIdeal.comap ψ).comap φ)
    (RingEquiv.refl A) hi.symm
  have heq := Localization.localRingHom_comp
    (I := q.asIdeal.comap (ψ.comp φ)) (J := q.asIdeal.comap ψ)
    (K := q.asIdeal) φ hi.symm ψ rfl
  have hinner :
      Localization.localRingHom (q.asIdeal.comap (ψ.comp φ))
          (q.asIdeal.comap ψ) φ hi.symm =
        (Localization.localRingHom ((q.asIdeal.comap ψ).comap φ)
          (q.asIdeal.comap ψ) φ rfl).comp
          (Localization.localRingHom (q.asIdeal.comap (ψ.comp φ))
            ((q.asIdeal.comap ψ).comap φ) (RingHom.id A) hi.symm) := by
    have hinner' := Localization.localRingHom_comp
      (I := q.asIdeal.comap (ψ.comp φ))
      (J := (q.asIdeal.comap ψ).comap φ) (K := q.asIdeal.comap ψ)
      (RingHom.id A) hi.symm φ rfl
    simpa only [RingHom.comp_id] using hinner'
  rw [heq, hinner]
  simpa [e, Localization.localRingEquiv, Localization.localRingHom_id, p,
    Function.comp_def] using
    (hq.comp hp).comp e.bijective

theorem of_isLocalIsomorphism_of_isLocalIsomorphism
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C)
    (hB : IsLocalIsomorphism (algebraMap A B))
    (hC : IsLocalIsomorphism (algebraMap A C)) :
    IsLocalIsomorphism f.toRingHom := by
  have hB' : @Algebra.IsLocalIso A B _ _ (algebraMap A B).toAlgebra := hB
  have hC' : @Algebra.IsLocalIso A C _ _ (algebraMap A C).toAlgebra := hC
  let _ : Algebra B C := f.toRingHom.toAlgebra
  let _ : IsScalarTower A B C := IsScalarTower.of_algHom f
  change Algebra.IsLocalIso B C
  constructor
  intro P hP
  let _ : P.IsPrime := hP
  let p : PrimeSpectrum B := ⟨P.comap f.toRingHom, inferInstance⟩
  obtain ⟨g, hg, hBg⟩ :=
    @Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion A B _ _
      (algebraMap A B).toAlgebra hB' p.asIdeal inferInstance
  obtain ⟨s, hs, hCs⟩ :=
    @Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion A C _ _
      (algebraMap A C).toAlgebra hC' P inferInstance
  refine ⟨s * f g, ?_, ?_⟩
  · apply hP.mul_notMem hs
    intro hfg
    exact hg hfg
  · obtain ⟨a, ha⟩ := hBg
    have hCs0 := hCs
    obtain ⟨b, hb⟩ := hCs
    let T := Localization.Away (s * f g)
    let fT : B →+* T := (algebraMap C T).comp f.toRingHom
    have hfgC : IsUnit ((algebraMap C T) (f g)) := by
      apply IsLocalization.Away.isUnit_of_dvd (x := s * f g)
      exact ⟨s, by ring⟩
    have hfg : IsUnit (fT g) := by simpa [fT] using hfgC
    let lift_g : Localization.Away g →+* T :=
      IsLocalization.Away.lift g hfg
    let _ : Algebra (Localization.Away g) T := lift_g.toAlgebra
    have hst : IsUnit ((algebraMap C T) s) := by
      apply IsLocalization.Away.isUnit_of_dvd (x := s * f g)
      exact ⟨f g, by simp⟩
    let lift_s : Localization.Away s →+* T :=
      IsLocalization.Away.lift s hst
    let Q := Localization.Away
      (algebraMap C (Localization.Away s) (f g))
    let fSQ : Localization.Away s →+* Q := algebraMap _ _
    let fCQ : C →+* Q := fSQ.comp (algebraMap C (Localization.Away s))
    have hfgQ : IsUnit
        (lift_s ((algebraMap C (Localization.Away s)) (f g))) := by
      rw [IsLocalization.Away.lift_eq]
      exact IsLocalization.Away.isUnit_of_dvd (x := s * f g) ⟨s, by ring⟩
    let u : Q →+* T := IsLocalization.Away.lift
      (algebraMap C (Localization.Away s) (f g)) (g := lift_s) hfgQ
    have hsQ : IsUnit (fCQ s) := by
      change IsUnit (fSQ ((algebraMap C (Localization.Away s)) s))
      exact IsUnit.map _ (IsLocalization.Away.algebraMap_isUnit s)
    have hfgQ' : IsUnit (fCQ (f g)) := by
      change IsUnit (fSQ ((algebraMap C (Localization.Away s)) (f g)))
      exact IsLocalization.Away.algebraMap_isUnit _
    have hprodQ : IsUnit (fCQ (s * f g)) := by
      rw [map_mul]
      exact hsQ.mul hfgQ'
    let v : T →+* Q := IsLocalization.Away.lift (s * f g) hprodQ
    have huv : u.comp v = RingHom.id T := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (s * f g))
      ext c
      simp [u, v, fCQ, fSQ, lift_s]
    have hvs : v.comp lift_s = algebraMap (Localization.Away s) Q := by
      apply IsLocalization.ringHom_ext (Submonoid.powers s)
      ext c
      simp [v, lift_s, fCQ, fSQ]
    have hvu : v.comp u = RingHom.id Q := by
      apply IsLocalization.ringHom_ext
        (Submonoid.powers
          (algebraMap C (Localization.Away s) (f g)))
      rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, hvs]
      rfl
    have hvbij : Function.Bijective v := by
      constructor
      · intro x y hxy
        have hx := congrArg (fun k : T →+* T => k x) huv
        have hy := congrArg (fun k : T →+* T => k y) huv
        have hx' : u (v x) = x := by simpa [Function.comp_def] using hx
        have hy' : u (v y) = y := by simpa [Function.comp_def] using hy
        exact hx'.symm.trans ((congrArg u hxy).trans hy')
      · intro y
        refine ⟨u y, ?_⟩
        have h := congrArg (fun k : Q →+* Q => k y) hvu
        simpa [Function.comp_def] using h
    let eQT : T ≃+* Q := RingEquiv.ofBijective v hvbij
    let eTQ : Q ≃+* T := eQT.symm
    have hfcomm0 : f.toRingHom.comp (algebraMap A B) = algebraMap A C := by
      ext x
      exact f.commutes x
    let _ : Algebra A C := (algebraMap A C).toAlgebra
    have heC : eTQ.toRingHom.comp fCQ = algebraMap C T := by
      ext c
      apply eQT.injective
      simp [eTQ, eQT, v, fCQ]
    have hCsR :
        (algebraMap A (Localization.Away s)).IsStandardOpenImmersion :=
      RingHom.isStandardOpenImmersion_algebraMap.2 hCs0
    have hSQR :
        (algebraMap (Localization.Away s) Q).IsStandardOpenImmersion :=
      RingHom.IsStandardOpenImmersion.algebraMap
        (algebraMap C (Localization.Away s) (f g))
    have hAQR :
        ((algebraMap (Localization.Away s) Q).comp
          (algebraMap A (Localization.Away s))).IsStandardOpenImmersion :=
      hCsR.comp hSQR
    have heR : eTQ.toRingHom.IsStandardOpenImmersion :=
      RingHom.IsStandardOpenImmersion.of_bijective eTQ.bijective
    have hATR :
        (eTQ.toRingHom.comp
          ((algebraMap (Localization.Away s) Q).comp
            (algebraMap A (Localization.Away s)))).IsStandardOpenImmersion :=
      hAQR.comp heR
    have hmapA :
        eTQ.toRingHom.comp
            ((algebraMap (Localization.Away s) Q).comp
              (algebraMap A (Localization.Away s))) = algebraMap A T := by
      ext x
      change eTQ (fCQ (algebraMap A C x)) =
        (algebraMap C T) (algebraMap A C x)
      exact DFunLike.congr_fun heC (algebraMap A C x)
    have hATR' : (algebraMap A T).IsStandardOpenImmersion := hmapA ▸ hATR
    let _ : Algebra A B := (algebraMap A B).toAlgebra
    let _ : Algebra A (Localization.Away g) :=
      @OreLocalization.instAlgebra B _ (Submonoid.powers g)
          (OreLocalization.oreSetComm (Submonoid.powers g)) A _
          (algebraMap A B).toAlgebra
    let _ : Algebra A T := (algebraMap A T).toAlgebra
    let _ : SMul A (Localization.Away g) :=
      (inferInstance : Algebra A (Localization.Away g)).toSMul
    let _ : SMul A T := (inferInstance : Algebra A T).toSMul
    let _ : IsLocalization.Away a (Localization.Away g) := ha
    have hATalg : Algebra.IsStandardOpenImmersion A T := hATR'.toAlgebra
    obtain ⟨d, hdT⟩ := hATalg
    let _ : IsLocalization.Away d T := hdT
    have hATower :
        (algebraMap (Localization.Away g) T).comp
            (algebraMap A (Localization.Away g)) = algebraMap A T := by
      ext x
      change lift_g ((algebraMap B (Localization.Away g))
        ((algebraMap A B) x)) = (algebraMap C T) ((algebraMap A C) x)
      rw [IsLocalization.Away.lift_eq]
      simp [fT]
      exact congrArg (algebraMap C T) (DFunLike.congr_fun hfcomm0 x)
    let _ : IsScalarTower A (Localization.Away g) T :=
      IsScalarTower.of_algebraMap_eq' hATower.symm
    have hunit_aT : IsUnit ((algebraMap A T) a) := by
      rw [← DFunLike.congr_fun hATower a]
      exact IsUnit.map (algebraMap (Localization.Away g) T) <|
        IsLocalization.map_units (Localization.Away g)
          (⟨a, 1, by simp⟩ : Submonoid.powers a)
    let _ : IsLocalization.Away (algebraMap A T a) T :=
      IsLocalization.away_of_isUnit_of_bijective T hunit_aT
        Function.bijective_id
    let _ : IsScalarTower A T T :=
      IsScalarTower.of_algebraMap_eq' rfl
    have hdSgT :
        IsLocalization.Away (algebraMap A (Localization.Away g) d) T :=
      IsLocalization.Away.commutes
        (Localization.Away g) T T a d
    let _ : IsLocalization.Away (algebraMap A (Localization.Away g) d) T := hdSgT
    have hSgT :
        (algebraMap (Localization.Away g) T).IsStandardOpenImmersion :=
      RingHom.IsStandardOpenImmersion.algebraMap
        (algebraMap A (Localization.Away g) d)
    have hBsg :
        (algebraMap B (Localization.Away g)).IsStandardOpenImmersion :=
      RingHom.IsStandardOpenImmersion.algebraMap g
    have hBT :
        ((algebraMap (Localization.Away g) T).comp
          (algebraMap B (Localization.Away g))).IsStandardOpenImmersion :=
      hBsg.comp hSgT
    have hcomp :
        (algebraMap (Localization.Away g) T).comp
            (algebraMap B (Localization.Away g)) = fT := by
      change lift_g.comp (algebraMap B (Localization.Away g)) = fT
      exact IsLocalization.Away.lift_comp g hfg
    have hBT' : fT.IsStandardOpenImmersion := hcomp ▸ hBT
    have hmapBT : fT = algebraMap B T := by
      ext x
      rfl
    have hBTmap : (algebraMap B T).IsStandardOpenImmersion :=
      hmapBT ▸ hBT'
    exact RingHom.isStandardOpenImmersion_algebraMap.1 hBTmap

theorem of_identifiesLocalRings_of_identifiesLocalRings
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C)
    (hB : IdentifiesLocalRings (algebraMap A B))
    (hC : IdentifiesLocalRings (algebraMap A C)) :
    IdentifiesLocalRings f.toRingHom := by
  let _ : Algebra B C := f.toRingHom.toAlgebra
  let _ : IsScalarTower A B C := IsScalarTower.of_algHom f
  intro q
  let p : PrimeSpectrum B := ⟨q.asIdeal.comap f.toRingHom, inferInstance⟩
  have hp := hB p
  have hq := hC q
  let I : Ideal A := q.asIdeal.comap (algebraMap A C)
  let J : Ideal A := (q.asIdeal.comap f.toRingHom).comap (algebraMap A B)
  have hi : I = J := by
    ext x
    change algebraMap A C x ∈ q.asIdeal ↔ f (algebraMap A B x) ∈ q.asIdeal
    rw [f.commutes]
  let e := Localization.localRingEquiv I J (RingEquiv.refl A) hi
  have hcompid := Localization.localRingHom_comp
    (I := I) (J := J) (K := p.asIdeal)
    (RingHom.id A) hi (algebraMap A B) rfl
  have hmapid :
      Localization.localRingHom I p.asIdeal (algebraMap A B) hi =
        (Localization.localRingHom J p.asIdeal (algebraMap A B) rfl).comp
          (Localization.localRingHom I J (RingHom.id A) hi) := by
    simpa only [RingHom.comp_id] using hcompid
  have hp' : Function.Bijective
      (Localization.localRingHom I p.asIdeal
        (algebraMap A B) hi) := by
    rw [hmapid]
    simpa [e, Localization.localRingEquiv] using hp.comp e.bijective
  have hic :
      I = q.asIdeal.comap (f.toRingHom.comp (algebraMap A B)) := by
    simpa only [I, J, Ideal.comap_comap] using hi
  have heq := Localization.localRingHom_comp
    (I := I) (J := p.asIdeal) (K := q.asIdeal)
    (algebraMap A B) hi f.toRingHom rfl
  have heq' :
      Localization.localRingHom I q.asIdeal
          (f.toRingHom.comp (algebraMap A B)) hic =
        (Localization.localRingHom (q.asIdeal.comap f.toRingHom)
          q.asIdeal f.toRingHom rfl).comp
          (Localization.localRingHom I (q.asIdeal.comap f.toRingHom)
            (algebraMap A B) hi) := by
    simpa [p] using heq
  have hmap :
      Localization.localRingHom I q.asIdeal
          (f.toRingHom.comp (algebraMap A B)) hic =
        Localization.localRingHom I q.asIdeal
          (algebraMap A C) rfl := by
    apply Localization.localRingHom_unique
    intro x
    simp
  have hq' : Function.Bijective
      ((Localization.localRingHom (q.asIdeal.comap f.toRingHom)
          q.asIdeal f.toRingHom rfl).comp
        (Localization.localRingHom I (q.asIdeal.comap f.toRingHom)
          (algebraMap A B) hi)) := by
    rw [← heq', hmap]
    exact hq
  constructor
  · intro x y hxy
    obtain ⟨z, hz, rfl⟩ := hp'.2 x
    obtain ⟨w, hw, rfl⟩ := hp'.2 y
    have hxy' :
        ((Localization.localRingHom (q.asIdeal.comap f.toRingHom)
            q.asIdeal f.toRingHom rfl).comp
          (Localization.localRingHom I (q.asIdeal.comap f.toRingHom)
            (algebraMap A B) hi)) z =
        ((Localization.localRingHom (q.asIdeal.comap f.toRingHom)
            q.asIdeal f.toRingHom rfl).comp
          (Localization.localRingHom I (q.asIdeal.comap f.toRingHom)
            (algebraMap A B) hi)) w := by
      change (Localization.localRingHom (q.asIdeal.comap f.toRingHom)
            q.asIdeal f.toRingHom rfl)
          ((Localization.localRingHom I p.asIdeal
            (algebraMap A B) hi) z) =
        (Localization.localRingHom (q.asIdeal.comap f.toRingHom)
            q.asIdeal f.toRingHom rfl)
          ((Localization.localRingHom I p.asIdeal
            (algebraMap A B) hi) w)
      exact hxy
    exact congrArg
      (fun t => Localization.localRingHom I (q.asIdeal.comap f.toRingHom)
        (algebraMap A B) hi t) (hq'.1 hxy')
  · intro y
    obtain ⟨z, hz⟩ := hq'.2 y
    refine ⟨Localization.localRingHom I (q.asIdeal.comap f.toRingHom)
      (algebraMap A B) hi z, ?_⟩
    change (Localization.localRingHom (q.asIdeal.comap f.toRingHom)
      q.asIdeal f.toRingHom rfl)
      ((Localization.localRingHom I (q.asIdeal.comap f.toRingHom)
        (algebraMap A B) hi) z) = y
    simpa only [RingHom.coe_comp, Function.comp_apply] using hz

/-! ## Consequences of local isomorphisms -/

theorem IsLocalIsomorphism.isEtale
    {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : IsLocalIsomorphism φ) :
    RingHom.Etale φ := by
  let _ : Algebra A B := φ.toAlgebra
  change Algebra.IsLocalIso A B at hφ
  let s : Set B := {g : B | Algebra.IsStandardOpenImmersion A (Localization.Away g)}
  apply RingHom.Etale.ofLocalizationSpanTarget φ s
    (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top A B)
  intro g
  letI : Algebra A (Localization.Away (g : B)) := inferInstance
  obtain ⟨f, hf⟩ := g.property.exists_away
  let alg0 : Algebra A (Localization.Away (g : B)) := inferInstance
  have hf0 : @IsLocalization.Away A _ f (Localization.Away (g : B)) _ alg0 := hf
  have heq0 : (algebraMap A (Localization.Away (g : B))).toAlgebra = alg0 := by
    apply IsScalarTower.Algebra.ext
    intro a x
    change (algebraMap A (Localization.Away (g : B))) a * x = a • x
    rw [Algebra.smul_def]
  have heq : (algebraMap A (Localization.Away (g : B))).toAlgebra =
      ((algebraMap B (Localization.Away (g : B))).comp φ).toAlgebra := by
    apply IsScalarTower.Algebra.ext
    intro a x
    simp only [Algebra.smul_def]
  have heq' : alg0 =
      ((algebraMap B (Localization.Away (g : B))).comp φ).toAlgebra :=
    heq0.symm.trans heq
  letI : Algebra A (Localization.Away (g : B)) :=
    ((algebraMap B (Localization.Away (g : B))).comp φ).toAlgebra
  have hf1 : @IsLocalization.Away A _ f (Localization.Away (g : B)) _
      ((algebraMap B (Localization.Away (g : B))).comp φ).toAlgebra := by
    rw [← heq']
    exact hf0
  letI : IsLocalization.Away f (Localization.Away (g : B)) := hf1
  exact Algebra.Etale.of_isLocalizationAway f

private theorem localRingHom_bijective_of_isLocalization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (q : PrimeSpectrum S)
    {I : Ideal R} [I.IsPrime] (hI0 : I = q.asIdeal.comap (algebraMap R S)) :
    Function.Bijective
      (Localization.localRingHom I q.asIdeal (algebraMap R S) hI0) := by
  let e : Localization M ≃ₐ[R] S := IsLocalization.algEquiv M _ _
  let p : PrimeSpectrum (Localization M) :=
    ⟨q.asIdeal.comap e.toRingHom, inferInstance⟩
  have he : e.toRingHom.comp (algebraMap R (Localization M)) = algebraMap R S := by
    ext x
    exact e.commutes x
  have hI : p.asIdeal.comap (algebraMap R (Localization M)) =
      q.asIdeal.comap (algebraMap R S) := by
    dsimp [p]
    exact congrArg (fun k : R →+* S => q.asIdeal.comap k) he
  have hI' : I = (p.asIdeal.comap (algebraMap R (Localization M))).comap
      (RingEquiv.refl R) := by
    rw [hI0, ← hI]
    rfl
  let a₀ : Localization.AtPrime I ≃+* Localization.AtPrime
      (p.asIdeal.comap (algebraMap R (Localization M))) :=
    Localization.localRingEquiv I
      (p.asIdeal.comap (algebraMap R (Localization M))) (RingEquiv.refl R) hI'
  let a₁ : Localization.AtPrime (p.asIdeal.comap (algebraMap R (Localization M))) ≃ₐ[R]
      Localization.AtPrime p.asIdeal :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization M p.asIdeal
  let a : Localization.AtPrime I ≃+* Localization.AtPrime p.asIdeal :=
    a₀.trans a₁.toRingEquiv
  let b : Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal :=
    Localization.localRingEquiv p.asIdeal q.asIdeal e.toRingEquiv rfl
  let c : Localization.AtPrime I →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom I q.asIdeal (algebraMap R S) hI0
  have hc : c = b.toRingHom.comp a.toRingHom := by
    apply Localization.localRingHom_unique
    intro x
    have ha : a (algebraMap R (Localization.AtPrime I) x) =
        algebraMap R (Localization.AtPrime p.asIdeal) x := by
      simp [a, a₀, a₁, Localization.localRingEquiv]
    change b (a (algebraMap R (Localization.AtPrime I) x)) =
      (algebraMap S (Localization.AtPrime q.asIdeal)) ((algebraMap R S) x)
    rw [ha]
    rw [IsScalarTower.algebraMap_apply R (Localization M)
      (Localization.AtPrime p.asIdeal)]
    change Localization.localRingHom p.asIdeal q.asIdeal e.toRingHom (by rfl) _ = _
    rw [Localization.localRingHom_to_map]
    exact congrArg (algebraMap S (Localization.AtPrime q.asIdeal))
      (DFunLike.congr_fun he x)
  change Function.Bijective c
  rw [hc]
  exact b.bijective.comp a.bijective

theorem IsLocalIsomorphism.identifiesLocalRings
    {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : IsLocalIsomorphism φ) :
    IdentifiesLocalRings φ := by
  let _ : Algebra A B := φ.toAlgebra
  change Algebra.IsLocalIso A B at hφ
  intro q
  let I : Ideal A := q.asIdeal.comap φ
  obtain ⟨g, hg, hstd⟩ := hφ.exists_notMem_isStandardOpenImmersion q.asIdeal
  have hqbasic : q ∈ PrimeSpectrum.basicOpen g := hg
  rw [← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range
    (Localization.Away g) g] at hqbasic
  obtain ⟨q', hq'⟩ := hqbasic
  have hqideal : q'.asIdeal.comap (algebraMap B (Localization.Away g)) = q.asIdeal := by
    simpa using congrArg (fun r : PrimeSpectrum B => r.asIdeal) hq'
  let T := Localization.Away g
  letI : Algebra A T := inferInstance
  obtain ⟨f, hf⟩ := hstd.exists_away
  let alg0 : Algebra A T := inferInstance
  have hf0 : @IsLocalization.Away A _ f T _ alg0 := hf
  have heq0 : (algebraMap A T).toAlgebra = alg0 := by
    apply IsScalarTower.Algebra.ext
    intro a z
    change (algebraMap A T) a * z = a • z
    rw [Algebra.smul_def]
  have heq : (algebraMap A T).toAlgebra =
      ((algebraMap B T).comp φ).toAlgebra := by
    apply IsScalarTower.Algebra.ext
    intro a z
    simp only [Algebra.smul_def]
  have heq' : alg0 = ((algebraMap B T).comp φ).toAlgebra :=
    heq0.symm.trans heq
  letI : Algebra A T := ((algebraMap B T).comp φ).toAlgebra
  have hf1 : @IsLocalization.Away A _ f T _
      ((algebraMap B T).comp φ).toAlgebra := by
    rw [← heq']
    exact hf0
  letI : IsLocalization.Away f T := hf1
  have hcomp : (algebraMap B T).comp φ = algebraMap A T := by rfl
  have hIT : I = q'.asIdeal.comap (algebraMap A T) := by
    calc
      I = q.asIdeal.comap φ := rfl
      _ = (q'.asIdeal.comap (algebraMap B T)).comap φ := by rw [hqideal]
      _ = q'.asIdeal.comap ((algebraMap B T).comp φ) := by
        rw [Ideal.comap_comap]
      _ = q'.asIdeal.comap (algebraMap A T) := by rw [hcomp]
  let c : Localization.AtPrime I →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom I q.asIdeal φ rfl
  let b : Localization.AtPrime q.asIdeal →+* Localization.AtPrime q'.asIdeal :=
    Localization.localRingHom q.asIdeal q'.asIdeal (algebraMap B T) hqideal.symm
  let d : Localization.AtPrime I →+* Localization.AtPrime q'.asIdeal :=
    Localization.localRingHom I q'.asIdeal (algebraMap A T) hIT
  have hb : Function.Bijective b := by
    exact localRingHom_bijective_of_isLocalization
      (R := B) (S := T) (Submonoid.powers g) q' hqideal.symm
  have hd : Function.Bijective d := by
    exact localRingHom_bijective_of_isLocalization
      (R := A) (S := T) (Submonoid.powers f) q' hIT
  have hdc : d = b.comp c := by
    apply Localization.localRingHom_unique
    intro a
    simp [b, c, d, hcomp, Localization.localRingHom_to_map]
    exact congrArg (algebraMap T (Localization.AtPrime q'.asIdeal))
      (DFunLike.congr_fun hcomp a)
  change Function.Bijective c
  constructor
  · intro x y hxy
    apply hd.1
    rw [hdc]
    exact congrArg b hxy
  · intro y
    obtain ⟨x, hx⟩ := hd.2 (b y)
    refine ⟨x, ?_⟩
    apply hb.1
    rw [← hx, hdc]
    rfl

theorem IsLocalIsomorphism.isQuasiFinite
    {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : IsLocalIsomorphism φ) :
    RingHom.QuasiFinite φ := by
  let _ : Algebra A B := φ.toAlgebra
  change Algebra.IsLocalIso A B at hφ
  let s : Set B := {g : B | Algebra.IsStandardOpenImmersion A (Localization.Away g)}
  apply RingHom.QuasiFinite.ofLocalizationSpanTarget φ s
    (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top A B)
  intro g
  letI : Algebra A (Localization.Away (g : B)) := inferInstance
  obtain ⟨f, hf⟩ := g.property.exists_away
  let alg0 : Algebra A (Localization.Away (g : B)) := inferInstance
  have hf0 : @IsLocalization.Away A _ f (Localization.Away (g : B)) _ alg0 := hf
  have heq0 : (algebraMap A (Localization.Away (g : B))).toAlgebra = alg0 := by
    apply IsScalarTower.Algebra.ext
    intro a x
    change (algebraMap A (Localization.Away (g : B))) a * x = a • x
    rw [Algebra.smul_def]
  have heq : (algebraMap A (Localization.Away (g : B))).toAlgebra =
      ((algebraMap B (Localization.Away (g : B))).comp φ).toAlgebra := by
    apply IsScalarTower.Algebra.ext
    intro a x
    simp only [Algebra.smul_def]
  have heq' : alg0 =
      ((algebraMap B (Localization.Away (g : B))).comp φ).toAlgebra :=
    heq0.symm.trans heq
  letI : Algebra A (Localization.Away (g : B)) :=
    ((algebraMap B (Localization.Away (g : B))).comp φ).toAlgebra
  have hf1 : @IsLocalization.Away A _ f (Localization.Away (g : B)) _
      ((algebraMap B (Localization.Away (g : B))).comp φ).toAlgebra := by
    rw [← heq']
    exact hf0
  letI : IsLocalization.Away f (Localization.Away (g : B)) := hf1
  let _ : SMul A (Localization.Away (g : B)) :=
    (inferInstance : Algebra A (Localization.Away (g : B))).toSMul
  letI : IsScalarTower A A (Localization.Away (g : B)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact Algebra.QuasiFinite.of_isLocalization (Submonoid.powers f)

/-! ## A finite standard-open presentation -/

theorem IsLocalIsomorphism.exists_finite_standardOpen_cover
    {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : IsLocalIsomorphism φ) :
    ∃ (n : ℕ) (g : Fin n → B) (f : Fin n → A),
      Ideal.span (Set.range g) = ⊤ ∧
        ∀ i, ∃ e : Localization.Away (f i) ≃+* Localization.Away (g i),
          e.toRingHom.comp (algebraMap A (Localization.Away (f i))) =
            (algebraMap B (Localization.Away (g i))).comp φ := by
  classical
  let _ : Algebra A B := φ.toAlgebra
  change Algebra.IsLocalIso A B at hφ
  let s : Set B := {g : B | Algebra.IsStandardOpenImmersion A (Localization.Away g)}
  have hs := Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top A B
  obtain ⟨t, ht, ht_top⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  let eFin : t ≃ Fin t.card := t.equivFin
  let g : Fin t.card → B := fun i => (eFin.symm i).1
  have haway : ∀ x : t, ∃ f : A, IsLocalization.Away f (Localization.Away x.1) := by
    intro x
    have hx : Algebra.IsStandardOpenImmersion A (Localization.Away x.1) := ht x.2
    exact hx.exists_away
  choose f hf using haway
  let f' : Fin t.card → A := fun i => f (eFin.symm i)
  refine ⟨t.card, g, f', ?_, ?_⟩
  · apply le_antisymm
    · rw [← ht_top]
      apply Ideal.span_mono
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      exact (eFin.symm i).property
    · rw [← ht_top]
      apply Ideal.span_le.mpr
      intro x hx
      let y : t := ⟨x, hx⟩
      have hy : y.1 ∈ Ideal.span (Set.range g) := by
        apply Ideal.subset_span
        refine ⟨eFin y, ?_⟩
        simp [g, eFin]
      exact hy
  · intro i
    let x : t := eFin.symm i
    letI : Algebra A (Localization.Away x.1) := inferInstance
    let alg0 : Algebra A (Localization.Away x.1) := inferInstance
    have hf0 : @IsLocalization.Away A _ (f x) (Localization.Away x.1) _ alg0 := hf x
    have heq0 : (algebraMap A (Localization.Away x.1)).toAlgebra = alg0 := by
      apply IsScalarTower.Algebra.ext
      intro a z
      change (algebraMap A (Localization.Away x.1)) a * z = a • z
      rw [Algebra.smul_def]
    have heq : (algebraMap A (Localization.Away x.1)).toAlgebra =
        ((algebraMap B (Localization.Away x.1)).comp φ).toAlgebra := by
      apply IsScalarTower.Algebra.ext
      intro a z
      simp only [Algebra.smul_def]
    have heq' : alg0 = ((algebraMap B (Localization.Away x.1)).comp φ).toAlgebra :=
      heq0.symm.trans heq
    letI : Algebra A (Localization.Away x.1) :=
      ((algebraMap B (Localization.Away x.1)).comp φ).toAlgebra
    have hf1 : @IsLocalization.Away A _ (f x) (Localization.Away x.1) _
        ((algebraMap B (Localization.Away x.1)).comp φ).toAlgebra := by
      rw [← heq']
      exact hf0
    letI : IsLocalization.Away (f x) (Localization.Away x.1) := hf1
    let e : Localization.Away (f x) ≃ₐ[A] Localization.Away x.1 :=
      IsLocalization.algEquiv (Submonoid.powers (f x)) _ _
    refine ⟨e.toRingEquiv, ?_⟩
    ext a
    change e (algebraMap A (Localization.Away (f x)) a) =
      (algebraMap B (Localization.Away x.1)) (φ a)
    calc
      e (algebraMap A (Localization.Away (f x)) a) =
          algebraMap A (Localization.Away x.1) a := e.commutes a
      _ = (algebraMap B (Localization.Away x.1)) (φ a) := rfl

/-! ## Locally ringed spaces over a fixed base -/

/-- The adjoint form of the structure-sheaf map of a locally ringed-space
morphism.  This is the canonical map from the pullback of the target sheaf to
the source sheaf. -/
def structureSheafPullbackMap
    {X Y : LocallyRingedSpace.{u}} (p : Y ⟶ X) :
    (TopCat.Sheaf.pullback CommRingCat p.base).obj X.𝒪 ⟶ Y.𝒪 :=
  let c : X.𝒪 ⟶ (TopCat.Sheaf.pushforward CommRingCat p.base).obj Y.𝒪 :=
    (TopCat.Sheaf.forget CommRingCat X.toTopCat).preimage p.toShHom.hom.c
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base).homEquiv
    X.𝒪 Y.𝒪).symm c

/-- The structure sheaf of the source is the pullback of the target sheaf. -/
def IsPullbackStructureSheaf
    {X Y : LocallyRingedSpace.{u}} (p : Y ⟶ X) : Prop :=
  IsIso (structureSheafPullbackMap p)

abbrev LRSOverHom
    {X Y Z : LocallyRingedSpace.{u}} (p : Y ⟶ X) (q : Z ⟶ X) :=
  (CostructuredArrow.mk q : CostructuredArrow (𝟭 LocallyRingedSpace) X) ⟶
    CostructuredArrow.mk p

abbrev TopOverHom
    {X Y Z : LocallyRingedSpace.{u}} (p : Y ⟶ X) (q : Z ⟶ X) :=
  (CostructuredArrow.mk q.base : CostructuredArrow (𝟭 TopCat) X.toTopCat) ⟶
    CostructuredArrow.mk p.base

/-- Forget a locally ringed-space morphism over `X` to its underlying map of
topological spaces over `X`. -/
def lrsOverHomToTopOverHom
    {X Y Z : LocallyRingedSpace.{u}} (p : Y ⟶ X) (q : Z ⟶ X) :
    LRSOverHom p q → TopOverHom p q := fun f =>
  CostructuredArrow.homMk f.left.base (by
    simpa using congrArg (fun h : Z ⟶ X => h.base) (CostructuredArrow.w f))

theorem fullyFaithfulSpacesOverX
    {X Y Z : LocallyRingedSpace.{u}} (p : Y ⟶ X) (q : Z ⟶ X)
    (hp : IsPullbackStructureSheaf p) :
    Function.Bijective (lrsOverHomToTopOverHom p q) := by
  letI : IsIso (structureSheafPullbackMap p) := hp
  have hpstalk (y : Y) : IsIso (p.stalkMap y) := by
    let P := structureSheafPullbackMap p
    let ePull := (TopCat.Sheaf.pullbackIso CommRingCat p.base).app X.𝒪
    let eUnit := CategoryTheory.toSheafify (Opens.grothendieckTopology
      (Y.toPresheafedSpace : TopCat))
      ((TopCat.Sheaf.forget CommRingCat X.toTopCat ⋙
        TopCat.Presheaf.pullback CommRingCat p.base).obj X.𝒪)
    haveI : IsIso
        (TopCat.Presheaf.stalkPullbackIso CommRingCat p.base X.𝒪.1 y).hom := by
      infer_instance
    haveI : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat y).map eUnit) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y CommRingCat
        ((TopCat.Presheaf.pullback CommRingCat p.base).obj X.𝒪.1)
    haveI : IsIso ePull.inv.1 := by
      exact (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map_isIso ePull.inv
    haveI : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat y).map ePull.inv.1) := by
      infer_instance
    haveI : IsIso P.hom := by
      exact (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map_isIso P
    haveI : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat y).map P.hom) := by
      exact (TopCat.Presheaf.stalkFunctor CommRingCat y).map_isIso P.hom
    haveI : IsIso
        ((TopCat.Presheaf.stalkFunctor CommRingCat y).map eUnit ≫
          (TopCat.Presheaf.stalkFunctor CommRingCat y).map ePull.inv.1) := by
      infer_instance
    let vIso := asIso
      ((TopCat.Presheaf.stalkFunctor CommRingCat y).map eUnit ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat y).map ePull.inv.1)
    let uIso :=
      (TopCat.Presheaf.stalkPullbackIso CommRingCat p.base X.𝒪.1 y).trans vIso
    let u := uIso.hom
    haveI : IsIso u := by
      infer_instance
    have heq : u ≫ (TopCat.Presheaf.stalkFunctor CommRingCat y).map P.hom =
        p.stalkMap y := by
      apply TopCat.Presheaf.stalk_hom_ext X.𝒪.1
      intro U hy
      dsimp [u, uIso, vIso, Iso.trans, TopCat.Presheaf.stalkPullbackIso]
      change
        ((TopCat.Presheaf.germ X.𝒪.1 U ((ConcreteCategory.hom p.base) y) hy ≫
            TopCat.Presheaf.stalkPullbackHom CommRingCat p.base X.𝒪.1 y) ≫
          (asIso
              ((TopCat.Presheaf.stalkFunctor CommRingCat y).map eUnit ≫
                (TopCat.Presheaf.stalkFunctor CommRingCat y).map ePull.inv.hom)).hom ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat y).map P.hom) =
          TopCat.Presheaf.germ X.𝒪.1 U ((ConcreteCategory.hom p.base) y) hy ≫
            LocallyRingedSpace.Hom.stalkMap p y
      rw [TopCat.Presheaf.germ_stalkPullbackHom]
      dsimp [asIso]
      have hmap := TopCat.Presheaf.stalkFunctor_map_germ
        (C := CommRingCat) ((TopologicalSpace.Opens.map p.base).obj U) y hy eUnit
      have hmap' :
          ((TopCat.Presheaf.pullback CommRingCat p.base).obj
              ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)).germ
              ((TopologicalSpace.Opens.map p.base).obj U) y hy ≫
            (TopCat.Presheaf.stalkFunctor CommRingCat y).map eUnit =
          eUnit.app (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) ≫
            TopCat.Presheaf.germ
              (sheafify (Opens.grothendieckTopology
                (Y.toPresheafedSpace : TopCat))
                ((TopCat.Presheaf.pullback CommRingCat p.base).obj
                  ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)))
              ((TopologicalSpace.Opens.map p.base).obj U) y hy := by
        simpa only [Functor.comp_obj] using hmap
      change
        (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat p.base).unit.app
              ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)).app
            (Opposite.op U) ≫
          ((TopCat.Presheaf.pullback CommRingCat p.base).obj
              ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)).germ
            ((TopologicalSpace.Opens.map p.base).obj U) y hy ≫
          ((TopCat.Presheaf.stalkFunctor CommRingCat y).map eUnit ≫
              (TopCat.Presheaf.stalkFunctor CommRingCat y).map ePull.inv.hom) ≫
            (TopCat.Presheaf.stalkFunctor CommRingCat y).map P.hom) =
          TopCat.Presheaf.germ X.𝒪.1 U ((ConcreteCategory.hom p.base) y) hy ≫
            LocallyRingedSpace.Hom.stalkMap p y
      calc
        _ = ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat p.base).unit.app
              ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)).app
              (Opposite.op U) ≫
            (((TopCat.Presheaf.pullback CommRingCat p.base).obj
                ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)).germ
                ((TopologicalSpace.Opens.map p.base).obj U) y hy ≫
              (TopCat.Presheaf.stalkFunctor CommRingCat y).map eUnit) ≫
            ((TopCat.Presheaf.stalkFunctor CommRingCat y).map ePull.inv.hom ≫
              (TopCat.Presheaf.stalkFunctor CommRingCat y).map P.hom) := by
          rfl
        _ = _ := by
          rw [hmap']
          have hmap2 := TopCat.Presheaf.stalkFunctor_map_germ
            (C := CommRingCat) ((TopologicalSpace.Opens.map p.base).obj U) y hy
            ePull.inv.hom
          have hmap3 := TopCat.Presheaf.stalkFunctor_map_germ
            (C := CommRingCat) ((TopologicalSpace.Opens.map p.base).obj U) y hy P.hom
          have hmap2' :
              TopCat.Presheaf.germ
                  (sheafify (Opens.grothendieckTopology (Y.toTopCat : Type _))
                    ((TopCat.Presheaf.pullback CommRingCat p.base).obj
                      ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)))
                  ((TopologicalSpace.Opens.map p.base).obj U) y hy ≫
                (TopCat.Presheaf.stalkFunctor CommRingCat y).map ePull.inv.hom =
              ePull.inv.hom.app (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) ≫
                TopCat.Presheaf.germ ((TopCat.Sheaf.pullback CommRingCat p.base).obj X.𝒪).obj
                  ((TopologicalSpace.Opens.map p.base).obj U) y hy := by
            convert hmap2 using 1 <;> rfl
          calc
            _ = ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat p.base).unit.app
                  ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)).app
                  (Opposite.op U) ≫
                (eUnit.app (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) ≫
                  (TopCat.Presheaf.germ
                    (sheafify (Opens.grothendieckTopology (Y.toTopCat : Type _))
                      ((TopCat.Presheaf.pullback CommRingCat p.base).obj
                        ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)))
                    ((TopologicalSpace.Opens.map p.base).obj U) y hy ≫
                    (TopCat.Presheaf.stalkFunctor CommRingCat y).map ePull.inv.hom)) ≫
                (TopCat.Presheaf.stalkFunctor CommRingCat y).map P.hom := by
              rfl
            _ = _ := by
              rw [hmap2']
              calc
                _ = ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat p.base).unit.app
                      ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)).app
                      (Opposite.op U) ≫
                    (eUnit.app (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) ≫
                      ePull.inv.hom.app
                        (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) ≫
                      (TopCat.Presheaf.germ
                        ((TopCat.Sheaf.pullback CommRingCat p.base).obj X.𝒪).obj
                        ((TopologicalSpace.Opens.map p.base).obj U) y hy ≫
                        (TopCat.Presheaf.stalkFunctor CommRingCat y).map P.hom)) := by
                  rfl
                _ = _ := by
                  rw [hmap3]
                  let c : X.𝒪 ⟶
                      (TopCat.Sheaf.pushforward CommRingCat p.base).obj Y.𝒪 :=
                    (TopCat.Sheaf.forget CommRingCat X.toTopCat).preimage
                      (LocallyRingedSpace.Hom.toShHom p).hom.c
                  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction
                    CommRingCat p.base
                  let J := Opens.grothendieckTopology (X.toPresheafedSpace : TopCat)
                  let K := Opens.grothendieckTopology (Y.toPresheafedSpace : TopCat)
                  let adj' := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (TopologicalSpace.Opens.map p.base) CommRingCat J K
                  have hunit :
                      adj.unit.app X.𝒪 ≫
                          (TopCat.Sheaf.pushforward CommRingCat p.base).map ePull.hom =
                        adj'.unit.app X.𝒪 := by
                    convert Adjunction.unit_leftAdjointUniq_hom_app
                      (Functor.sheafAdjunctionContinuous
                        (TopologicalSpace.Opens.map p.base) CommRingCat J K)
                      adj' X.𝒪 using 1 <;> rfl
                  have hP : adj.homEquiv X.𝒪 Y.𝒪 P = c := by
                    dsimp [P, structureSheafPullbackMap, c, adj]
                    exact (adj.homEquiv X.𝒪 Y.𝒪).apply_symm_apply _
                  rw [Adjunction.homEquiv_unit] at hP
                  have hPapp := congrArg (fun f => f.hom.app (Opposite.op U)) hP
                  have hfactor :
                      adj.unit.app X.𝒪 ≫
                          (TopCat.Sheaf.pushforward CommRingCat p.base).map P =
                        adj'.unit.app X.𝒪 ≫
                          (TopCat.Sheaf.pushforward CommRingCat p.base).map ePull.inv ≫
                          (TopCat.Sheaf.pushforward CommRingCat p.base).map P := by
                    calc
                      _ = (adj.unit.app X.𝒪 ≫
                          (TopCat.Sheaf.pushforward CommRingCat p.base).map ePull.hom) ≫
                          (TopCat.Sheaf.pushforward CommRingCat p.base).map
                            (ePull.inv ≫ P) := by
                        simp only [Functor.map_comp, Category.assoc]
                        rw [← Category.assoc
                            ((TopCat.Sheaf.pushforward CommRingCat p.base).map ePull.hom)
                            ((TopCat.Sheaf.pushforward CommRingCat p.base).map ePull.inv)
                            ((TopCat.Sheaf.pushforward CommRingCat p.base).map P),
                          ← (TopCat.Sheaf.pushforward CommRingCat p.base).map_comp
                            ePull.hom ePull.inv,
                          Iso.hom_inv_id,
                          (TopCat.Sheaf.pushforward CommRingCat p.base).map_id]
                        simp only [Category.id_comp, Category.comp_id]
                      _ = _ := by
                        rw [hunit, (TopCat.Sheaf.pushforward CommRingCat p.base).map_comp]
                        rfl
                  have hfactor_app :=
                    congrArg (fun f => f.hom.app (Opposite.op U)) hfactor
                  have hunit' :
                      (adj'.unit.app X.𝒪).hom.app (Opposite.op U) =
                        ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat p.base).unit.app
                              ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)).app
                            (Opposite.op U) ≫
                          eUnit.app
                            (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) := by
                    rfl
                  have hfactor_app' :
                      (adj.unit.app X.𝒪).hom.app (Opposite.op U) ≫
                          P.hom.app
                            (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) =
                        (adj'.unit.app X.𝒪).hom.app (Opposite.op U) ≫
                          ePull.inv.hom.app
                            (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) ≫
                          P.hom.app
                            (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) := by
                    change
                      ((adj.unit.app X.𝒪).hom.app (Opposite.op U) ≫
                        P.hom.app
                          (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U))) =
                        ((adj'.unit.app X.𝒪).hom.app (Opposite.op U) ≫
                          ePull.inv.hom.app
                            (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) ≫
                          P.hom.app
                            (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)))
                    exact hfactor_app
                  have hunit_app :
                      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat p.base).unit.app
                              ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)).app
                            (Opposite.op U) ≫
                          eUnit.app
                            (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) ≫
                          ePull.inv.hom.app
                            (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) ≫
                          P.hom.app
                            (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) =
                        (adj'.unit.app X.𝒪).hom.app (Opposite.op U) ≫
                          ePull.inv.hom.app
                            (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) ≫
                          P.hom.app
                            (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) := by
                    rw [hunit']
                    rfl
                  have hchain :
                      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat p.base).unit.app
                              ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪)).app
                            (Opposite.op U) ≫
                        eUnit.app (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) ≫
                        ePull.inv.hom.app
                          (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) ≫
                        P.hom.app
                          (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U)) =
                      c.hom.app (Opposite.op U) := by
                    exact hunit_app.trans (hfactor_app'.symm.trans hPapp)
                  have hprefix := congrArg
                    (fun k => k ≫ TopCat.Presheaf.germ Y.𝒪.obj
                      ((TopologicalSpace.Opens.map p.base).obj U) y hy)
                    hchain
                  have hobj :
                      X.𝒪.obj.obj =
                        ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪).obj := by
                    rfl
                  have hobjU :
                      X.𝒪.obj.obj (Opposite.op U) =
                        ((TopCat.Sheaf.forget CommRingCat X.toTopCat).obj X.𝒪).obj
                          (Opposite.op U) := by
                    rfl
                  have hc_app :
                      c.hom.app (Opposite.op U) =
                        (LocallyRingedSpace.Hom.toShHom p).hom.c.app
                          (Opposite.op U) := by
                    have hc :
                        (TopCat.Sheaf.forget CommRingCat X.toTopCat).map c =
                          (LocallyRingedSpace.Hom.toShHom p).hom.c := by
                      dsimp [c]
                      apply (TopCat.Sheaf.forget CommRingCat X.toTopCat).map_preimage
                    exact congrArg (fun f => f.app (Opposite.op U)) hc
                  have hbase :
                      (TopologicalSpace.Opens.map
                          (LocallyRingedSpace.Hom.toShHom p).hom.base).obj U =
                        (TopologicalSpace.Opens.map p.base).obj U := by
                    rfl
                  calc
                    _ = c.hom.app (Opposite.op U) ≫
                        TopCat.Presheaf.germ Y.𝒪.obj
                          ((TopologicalSpace.Opens.map p.base).obj U) y hy := by
                      convert hprefix using 1
                      exact Iff.rfl
                    _ = _ := by
                      rw [hc_app]
                      dsimp only [LocallyRingedSpace.Hom.stalkMap,
                        TopCat.Sheaf.forget, LocallyRingedSpace.𝒪,
                        SheafedSpace.sheaf, Functor.id_obj, Functor.comp_obj,
                        LocallyRingedSpace.Hom.toShHom, InducedCategory.homMk,
                        hbase]
                      exact
                        (PresheafedSpace.stalkMap_germ
                          (LocallyRingedSpace.Hom.toShHom p).hom U y hy).symm
    rw [← heq]
    let wIso := uIso.trans
      (asIso ((TopCat.Presheaf.stalkFunctor CommRingCat y).map P.hom))
    change IsIso wIso.hom
    infer_instance
  classical
  refine ⟨?_, ?_⟩
  · intro f g hfg
    have hbase : f.left.base = g.left.base :=
      congrArg (fun k => k.left) hfg
    apply CostructuredArrow.hom_ext
    · apply LocallyRingedSpace.Hom.ext'
      apply PresheafedSpace.Hom.ext
      · let Sf := (TopCat.Sheaf.pushforward CommRingCat f.left.base).obj Z.𝒪
        let Sg := (TopCat.Sheaf.pushforward CommRingCat g.left.base).obj Z.𝒪
        let cp : X.𝒪 ⟶
            (TopCat.Sheaf.pushforward CommRingCat p.base).obj Y.𝒪 :=
          (TopCat.Sheaf.forget CommRingCat X.toTopCat).preimage
            (LocallyRingedSpace.Hom.toShHom p).hom.c
        let cf : Y.𝒪 ⟶ Sf :=
          (TopCat.Sheaf.forget CommRingCat Y.toTopCat).preimage
            f.left.toShHom.hom.c
        let cg : Y.𝒪 ⟶ Sg :=
          (TopCat.Sheaf.forget CommRingCat Y.toTopCat).preimage
            g.left.toShHom.hom.c
        let qMap : X.𝒪 ⟶
            (TopCat.Sheaf.pushforward CommRingCat q.base).obj Z.𝒪 :=
          (TopCat.Sheaf.forget CommRingCat X.toTopCat).preimage
            q.toShHom.hom.c
        have hfcomp :
            (f.left.toHom ≫ p.toHom : Z.toPresheafedSpace ⟶ X.toPresheafedSpace) =
              q.toHom := by
          rw [← LocallyRingedSpace.comp_toHom]
          exact congrArg (fun h : Z ⟶ X => h.toHom) (CostructuredArrow.w f)
        have hgcomp :
            (g.left.toHom ≫ p.toHom : Z.toPresheafedSpace ⟶ X.toPresheafedSpace) =
              q.toHom := by
          rw [← LocallyRingedSpace.comp_toHom]
          exact congrArg (fun h : Z ⟶ X => h.toHom) (CostructuredArrow.w g)
        have hfbase : f.left.base ≫ p.base = q.base := by
          change (f.left ≫ p).base = q.base
          exact congrArg (fun h : Z ⟶ X => h.base) (CostructuredArrow.w f)
        have hgbase : g.left.base ≫ p.base = q.base := by
          change (g.left ≫ p).base = q.base
          exact congrArg (fun h : Z ⟶ X => h.base) (CostructuredArrow.w g)
        have hfpush :
            (TopCat.Sheaf.pushforward CommRingCat p.base).obj Sf =
              (TopCat.Sheaf.pushforward CommRingCat q.base).obj Z.𝒪 := by
          dsimp [Sf]
          exact congrArg
            (fun b => (TopCat.Sheaf.pushforward CommRingCat b).obj Z.𝒪) hfbase
        have hgpush :
            (TopCat.Sheaf.pushforward CommRingCat p.base).obj Sg =
              (TopCat.Sheaf.pushforward CommRingCat q.base).obj Z.𝒪 := by
          dsimp [Sg]
          exact congrArg
            (fun b => (TopCat.Sheaf.pushforward CommRingCat b).obj Z.𝒪) hgbase
        let hfHom : Z.toPresheafedSpace ⟶ X.toPresheafedSpace :=
          f.left.toHom ≫ p.toHom
        let hgHom : Z.toPresheafedSpace ⟶ X.toPresheafedSpace :=
          g.left.toHom ≫ p.toHom
        have hfbase' :
            (TopologicalSpace.Opens.map hfHom.base).op =
              (TopologicalSpace.Opens.map q.toHom.base).op := by
          exact congrArg (fun h : Z.toPresheafedSpace ⟶ X.toPresheafedSpace =>
            (TopologicalSpace.Opens.map h.base).op) hfcomp
        have hgbase' :
            (TopologicalSpace.Opens.map hgHom.base).op =
              (TopologicalSpace.Opens.map q.toHom.base).op := by
          exact congrArg (fun h : Z.toPresheafedSpace ⟶ X.toPresheafedSpace =>
            (TopologicalSpace.Opens.map h.base).op) hgcomp
        have hfcomp_c :
            (f.left.toHom ≫ p.toHom : Z.toPresheafedSpace ⟶ X.toPresheafedSpace).c ≫
                Functor.whiskerRight
                  (eqToHom (by
                    exact hfbase')) Z.presheaf =
              q.toHom.c := by
          apply NatTrans.ext
          funext U
          rw [NatTrans.comp_app, Functor.whiskerRight_app]
          rw [PresheafedSpace.congr_app hfcomp U]
          rw [Category.assoc, ← Z.presheaf.map_comp]
          rw [eqToHom_app]
          simp only [eqToHom_trans, eqToHom_refl, Functor.map_id, Z.presheaf.map_id,
            Category.comp_id]
          exact Category.comp_id _
        have hgcomp_c :
            (g.left.toHom ≫ p.toHom : Z.toPresheafedSpace ⟶ X.toPresheafedSpace).c ≫
                Functor.whiskerRight
                  (eqToHom (by
                    exact hgbase')) Z.presheaf =
              q.toHom.c := by
          apply NatTrans.ext
          funext U
          rw [NatTrans.comp_app, Functor.whiskerRight_app]
          rw [PresheafedSpace.congr_app hgcomp U]
          rw [Category.assoc, ← Z.presheaf.map_comp]
          rw [eqToHom_app]
          simp only [eqToHom_trans, eqToHom_refl, Functor.map_id, Z.presheaf.map_id,
            Category.comp_id]
          exact Category.comp_id _
        have hfpush_map :
            (TopCat.Sheaf.forget CommRingCat X.toTopCat).map (eqToHom hfpush) =
              Functor.whiskerRight (eqToHom hfbase') Z.presheaf := by
          apply NatTrans.ext
          funext U
          simpa [TopCat.Sheaf.forget, TopCat.Sheaf.pushforward,
            TopCat.Sheaf.pushforward_map, TopCat.Sheaf.pushforward_obj_val,
            TopCat.Presheaf.pushforward_map_app',
            TopCat.Presheaf.pushforwardEq_hom_app,
            Functor.whiskerRight_app, eqToHom_app, eqToHom_map,
            eqToHom_trans, hfHom, Category.assoc] using
            (TopCat.Presheaf.pushforwardEq_hom_app (C := CommRingCat)
              (f := hfHom) (g := q.toHom) hfcomp Z.presheaf U)
        have hfc : cp ≫
              (TopCat.Sheaf.pushforward CommRingCat p.base).map cf =
            qMap ≫ eqToHom hfpush.symm := by
          apply (TopCat.Sheaf.forget CommRingCat X.toTopCat).map_injective
          rw [Functor.map_comp]
          have hcp :
              (TopCat.Sheaf.forget CommRingCat X.toTopCat).map cp =
                (LocallyRingedSpace.Hom.toShHom p).hom.c := by
            dsimp [cp, TopCat.Sheaf.forget]
            apply (TopCat.Sheaf.forget CommRingCat X.toTopCat).map_preimage
          have hcf :
              (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map cf =
                (LocallyRingedSpace.Hom.toShHom f.left).hom.c := by
            dsimp [cf, TopCat.Sheaf.forget]
            apply (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map_preimage
          have hFcf :
              (TopCat.Sheaf.forget CommRingCat X.toTopCat).map
                  ((TopCat.Sheaf.pushforward CommRingCat p.base).map cf) =
                (TopCat.Presheaf.pushforward CommRingCat p.base).map
                  ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map cf) := by
            rfl
          have hq :
              (TopCat.Sheaf.forget CommRingCat X.toTopCat).map qMap =
                (LocallyRingedSpace.Hom.toShHom q).hom.c := by
            dsimp [qMap, TopCat.Sheaf.forget]
            apply (TopCat.Sheaf.forget CommRingCat X.toTopCat).map_preimage
          have hqcomp :
              (TopCat.Sheaf.forget CommRingCat X.toTopCat).map
                  (qMap ≫ eqToHom hfpush.symm) =
                (TopCat.Sheaf.forget CommRingCat X.toTopCat).map qMap ≫
                  (TopCat.Sheaf.forget CommRingCat X.toTopCat).map
                    (eqToHom hfpush.symm) := by
            rw [Functor.map_comp]
          rw [hcp, hFcf, hcf, hqcomp, hq]
          apply (cancel_mono
            ((TopCat.Sheaf.forget CommRingCat X.toTopCat).map (eqToHom hfpush))).1
          simp only [eqToHom_map, eqToHom_trans, eqToHom_refl, Functor.map_id,
            Category.comp_id, Category.id_comp, Category.assoc]
          apply NatTrans.ext
          funext U
          rw [NatTrans.comp_app]
          change
            (p.toHom.c.app U ≫
              f.left.toHom.c.app
                (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U.unop))) ≫ _ = _
          have hfcomp_c' := hfcomp_c
          erw [PresheafedSpace.comp_c] at hfcomp_c'
          have hfcomp_app := congrArg (fun k => k.app U) hfcomp_c'
          erw [NatTrans.comp_app, Functor.whiskerRight_app] at hfcomp_app
          erw [NatTrans.comp_app]
          convert hfcomp_app using 1 <;>
            simp [TopCat.Sheaf.forget, LocallyRingedSpace.𝒪, SheafedSpace.sheaf,
              LocallyRingedSpace.Hom.toShHom, InducedCategory.homMk,
              TopCat.Sheaf.pushforward_map, TopCat.Sheaf.pushforward_obj_val,
              TopCat.Presheaf.pushforward_map_app', NatTrans.comp_app,
              Functor.whiskerRight_app, eqToHom_app, eqToHom_map, eqToHom_trans,
              Category.assoc]
          constructor
          · intro _
            exact hfcomp_app
          · intro h
            erw [NatTrans.comp_app]
            simp only [eqToHom_map, eqToHom_trans, eqToHom_refl, Functor.map_id,
              Category.comp_id, Category.id_comp, Category.assoc]
            convert h using 1 <;>
              try rfl
            all_goals
              rename_i htype
              cases htype <;>
              exact eqRec_heq _ _
        have hgc : cp ≫
              (TopCat.Sheaf.pushforward CommRingCat p.base).map cg =
            qMap ≫ eqToHom hgpush.symm := by
          apply (TopCat.Sheaf.forget CommRingCat X.toTopCat).map_injective
          rw [Functor.map_comp]
          have hcp :
              (TopCat.Sheaf.forget CommRingCat X.toTopCat).map cp =
                (LocallyRingedSpace.Hom.toShHom p).hom.c := by
            dsimp [cp, TopCat.Sheaf.forget]
            apply (TopCat.Sheaf.forget CommRingCat X.toTopCat).map_preimage
          have hcg :
              (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map cg =
                (LocallyRingedSpace.Hom.toShHom g.left).hom.c := by
            dsimp [cg, TopCat.Sheaf.forget]
            apply (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map_preimage
          have hFcg :
              (TopCat.Sheaf.forget CommRingCat X.toTopCat).map
                  ((TopCat.Sheaf.pushforward CommRingCat p.base).map cg) =
                (TopCat.Presheaf.pushforward CommRingCat p.base).map
                  ((TopCat.Sheaf.forget CommRingCat Y.toTopCat).map cg) := by
            rfl
          have hq :
              (TopCat.Sheaf.forget CommRingCat X.toTopCat).map qMap =
                (LocallyRingedSpace.Hom.toShHom q).hom.c := by
            dsimp [qMap, TopCat.Sheaf.forget]
            apply (TopCat.Sheaf.forget CommRingCat X.toTopCat).map_preimage
          have hqcomp :
              (TopCat.Sheaf.forget CommRingCat X.toTopCat).map
                  (qMap ≫ eqToHom hgpush.symm) =
                (TopCat.Sheaf.forget CommRingCat X.toTopCat).map qMap ≫
                  (TopCat.Sheaf.forget CommRingCat X.toTopCat).map
                    (eqToHom hgpush.symm) := by
            rw [Functor.map_comp]
          rw [hcp, hFcg, hcg, hqcomp, hq]
          apply (cancel_mono
            ((TopCat.Sheaf.forget CommRingCat X.toTopCat).map (eqToHom hgpush))).1
          simp only [eqToHom_map, eqToHom_trans, eqToHom_refl, Functor.map_id,
            Category.comp_id, Category.id_comp, Category.assoc]
          apply NatTrans.ext
          funext U
          rw [NatTrans.comp_app]
          change
            (p.toHom.c.app U ≫
              g.left.toHom.c.app
                (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U.unop))) ≫ _ = _
          have hgcomp_c' := hgcomp_c
          erw [PresheafedSpace.comp_c] at hgcomp_c'
          have hgcomp_app := congrArg (fun k => k.app U) hgcomp_c'
          erw [NatTrans.comp_app, Functor.whiskerRight_app] at hgcomp_app
          erw [NatTrans.comp_app]
          convert hgcomp_app using 1 <;>
            simp [TopCat.Sheaf.forget, LocallyRingedSpace.𝒪, SheafedSpace.sheaf,
              LocallyRingedSpace.Hom.toShHom, InducedCategory.homMk,
              TopCat.Sheaf.pushforward_map, TopCat.Sheaf.pushforward_obj_val,
              TopCat.Presheaf.pushforward_map_app', NatTrans.comp_app,
              Functor.whiskerRight_app, eqToHom_app, eqToHom_map, eqToHom_trans,
              Category.assoc]
          constructor
          · intro _
            exact hgcomp_app
          · intro h
            erw [NatTrans.comp_app]
            simp only [eqToHom_map, eqToHom_trans, eqToHom_refl, Functor.map_id,
              Category.comp_id, Category.id_comp, Category.assoc]
            convert h using 1 <;>
              try rfl
            all_goals
              rename_i htype
              cases htype <;>
              exact eqRec_heq _ _
        let eS : Sf ⟶ Sg := eqToHom (congrArg
          (fun b => (TopCat.Sheaf.pushforward CommRingCat b).obj Z.𝒪) hbase)
        have htransport :
            qMap ≫ eqToHom hfpush.symm ≫
                (TopCat.Sheaf.pushforward CommRingCat p.base).map eS =
              qMap ≫ eqToHom hgpush.symm := by
          simp only [eS, eqToHom_map, eqToHom_trans]
        have hcompS : cp ≫
              (TopCat.Sheaf.pushforward CommRingCat p.base).map (cf ≫ eS) =
            cp ≫ (TopCat.Sheaf.pushforward CommRingCat p.base).map cg := by
          let F := TopCat.Sheaf.pushforward CommRingCat p.base
          calc
            cp ≫ F.map (cf ≫ eS) =
                (cp ≫ F.map cf) ≫ F.map eS := by
              rw [F.map_comp, Category.assoc]
            _ = (qMap ≫ eqToHom hfpush.symm) ≫ F.map eS := by rw [hfc]
            _ = qMap ≫ eqToHom hgpush.symm := htransport
            _ = cp ≫ F.map cg := hgc.symm
        let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base
        let P := structureSheafPullbackMap p
        have hP : adj.homEquiv X.𝒪 Y.𝒪 P = cp := by
          dsimp [P, structureSheafPullbackMap, cp, adj]
          exact (adj.homEquiv X.𝒪 Y.𝒪).apply_symm_apply _
        rw [Adjunction.homEquiv_unit] at hP
        have hAdj :
            adj.homEquiv X.𝒪 Sg (P ≫ (cf ≫ eS)) =
              adj.homEquiv X.𝒪 Sg (P ≫ cg) := by
          rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
          have hcompS' := hcompS
          rw [← hP] at hcompS'
          simpa only [Functor.map_comp, Category.assoc] using hcompS'
        have hsheaf : cf ≫ eS = cg := by
          apply (cancel_epi P).1
          exact (adj.homEquiv X.𝒪 Sg).injective hAdj
        have hcf' :
            (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map cf = f.left.c := by
          dsimp [cf]
          apply (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map_preimage
        have hcg' :
            (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map cg = g.left.c := by
          dsimp [cg]
          apply (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map_preimage
        have hsheaf_map := congrArg
          (fun k => (TopCat.Sheaf.forget CommRingCat Y.toTopCat).map k) hsheaf
        rw [Functor.map_comp, hcf', hcg'] at hsheaf_map
        apply NatTrans.ext
        funext U
        rw [NatTrans.comp_app]
        have hsheaf_app := congrArg (fun k => k.app U) hsheaf_map
        erw [NatTrans.comp_app] at hsheaf_app
        convert hsheaf_app using 1 <;>
          simp [eS, hbase, TopCat.Sheaf.forget, LocallyRingedSpace.𝒪,
          SheafedSpace.sheaf, LocallyRingedSpace.Hom.toShHom,
          InducedCategory.homMk, Functor.whiskerRight_app, NatTrans.comp_app,
          eqToHom_app, eqToHom_map, eqToHom_trans, Category.assoc]
      · exact hbase
  · intro f
    let fbase := f.left
    have hf : fbase ≫ p.base = q.base := CostructuredArrow.w f
    let S := (TopCat.Sheaf.pushforward CommRingCat fbase).obj Z.𝒪
    have hpush :
        (TopCat.Sheaf.pushforward CommRingCat p.base).obj S =
          (TopCat.Sheaf.pushforward CommRingCat q.base).obj Z.𝒪 := by
      rw [← hf]
      rfl
    let qMap : X.𝒪 ⟶
        (TopCat.Sheaf.pushforward CommRingCat q.base).obj Z.𝒪 :=
      (TopCat.Sheaf.forget CommRingCat X.toTopCat).preimage
        (LocallyRingedSpace.Hom.toShHom q).hom.c
    let cq : X.𝒪 ⟶
        (TopCat.Sheaf.pushforward CommRingCat p.base).obj S :=
      qMap ≫ eqToHom hpush.symm
    let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat p.base
    let P := structureSheafPullbackMap p
    let d := (adj.homEquiv X.𝒪 S).symm cq
    let d' := (asIso P).inv ≫ d
    let gSh : Z.toSheafedSpace ⟶ Y.toSheafedSpace :=
      InducedCategory.homMk
        { base := fbase
          c := d'.1 }
    have hgcomp : gSh.hom ≫ (LocallyRingedSpace.Hom.toShHom p).hom =
        (LocallyRingedSpace.Hom.toShHom q).hom := by
      let cp : X.𝒪 ⟶
          (TopCat.Sheaf.pushforward CommRingCat p.base).obj Y.𝒪 :=
        (TopCat.Sheaf.forget CommRingCat X.toTopCat).preimage
          (LocallyRingedSpace.Hom.toShHom p).hom.c
      have hP : adj.homEquiv X.𝒪 Y.𝒪 P = cp := by
        dsimp [P, structureSheafPullbackMap, cp, adj]
        exact (adj.homEquiv X.𝒪 Y.𝒪).apply_symm_apply _
      rw [Adjunction.homEquiv_unit] at hP
      have hd :
          adj.unit.app X.𝒪 ≫
              (TopCat.Sheaf.pushforward CommRingCat p.base).map d = cq := by
        have hd0 : adj.homEquiv X.𝒪 S d = cq := by
          dsimp [d]
          exact (adj.homEquiv X.𝒪 S).apply_symm_apply _
        rw [Adjunction.homEquiv_unit] at hd0
        exact hd0
      have hcomp :
          cp ≫ (TopCat.Sheaf.pushforward CommRingCat p.base).map d' = cq := by
        let F := TopCat.Sheaf.pushforward CommRingCat p.base
        calc
          cp ≫ F.map d' =
              (adj.unit.app X.𝒪 ≫ F.map P) ≫
                F.map ((asIso P).inv ≫ d) := by
            rw [hP]
          _ = (adj.unit.app X.𝒪 ≫ F.map P) ≫
                (F.map (asIso P).inv ≫ F.map d) := by
            simp only [d', Functor.map_comp]
          _ = adj.unit.app X.𝒪 ≫ F.map d := by
            have hPinv : P ≫ (asIso P).inv = 𝟙 _ := by
              change (asIso P).hom ≫ (asIso P).inv = _
              exact (asIso P).hom_inv_id
            calc
              _ = adj.unit.app X.𝒪 ≫
                    (F.map P ≫ F.map (asIso P).inv) ≫ F.map d := by
                simp only [Category.assoc]
              _ = adj.unit.app X.𝒪 ≫
                    F.map (P ≫ (asIso P).inv) ≫ F.map d := by
                rw [F.map_comp]
              _ = _ := by
                rw [hPinv, F.map_id]
                rw [← Category.assoc]
                change (adj.unit.app X.𝒪 ≫ 𝟙 _) ≫ F.map d = _
                rw [Category.comp_id]
          _ = cq := hd
      apply PresheafedSpace.Hom.ext
      · dsimp [gSh, InducedCategory.homMk]
        erw [PresheafedSpace.comp_c]
        have hcomp_map := congrArg
          (fun k => (TopCat.Sheaf.forget CommRingCat X.toTopCat).map k) hcomp
        rw [Functor.map_comp] at hcomp_map
        apply NatTrans.ext
        funext U
        have hcomp_app := congrArg (fun k => k.app U) hcomp_map
        erw [NatTrans.comp_app] at hcomp_app
        simpa [gSh, InducedCategory.homMk, LocallyRingedSpace.comp_c,
          PresheafedSpace.comp_c, TopCat.Sheaf.forget, LocallyRingedSpace.𝒪,
          SheafedSpace.sheaf, TopCat.Sheaf.pushforward_map,
          cp, cq, qMap, d', hpush, hf, Category.assoc,
          TopCat.Presheaf.pushforward_map_app',
          PresheafedSpace.comp_c_app, NatTrans.comp_app,
          Functor.whiskerRight_app, eqToHom_app, eqToHom_map, eqToHom_trans] using
          hcomp_app
      · change fbase ≫ p.base = q.base
        exact hf
    let g : Z ⟶ Y := LocallyRingedSpace.homMk gSh (by
      intro z
      have hz : p.base (fbase z) = q.base z := by
        exact congrArg (fun h : Z.toTopCat ⟶ X.toTopCat => h z) hf
      let e := eqToIso (congrArg (fun x : X => X.presheaf.stalk x) hz)
      let qz :=
        e.hom ≫ q.stalkMap z
      have hcomp :
          p.stalkMap (fbase z) ≫ gSh.hom.stalkMap z = qz := by
        have hstalk := PresheafedSpace.stalkMap.congr_hom
          (gSh.hom ≫ (LocallyRingedSpace.Hom.toShHom p).hom)
          (LocallyRingedSpace.Hom.toShHom q).hom hgcomp z
        simpa [qz, e, gSh, PresheafedSpace.stalkMap.comp,
          LocallyRingedSpace.Hom.toShHom, InducedCategory.homMk,
          LocallyRingedSpace.Hom.stalkMap] using hstalk
      let pIso := asIso (p.stalkMap (fbase z))
      have hsolve :
          gSh.hom.stalkMap z = pIso.inv ≫ qz := by
        apply (cancel_epi (p.stalkMap (fbase z))).1
        rw [hcomp]
        dsimp [pIso]
        simp
      rw [hsolve]
      dsimp [qz]
      letI : IsLocalHom pIso.symm.hom.hom := isLocalHom_of_iso pIso.symm
      letI : IsLocalHom e.hom.hom := isLocalHom_of_iso e
      change IsLocalHom (pIso.symm.hom ≫ (e.hom ≫ q.stalkMap z)).hom
      infer_instance)
    refine ⟨CostructuredArrow.homMk g ?_, ?_⟩
    · change g ≫ p = q
      apply LocallyRingedSpace.Hom.ext'
      simpa [g] using hgcomp
    · apply CostructuredArrow.hom_ext
      rfl

/-! ## The affine local-isomorphism functor -/

/-- Morphisms over `Spec A` between the affine topological spaces associated
to two `A`-algebras. -/
abbrev AffineTopOverHom
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φB : A →+* B) (φC : A →+* C) :=
  (CostructuredArrow.mk (Spec.map (CommRingCat.ofHom φC)).base :
      CostructuredArrow (𝟭 TopCat)
        (Spec (CommRingCat.of A)).toLocallyRingedSpace.toTopCat) ⟶
    CostructuredArrow.mk (Spec.map (CommRingCat.ofHom φB)).base

/-- The map on morphisms induced by the affine `Spec` construction. -/
def affineRingHomToTopOverHom
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φB : A →+* B) (φC : A →+* C) :
    {f : B →+* C // f.comp φB = φC} → AffineTopOverHom φB φC := fun f =>
  CostructuredArrow.homMk (Spec.map (CommRingCat.ofHom f.1)).base (by
    have hcomp :
        (CommRingCat.ofHom φB) ≫ CommRingCat.ofHom f.1 =
          CommRingCat.ofHom φC := by
      rw [← CommRingCat.ofHom_comp]
      exact congrArg CommRingCat.ofHom f.2
    have hspec := congrArg (fun h => h.base) (show
        Spec.map (CommRingCat.ofHom f.1) ≫
            Spec.map (CommRingCat.ofHom φB) =
          Spec.map (CommRingCat.ofHom φC) by
      rw [← Spec.map_comp, hcomp])
    change (Spec.map (CommRingCat.ofHom f.1)).base ≫
        (Spec.map (CommRingCat.ofHom φB)).base =
      (Spec.map (CommRingCat.ofHom φC)).base
    exact hspec)

/- The source's category of `A`-algebras is the full subcategory of the
   canonical under-category whose objects identify local rings. -/
def affineAlgebraProperty (A : Type u) [CommRing A] :
    ObjectProperty (Under (CommRingCat.of A)) :=
  fun B => IdentifiesLocalRings B.hom.hom

abbrev AffineAlgebrasWithIdentifiesLocalRings
    (A : Type u) [CommRing A] :=
  (affineAlgebraProperty A).FullSubcategory

abbrev AffineTopologicalSpacesOverSpec
    (A : Type u) [CommRing A] :=
  CostructuredArrow (𝟭 TopCat)
    (Spec (CommRingCat.of A)).toLocallyRingedSpace.toTopCat

/- The object part of the source's functor is the affine spectrum, regarded
   as a topological space over `Spec A`. -/
def affineSpecTopObject
    {A : Type u} [CommRing A]
    (B : AffineAlgebrasWithIdentifiesLocalRings A) :
    AffineTopologicalSpacesOverSpec A :=
  CostructuredArrow.mk (Spec.map B.obj.hom).base

/- The affine Spec construction on an algebra morphism, before packaging the
   resulting assignments as a functor. -/
def affineSpecTopMap
    {A : Type u} [CommRing A]
    {B C : AffineAlgebrasWithIdentifiesLocalRings A}
    (f : B ⟶ C) : affineSpecTopObject C ⟶ affineSpecTopObject B :=
  CostructuredArrow.homMk (Spec.map f.hom.right).base (by
    have hcomp : B.obj.hom ≫ f.hom.right = C.obj.hom := Under.w f.hom
    have hspec := congrArg (fun h => h.base) (show
        Spec.map f.hom.right ≫ Spec.map B.obj.hom = Spec.map C.obj.hom by
      rw [← Spec.map_comp, hcomp])
    change (Spec.map f.hom.right).base ≫ (Spec.map B.obj.hom).base =
      (Spec.map C.obj.hom).base
    exact hspec)

/- The actual functor named in the final statement of the source section. -/
def affineSpecTopFunctor (A : Type u) [CommRing A] :
    (AffineAlgebrasWithIdentifiesLocalRings A)ᵒᵖ ⥤
      AffineTopologicalSpacesOverSpec A where
  obj := fun B => affineSpecTopObject B.unop
  map := fun f => affineSpecTopMap f.unop
  map_id := by
    intro B
    apply CostructuredArrow.hom_ext
    change (Spec.map (𝟙 B.unop.obj.right)).base = _
    rfl
  map_comp := by
    intro B C D f g
    apply CostructuredArrow.hom_ext
    change (Spec.map (g.unop.hom.right ≫ f.unop.hom.right)).base = _
    rw [Spec.map_comp]
    rfl

theorem spec_fullyFaithful_of_identifiesLocalRings
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φB : A →+* B) (φC : A →+* C)
    (hB : IdentifiesLocalRings φB) (hC : IdentifiesLocalRings φC) :
    Function.Bijective (affineRingHomToTopOverHom φB φC) := by
  sorry

theorem affineSpecTopFunctor_fullyFaithful
    (A : Type u) [CommRing A] :
    Nonempty (affineSpecTopFunctor A).FullyFaithful := by
  sorry

end

end Formalization.Books.Proetale.Unit03
