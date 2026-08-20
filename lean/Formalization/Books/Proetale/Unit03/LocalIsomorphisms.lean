import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.TensorProduct.Basic

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
  sorry

theorem IsLocalIsomorphism.identifiesLocalRings
    {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : IsLocalIsomorphism φ) :
    IdentifiesLocalRings φ := by
  sorry

theorem IsLocalIsomorphism.isQuasiFinite
    {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : IsLocalIsomorphism φ) :
    RingHom.QuasiFinite φ := by
  sorry

/-! ## A finite standard-open presentation -/

theorem IsLocalIsomorphism.exists_finite_standardOpen_cover
    {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} (hφ : IsLocalIsomorphism φ) :
    ∃ (n : ℕ) (g : Fin n → B) (f : Fin n → A),
      Ideal.span (Set.range g) = ⊤ ∧
        ∀ i, ∃ e : Localization.Away (f i) ≃+* Localization.Away (g i),
          e.toRingHom.comp (algebraMap A (Localization.Away (f i))) =
            (algebraMap B (Localization.Away (g i))).comp φ := by
  sorry

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
  sorry

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
