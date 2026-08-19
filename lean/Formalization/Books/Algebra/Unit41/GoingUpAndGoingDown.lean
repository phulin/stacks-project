import Formalization.Books.Algebra.Unit40.SupportsAndAnnihilators
import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.Algebra.Unit38.GoingDown
import Formalization.Books.Algebra.Unit29.ImagesOfFinitePresentation
import Formalization.Books.Topology.Unit19.Specialization
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Commutative Algebra, Chapter 41: Going up and going down

The source's going-up and going-down predicates are Mathlib's canonical
`Algebra.HasGoingUp` and `Algebra.HasGoingDown`.  The ring-map statements in
the source are expressed using the corresponding algebra structures, while
the spectrum maps use `PrimeSpectrum.comap`.
-/

namespace Formalization.Books.Algebra.Unit41

universe u v w

noncomputable section

open Set
open _root_.Topology
open scoped TensorProduct

/-! ## Specialization in the spectrum -/

/- The points corresponding to `p'` and `p` specialize exactly when the prime
   ideals are ordered by inclusion.  `PrimeSpectrum.le_iff_specializes` and
   `PrimeSpectrum.asIdeal_le_asIdeal` are the canonical APIs behind this. -/
theorem primeSpectrum_specializes_iff_ideal_inclusion
    {R : Type*} [CommRing R] (p p' : PrimeSpectrum R) :
    p' ⤳ p ↔ p'.asIdeal ≤ p.asIdeal := by
  rw [← PrimeSpectrum.le_iff_specializes, PrimeSpectrum.asIdeal_le_asIdeal]

/-! ## Going up and going down -/

/- Mathlib's classes are the source definitions, and these equivalences are
   the source's specialization/generalization formulation. -/
theorem hasGoingDown_iff_generalizingMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.HasGoingDown R S ↔
      GeneralizingMap (PrimeSpectrum.comap (algebraMap R S)) :=
  Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap

theorem hasGoingUp_iff_specializingMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.HasGoingUp R S ↔
      SpecializingMap (PrimeSpectrum.comap (algebraMap R S)) :=
  Algebra.HasGoingUp.iff_specializingMap_primeSpectrumComap

/- The six cases listed immediately after the definition. -/
theorem integral_hasGoingUp
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] :
    Algebra.HasGoingUp R S := by
  infer_instance

theorem finite_hasGoingUp
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] :
    Algebra.HasGoingUp R S := by
  infer_instance

theorem quotient_hasGoingUp
    {R : Type*} [CommRing R] (I : Ideal R) :
    Algebra.HasGoingUp R (R ⧸ I) := by
  infer_instance

theorem flat_hasGoingDown
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] :
    Algebra.HasGoingDown R S := by
  infer_instance

theorem localization_hasGoingDown
    {R : Type*} [CommRing R] (M : Submonoid R) :
    Algebra.HasGoingDown R (Localization M) := by
  infer_instance

/- The normal-domain integral-extension case is already recorded by
   `Formalization.Books.Algebra.Unit38.goingDown_normal_integral`, whose
   ideal-level conclusion is more general than a new wrapper here. -/

/-! ## Open maps and going down -/

theorem hasGoingDown_of_isOpenMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap R S))) :
    Algebra.HasGoingDown R S := by
  /- Prior attempt:
  rw [hasGoingDown_iff_generalizingMap]
  intro q p hpq
  let K := p.asIdeal.ResidueField
  let B := S ⊗[R] K
  letI : Algebra S B :=
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] B).toAlgebra
  let M : Submonoid B :=
    Submonoid.map
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] B).toMonoidHom
      q.asIdeal.primeCompl
  have hnil (s : S) (hs : s ∉ q.asIdeal) :
      ¬ IsNilpotent (algebraMap S B s) := by
    apply (PrimeSpectrum.mem_image_comap_basicOpen s p).mp
    apply (hopen _ (PrimeSpectrum.basicOpen s).isOpen).stableUnderGeneralization hpq
    exact ⟨q, (PrimeSpectrum.mem_basicOpen s q).2 hs, rfl⟩
  have hzero : (0 : B) ∉ M := by
    intro h0
    obtain ⟨s, hs, hs0⟩ := (Submonoid.mem_map).mp h0
    apply hnil s hs
    rw [hs0]
    exact IsNilpotent.zero
  let L := Localization M
  have hL : Nontrivial L := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    exact hzero ((IsLocalization.subsingleton_iff).mp hsub)
  letI : Nontrivial L := hL
  letI : Algebra R L :=
    ((algebraMap B L).comp (algebraMap R B)).toAlgebra
  letI : IsScalarTower R B L := by
    apply IsScalarTower.of_algebraMap_smul
    intro r x
    change algebraMap B L (algebraMap R B r) * x = algebraMap R L r * x
    congr 1
    rfl
  let fS : S →ₐ[R] L :=
    (IsScalarTower.toAlgHom R B L).comp
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] B)
  let fK : K →ₐ[R] L :=
    (IsScalarTower.toAlgHom R B L).comp
      (Algebra.TensorProduct.includeRight : K →ₐ[R] B)
  let fSloc : Localization.AtPrime q.asIdeal →ₐ[R] L :=
    IsLocalization.liftAlgHom (f := fS) (fun y => by
      obtain ⟨s, hs⟩ := y
      simpa [fS] using IsLocalization.map_units L
        ⟨_, Submonoid.mem_map_of_mem
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] B).toMonoidHom hs⟩)
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := K)
    (B := Localization.AtPrime q.asIdeal)
  let fFiber : K ⊗[R] Localization.AtPrime q.asIdeal →ₐ[R] L :=
    Algebra.TensorProduct.lift fK fSloc (fun _ _ => Commute.all _ _)
  obtain ⟨q', hq'⟩ :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mp
      (RingHom.domain_nontrivial fFiber.toRingHom)
  refine ⟨PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q.asIdeal)) q',
    ?_, ?_⟩
  · apply (primeSpectrum_specializes_iff_ideal_inclusion q
      (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q.asIdeal)) q')).2
    have hdisj : Disjoint (q.asIdeal.primeCompl : Set S)
        (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q.asIdeal)) q').asIdeal := by
      rw [← PrimeSpectrum.localization_comap_range
        (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl]
      exact ⟨q', rfl⟩
    exact disjoint_compl_left_iff.mp hdisj
  · rw [← PrimeSpectrum.comap_comp_apply]
    simpa [IsScalarTower.algebraMap_eq R S (Localization.AtPrime q.asIdeal)] using hq'
  -/
  rw [hasGoingDown_iff_generalizingMap]
  intro q p hpq
  let K := p.asIdeal.ResidueField
  let B := S ⊗[R] K
  let M : Submonoid B :=
    Submonoid.map
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] B).toMonoidHom
      q.asIdeal.primeCompl
  have hnil (s : S) (hs : s ∉ q.asIdeal) :
      ¬ IsNilpotent (algebraMap S B s) := by
    apply (PrimeSpectrum.mem_image_comap_basicOpen s p).mp
    apply (hopen _ (PrimeSpectrum.basicOpen s).isOpen).stableUnderGeneralization hpq
    exact ⟨q, (PrimeSpectrum.mem_basicOpen s q).2 hs, rfl⟩
  have hzero : (0 : B) ∉ M := by
    intro h0
    obtain ⟨s, hs, hs0⟩ := (Submonoid.mem_map).mp h0
    apply hnil s hs
    have hs0' : (Algebra.TensorProduct.includeLeft : S →ₐ[R] B) s = 0 := hs0
    exact hs0' ▸ IsNilpotent.zero
  let L := Localization M
  have hL : Nontrivial L := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    exact hzero ((IsLocalization.subsingleton_iff).mp hsub)
  letI : Nontrivial L := hL
  letI : Algebra R L :=
    ((algebraMap B L).comp (algebraMap R B)).toAlgebra
  letI : IsScalarTower R B L := by
    apply IsScalarTower.of_algebraMap_smul
    intro r x
    induction x using Localization.induction_on with
    | _ bs =>
        rcases bs with ⟨b, s⟩
        rw [Localization.smul_mk, Localization.smul_mk]
        simp [Algebra.smul_def]
  let fS : S →ₐ[R] L :=
    { toRingHom := (algebraMap B L).comp
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] B).toRingHom
      commutes' := by
        intro r
        calc
          algebraMap B L
              ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B)
              (algebraMap R S r)) = algebraMap B L (algebraMap R B r) := by
            rw [(Algebra.TensorProduct.includeLeft : S →ₐ[R] B).commutes]
          _ = algebraMap R L r := by
            change (algebraMap B L).comp (algebraMap R B) r = _
            rfl }
  let fK : K →ₐ[R] L :=
    { toRingHom := (algebraMap B L).comp
        (Algebra.TensorProduct.includeRight : K →ₐ[R] B).toRingHom
      commutes' := by
        intro r
        calc
          algebraMap B L
              ((Algebra.TensorProduct.includeRight : K →ₐ[R] B)
              (algebraMap R K r)) = algebraMap B L (algebraMap R B r) := by
            rw [(Algebra.TensorProduct.includeRight : K →ₐ[R] B).commutes]
          _ = algebraMap R L r := by
            change (algebraMap B L).comp (algebraMap R B) r = _
            rfl }
  let fSloc : Localization.AtPrime q.asIdeal →ₐ[R] L :=
    IsLocalization.liftAlgHom (f := fS) (fun y => by
      obtain ⟨s, hs⟩ := y
      change IsUnit (algebraMap B L
        ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B) s))
      exact IsLocalization.map_units (M := M) L
        ⟨_, Submonoid.mem_map_of_mem
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] B).toMonoidHom hs⟩)
  letI : SMul R L := (inferInstance : Algebra R L).toSMul
  letI : IsScalarTower R R L := by
    exact IsScalarTower.of_algebraMap_eq' rfl
  let fFiber : K ⊗[R] Localization.AtPrime q.asIdeal →ₐ[R] L :=
    Algebra.TensorProduct.lift fK fSloc (fun _ _ => Commute.all _ _)
  obtain ⟨q', hq'⟩ :=
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mp
      (RingHom.domain_nontrivial fFiber.toRingHom)
  refine ⟨PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q.asIdeal)) q',
    ?_, ?_⟩
  · apply (primeSpectrum_specializes_iff_ideal_inclusion q
      (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q.asIdeal)) q')).2
    have hdisj : Disjoint (q.asIdeal.primeCompl : Set S)
        (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q.asIdeal)) q').asIdeal := by
      change Disjoint (q.asIdeal.primeCompl : Set S)
        (PrimeSpectrum.comap (algebraMap S (Localization q.asIdeal.primeCompl)) q').asIdeal
      change PrimeSpectrum.comap (algebraMap S (Localization q.asIdeal.primeCompl)) q' ∈
        {p : PrimeSpectrum S |
          Disjoint (q.asIdeal.primeCompl : Set S) p.asIdeal}
      rw [← PrimeSpectrum.localization_comap_range
        (Localization q.asIdeal.primeCompl) q.asIdeal.primeCompl]
      exact ⟨q', rfl⟩
    exact disjoint_compl_left_iff.mp hdisj
  · rw [← PrimeSpectrum.comap_comp_apply]
    simpa [IsScalarTower.algebraMap_eq R S (Localization.AtPrime q.asIdeal)] using hq'

/-! ## Composition and images -/

theorem hasGoingDown_trans
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.HasGoingDown R S] [Algebra.HasGoingDown S T] :
    Algebra.HasGoingDown R T := by
  exact Algebra.HasGoingDown.trans R S T

theorem hasGoingUp_trans
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.HasGoingUp R S] [Algebra.HasGoingUp S T] :
    Algebra.HasGoingUp R T := by
  exact Algebra.HasGoingUp.trans R S T

theorem isClosed_range_comap_of_stableUnderSpecialization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (hT : StableUnderSpecialization
      (Set.range (PrimeSpectrum.comap (algebraMap R S)))) :
    IsClosed (Set.range (PrimeSpectrum.comap (algebraMap R S))) := by
  exact PrimeSpectrum.isClosed_range_of_stableUnderSpecialization (algebraMap R S) hT

theorem hasGoingUp_iff_isClosedMap_comap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.HasGoingUp R S ↔
      IsClosedMap (PrimeSpectrum.comap (algebraMap R S)) := by
  rw [hasGoingUp_iff_specializingMap]
  constructor
  · intro h Z hZ
    exact PrimeSpectrum.isClosed_image_of_stableUnderSpecialization _ _ hZ
      (h.stableUnderSpecialization_image hZ.stableUnderSpecialization)
  · intro h
    exact h.specializingMap

theorem isClosed_of_constructible_stableUnderSpecialization
    {R : Type*} [CommRing R] {E : Set (PrimeSpectrum R)}
    (hE : IsConstructible E) (hstable : StableUnderSpecialization E) :
    IsClosed E := by
  exact PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible
    hstable hE

theorem isOpen_of_constructible_stableUnderGeneralization
    {R : Type*} [CommRing R] {E : Set (PrimeSpectrum R)}
    (hE : IsConstructible E) (hstable : StableUnderGeneralization E) :
    IsOpen E := by
  exact PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible
    hstable hE

/- The general finite-presentation/going-down assertion is the canonical
   affine form of the source proposition; the flat case follows from the
   existing flat-going-down instance. -/
theorem finitePresentation_hasGoingDown_isOpenMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.HasGoingDown R S] [Algebra.FinitePresentation R S] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) := by
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

theorem flat_finitePresentation_isOpenMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [Algebra.FinitePresentation R S] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) := by
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

/-! ## Tensor products over a field -/

/- This is the right-factor ring map `R → S ⊗[k] R` used by the source's
   south arrows.  The right-algebra structure is deliberately not installed
   globally by Mathlib, so the explicit canonical ring hom is used. -/
noncomputable def tensorRightRingHom
    {k A R : Type*} [Field k] [CommRing A] [CommRing R]
    [Algebra k A] [Algebra k R] :
    R →+* A ⊗[k] R :=
  (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R).toRingHom

noncomputable def tensorLocalizationBaseMap
    {k A R : Type*} [Field k] [CommRing A] [CommRing R]
    [Algebra k A] [Algebra k R] (f : A ⊗[k] R) :
    R →+* Localization.Away f :=
  (algebraMap (A ⊗[k] R) (Localization.Away f)).comp
    (tensorRightRingHom (k := k) (A := A) (R := R))

noncomputable def tensorSubalgebraMap
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (S' : Subalgebra k S) :
    S' ⊗[k] R →+* S ⊗[k] R :=
  (Algebra.TensorProduct.map S'.val (AlgHom.id k R)).toRingHom

noncomputable def tensorLocalizationMap
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (S' : Subalgebra k S)
    (f : S' ⊗[k] R) :
    Localization.Away f →+* Localization.Away
      (tensorSubalgebraMap (k := k) (R := R) S' f) :=
  Localization.awayMap (tensorSubalgebraMap (k := k) (R := R) S') f

theorem same_image
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (S' : Subalgebra k S)
    (f : S' ⊗[k] R) :
    Set.range (PrimeSpectrum.comap
      (tensorLocalizationBaseMap (k := k) (A := S) (R := R)
        (tensorSubalgebraMap (k := k) (R := R) S' f))) =
      Set.range (PrimeSpectrum.comap
        (tensorLocalizationBaseMap (k := k) (A := S') (R := R) f)) ∧
    PrimeSpectrum.comap
        (tensorLocalizationBaseMap (k := k) (A := S) (R := R)
          (tensorSubalgebraMap (k := k) (R := R) S' f)) =
      (PrimeSpectrum.comap
          (tensorLocalizationBaseMap (k := k) (A := S') (R := R) f)) ∘
      (PrimeSpectrum.comap
          (tensorLocalizationMap (k := k) (R := R) S' f)) := by
  /- Prior attempt:
  constructor
  · ext p
    simp [tensorLocalizationBaseMap,
      tensorSubalgebraMap]
  · have hcomp :
      tensorLocalizationBaseMap (k := k) (A := S) (R := R)
          (tensorSubalgebraMap (k := k) (R := R) S' f) =
        (tensorLocalizationMap (k := k) (R := R) S' f).comp
          (tensorLocalizationBaseMap (k := k) (A := S') (R := R) f) := by
      ext x
      simp [tensorLocalizationBaseMap, tensorLocalizationMap,
        tensorSubalgebraMap]
    rw [hcomp, PrimeSpectrum.comap_comp]
  -/
  constructor
  · ext p
    simp [tensorLocalizationBaseMap, tensorSubalgebraMap]
  · have hcomp :
      tensorLocalizationBaseMap (k := k) (A := S) (R := R)
          (tensorSubalgebraMap (k := k) (R := R) S' f) =
        (tensorLocalizationMap (k := k) (R := R) S' f).comp
          (tensorLocalizationBaseMap (k := k) (A := S') (R := R) f) := by
      ext x
      simp [tensorLocalizationBaseMap, tensorLocalizationMap,
        tensorSubalgebraMap]
    rw [hcomp, PrimeSpectrum.comap_comp]

theorem map_into_tensor_algebra_isOpenMap
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] :
    IsOpenMap (PrimeSpectrum.comap
      (tensorRightRingHom (k := k) (A := S) (R := R))) := by
  sorry
/-
  let e : R ⊗[k] S ≃+* S ⊗[k] R :=
    (Algebra.TensorProduct.comm k R S).toRingEquiv
  have he : IsOpenMap (PrimeSpectrum.comap (e : R ⊗[k] S →+* S ⊗[k] R)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv e).symm.isOpenMap
  have hleft : IsOpenMap (PrimeSpectrum.comap
      (algebraMap R (R ⊗[k] S))) :=
    PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field
  have hcomp := hleft.comp he
  have hring : (e : R ⊗[k] S →+* S ⊗[k] R).comp
      (algebraMap R (R ⊗[k] S)) =
      tensorRightRingHom (k := k) (A := S) (R := R) := by
    ext r
    simp [e, tensorRightRingHom]
  rw [← hring, PrimeSpectrum.comap_comp]
  exact hcomp -/

/-! ## Localizing below a unique prime -/

/- The source writes an equality between two localization presentations.  In
   Lean the presentations have different carrier types, so the source-faithful
   usable interface is a ring equivalence. -/
noncomputable abbrev localizedAtBasePrime
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] : Type _ :=
  Localization (p.primeCompl.map (algebraMap R S))

theorem unique_prime_over_localize_below
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hunique : ∀ q' : Ideal S, q'.IsPrime → q'.LiesOver p → q' = q)
    (hcase : Algebra.HasGoingUp R S ∨
      (Algebra.HasGoingDown R S ∧
        ∀ p' : Ideal R, p'.IsPrime →
          ∀ q₁ q₂ : Ideal S, q₁.IsPrime → q₂.IsPrime →
            q₁.LiesOver p' → q₂.LiesOver p' → q₁ = q₂)) :
    Nonempty
      (localizedAtBasePrime (R := R) (S := S) p ≃+* Localization.AtPrime q) := by
  let M : Submonoid S := p.primeCompl.map (algebraMap R S)
  have hM : M ≤ q.primeCompl := by
    rintro x ⟨r, hr, rfl⟩
    rw [Ideal.mem_primeCompl_iff]
    exact fun hq => (Ideal.mem_primeCompl_iff.mp hr)
      ((Ideal.mem_of_liesOver q p r).mpr hq)
  have hdiv : ∀ x : S, x ∈ q.primeCompl → ∃ m : M, x ∣ (m : S) := by
    intro x hx
    by_contra h
    have hdisj : Disjoint (Ideal.span ({x} : Set S) : Set S) (M : Set S) := by
      rw [Set.disjoint_iff_forall_ne]
      intro y hyI z hyM hyz
      obtain ⟨r, hr, hrz⟩ :=
        (Submonoid.mem_map.mp (show z ∈ M from hyM))
      apply h
      let m : M := ⟨algebraMap R S r, ⟨r, hr, rfl⟩⟩
      refine ⟨m, ?_⟩
      change x ∣ algebraMap R S r
      rw [hrz, ← hyz]
      exact Ideal.mem_span_singleton.mp hyI
    obtain ⟨Q, hQprime, hspan, hQdisj⟩ :=
      (Ideal.span ({x} : Set S)).exists_le_prime_disjoint M hdisj
    have hQprime' : Q.IsPrime := hQprime
    have hQunder : Q.under R ≤ p := by
      intro r hr
      by_contra hrp
      apply Set.disjoint_left.mp hQdisj hr
      exact ⟨r, hrp, rfl⟩
    rcases hcase with hgu | ⟨hgd, huniq⟩
    · obtain ⟨Q', hQQ', hQ'prime, hQ'over⟩ :=
        @Ideal.exists_ideal_ge_liesOver_of_le R S _ _ _ hgu
          (Q.under R) p (by infer_instance) Q (by infer_instance)
          (by infer_instance) hQunder
      have hQ'eq : Q' = q := hunique Q' hQ'prime hQ'over
      apply hx
      rw [← hQ'eq]
      exact hQQ' (hspan (Ideal.mem_span_singleton_self x))
    · obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
        @Ideal.exists_ideal_le_liesOver_of_le R S _ _ _ hgd
          (Q.under R) p (by infer_instance) (by infer_instance) q
          (by infer_instance) (by infer_instance) hQunder
      have hQeq : Q' = Q := huniq (Q.under R) (Ideal.IsPrime.under R Q)
        Q' Q hQ'prime hQprime hQ'over (by infer_instance)
      apply hx
      apply hQ'Q
      rw [hQeq]
      exact hspan (Ideal.mem_span_singleton_self x)
  have hlocalization : IsLocalization q.primeCompl (Localization M) :=
    IsLocalization.of_le_of_exists_dvd M q.primeCompl hM (by
      intro x hx
      obtain ⟨m, hm⟩ := hdiv x hx
      exact ⟨m, m.property, hm⟩)
  exact ⟨(IsLocalization.algEquiv q.primeCompl (Localization M)
    (Localization.AtPrime q)).toRingEquiv⟩

/-! ## Generalizations in the support of a finite flat module -/

private lemma localizedModule_support_witness
    {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    (U : Submonoid R) (Q : Ideal (Localization U)) (z : LocalizedModule U N)
    (hz : (Submodule.span (Localization U) {z}).annihilator ≤ Q) :
    ∃ n : N, ∀ r ∉ Q.comap (algebraMap R (Localization U)), r • n ≠ 0 := by
  induction z using LocalizedModule.induction_on with
  | _ n s =>
      refine ⟨n, ?_⟩
      intro r hr hrn
      have hmzero : (algebraMap R (Localization U) r) •
          LocalizedModule.mk n s = 0 := by
        change (Localization.mk r (1 : U)) • LocalizedModule.mk n s = 0
        rw [LocalizedModule.mk_smul_mk, hrn]
        simp
      have hrQ : algebraMap R (Localization U) r ∈ Q := by
        apply hz
        rw [Submodule.mem_annihilator_span_singleton]
        exact hmzero
      exact hr (show r ∈ Q.comap (algebraMap R (Localization U)) from hrQ)

noncomputable def supportSpectrumMap
    {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] :
    {p : PrimeSpectrum S // p ∈ Module.support S N} → PrimeSpectrum R :=
  fun p => PrimeSpectrum.comap (algebraMap R S) p.1

theorem support_generalizingMap_of_finite_flat
    {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Flat R N] :
    GeneralizingMap (supportSpectrumMap (R := R) (S := S) (N := N)) := by
  sorry
/-
  intro x y hxy
  rcases x with ⟨q', hq'⟩
  let p' : Ideal R := q'.asIdeal.comap (algebraMap R S)
  have hp'prime : p'.IsPrime := by
    dsimp [p']
    infer_instance
  have hq'over : q'.asIdeal.LiesOver p' := ⟨rfl⟩
  let A := Localization.AtPrime p'
  let B := Localization.AtPrime q'.asIdeal
  let M := LocalizedModule q'.asIdeal.primeCompl N
  let hAlgebraAB : Algebra A B := Localization.AtPrime.algebraOfLiesOver p' q'.asIdeal
  let hModuleAM : Module A M := Module.compHom _ (algebraMap A B)
  let hTowerRAM : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun r x => by
    change algebraMap A B (algebraMap R A r) • x = r • x
    rw [← IsScalarTower.algebraMap_apply R A B]
    exact algebraMap_smul B r x
  let hTowerABM : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun a m => by
    change algebraMap A B a • m = a • m
    rfl
  have hflat : Formalization.Books.Algebra.Unit39.flat_at_prime_over
      (R := R) (A := S) (M := N) q'.asIdeal :=
    (Formalization.Books.Algebra.Unit39.flat_iff_localized_over_primes
      (R := R) (A := S) (M := N)).mp
      (inferInstance : Module.Flat R N) q'.asIdeal
  have hflatA : Module.Flat A M := by
    simpa [Formalization.Books.Algebra.Unit39.flat_at_prime_over, A, B, M] using hflat
  have hM : Nontrivial M := by
    change Nontrivial (LocalizedModule q'.asIdeal.primeCompl N)
    exact hq'
  have hM' : Nontrivial M := hM
  have hmaxA : IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ≠ ⊤ := by
    intro htop
    have hmaptop :
        Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) •
            (⊤ : Submodule B M) = ⊤ := by
      apply top_unique
      intro m hm
      have hmA : m ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) := by
        rw [htop]
        exact hm
      have hmR :
          m ∈ Submodule.restrictScalars A
            (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) •
              (⊤ : Submodule B M)) := by
        rw [Ideal.smul_restrictScalars]
        exact hmA
      exact hmR
    have hmaple :
        Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)
          ≤ IsLocalRing.maximalIdeal B := by
      rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
    have htopB :
        IsLocalRing.maximalIdeal B • (⊤ : Submodule B M) = ⊤ := by
      apply top_unique
      calc
        (⊤ : Submodule B M) =
            Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) •
              (⊤ : Submodule B M) := hmaptop.symm
        _ ≤ IsLocalRing.maximalIdeal B • (⊤ : Submodule B M) :=
          Submodule.smul_mono hmaple le_rfl
    have hquot : Subsingleton
        (M ⧸ IsLocalRing.maximalIdeal B • (⊤ : Submodule B M)) := by
      rw [Submodule.Quotient.subsingleton_iff]
      exact htopB
    have hquot' : Subsingleton
        (M ⧸ IsLocalRing.maximalIdeal B • (⊤ : Submodule B M)) := hquot
    have hfiberBsub : Subsingleton
        ((B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] M) :=
      (TensorProduct.quotTensorEquivQuotSMul M
        (IsLocalRing.maximalIdeal B)).toEquiv.subsingleton
    have hfiberB : Nontrivial
        ((B ⧸ IsLocalRing.maximalIdeal B) ⊗[B] M) := by
      change Nontrivial (IsLocalRing.ResidueField B ⊗[B] M)
      rw [← not_subsingleton_iff_nontrivial,
        IsLocalRing.subsingleton_tensorProduct,
        not_subsingleton_iff_nontrivial]
      exact hM
    exact not_subsingleton_iff_nontrivial.mpr hfiberB hfiberBsub
  have hffA : Module.FaithfullyFlat A M :=
    (Module.FaithfullyFlat.iff_flat_and_proper_ideal A M).2
      ⟨hflatA, by
        intro I hI htop
        apply hmaxA
        apply le_antisymm le_top
        calc
          (⊤ : Submodule A M) = I • ⊤ := htop.symm
          _ ≤ IsLocalRing.maximalIdeal A • ⊤ :=
            Submodule.smul_mono (IsLocalRing.le_maximalIdeal hI) le_rfl⟩
  have hpy : y.asIdeal ≤ p' := by
    have h := (primeSpectrum_specializes_iff_ideal_inclusion
      (PrimeSpectrum.comap (algebraMap R S) q') y).mp hxy
    simpa [p'] using h
  let K := y.asIdeal.ResidueField
  let fAK : A →ₐ[R] K :=
    IsLocalization.liftAlgHom (M := p'.primeCompl) (S := A)
      (f := (Algebra.ofId R K)) (fun z => by
      change IsUnit (algebraMap R K (z : R))
      rw [isUnit_iff_ne_zero, ne_eq, not_congr Ideal.algebraMap_residueField_eq_zero]
      intro hz
      exact (show (z : R) ∉ p' from Ideal.mem_primeCompl_iff.mp z.2) (hpy hz))
  let hAlgebraAK : Algebra A K := fAK.toRingHom.toAlgebra
  let hModuleAK : Module A K := Module.compHom _ fAK.toRingHom
  let hTowerRAK : IsScalarTower R A K :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      exact (fAK.commutes r).symm)
  have hKfiber' : Nontrivial (M ⊗[A] K) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right
      (R := A) (M := M) (N := K)).2 (by infer_instance)
  have hKfiber : Nontrivial (K ⊗[A] M) :=
    (TensorProduct.comm A M K).nontrivial_congr.mp hKfiber'
  /- Prior attempt: the preceding tensor-fiber construction left the required
     generalization witness as an unsolved existential. -/
  have hpure : ∃ k : K, ∃ m : M, k ⊗ₜ[A] m ≠ 0 := by
    by_contra h
    have hsub : Subsingleton (K ⊗[A] M) := by
      refine ⟨fun x y => ?_⟩
      have hz : ∀ z : K ⊗[A] M, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul k m =>
            have hk : k ⊗ₜ[A] m = 0 := by
              by_contra hkm
              exact h ⟨k, m, hkm⟩
            exact hk
        | add x y hx hy => rw [hx, hy, add_zero]
      exact (hz x).trans (hz y).symm
    exact (not_subsingleton_iff_nontrivial.mpr hKfiber) hsub
  obtain ⟨k, m, hkm⟩ := hpure
  let P : Ideal A := Ideal.comap (algebraMap A K) ⊥
  let J : Ideal B :=
    { carrier := {b | k ⊗ₜ[A] (b • m) = 0}
      zero_mem' := by simp
      add_mem' := by
        intro b c hb hc
        change k ⊗ₜ[A] ((b + c) • m) = 0
        rw [add_smul, TensorProduct.tmul_add, hb, hc, add_zero]
      smul_mem' := by
        intro b c hc
        change k ⊗ₜ[A] ((b * c) • m) = 0
        change k ⊗ₜ[A] (c • m) = 0 at hc
        let fb : M →ₗ[A] M :=
          { toFun := fun n => b • n
            map_add' := by intro n n'; exact smul_add b n n'
            map_smul' := by intro a n; exact smul_comm b a n }
        have hmap := congrArg
          (TensorProduct.map (LinearMap.id : K →ₗ[A] K) fb) hc
        rw [mul_smul]
        rw [TensorProduct.map_tmul, LinearMap.id_apply, map_zero] at hmap
        dsimp [fb] at hmap
        change k ⊗ₜ[A] (b • (c • m)) = 0 at hmap
        exact hmap }
  have hPmap : P.map (algebraMap A B) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change k ⊗ₜ[A] ((algebraMap A B a) • m) = 0
    rw [IsScalarTower.algebraMap_smul B a m, TensorProduct.tmul_smul]
    have ha' : fAK a = 0 := ha
    change fAK a • (k ⊗ₜ[A] m) = 0
    rw [ha', zero_smul]
  have hAnn : (Submodule.span B {m}).annihilator ≤ J := by
    intro b hb
    change k ⊗ₜ[A] (b • m) = 0
    rw [Submodule.mem_annihilator_span_singleton] at hb
    simpa [hb]
  have hI : P.map (algebraMap A B) + (Submodule.span B {m}).annihilator ≤ J :=
    add_le hPmap hAnn
  let T : Submonoid B :=
    Submonoid.map (algebraMap A B).toMonoidHom P.primeCompl
  have hdisj : Disjoint
      (P.map (algebraMap A B) + (Submodule.span B {m}).annihilator : Set B)
      (T : Set B) := by
    rw [Set.disjoint_left]
    intro z hzI hzT
    obtain ⟨a, ha, haz⟩ := (Submonoid.mem_map.mp hzT)
    have hzJ : z ∈ J := hI hzI
    have hz0 : k ⊗ₜ[A] (z • m) = 0 := hzJ
    rw [← haz] at hz0
    change k ⊗ₜ[A] ((algebraMap A B a) • m) = 0 at hz0
    rw [IsScalarTower.algebraMap_smul B a m, TensorProduct.tmul_smul] at hz0
    have hka : algebraMap A K a ≠ 0 := by
      intro hka
      exact ha hka
    have hz0' : algebraMap A K a • (k ⊗ₜ[A] m) = 0 := by
      simpa [fAK] using hz0
    exact hkm ((smul_eq_zero.mp hz0').resolve_left hka)
  obtain ⟨Q, hQprime, hIle, hQdisj⟩ :=
    (P.map (algebraMap A B) + (Submodule.span B {m}).annihilator).exists_le_prime_disjoint
      T hdisj
  let qB : PrimeSpectrum B := ⟨Q, hQprime⟩
  have hQunder : Q.comap (algebraMap A B) ≤ P := by
    intro a haQ
    by_contra haP
    apply Set.disjoint_left.mp hQdisj
    · exact haQ
    · exact ⟨a, haP, rfl⟩
  have hmapQ : P.map (algebraMap A B) ≤ Q :=
    le_trans (le_add_left le_rfl) hIle
  have hPunder : P ≤ Q.comap (algebraMap A B) := by
    rw [Ideal.le_comap_iff_map_le]
    exact hmapQ
  have hQeq : Q.comap (algebraMap A B) = P := le_antisymm hQunder hPunder
  have hqBsupport : qB ∈ Module.support B M := by
    rw [Module.mem_support_iff_exists_annihilator]
    exact ⟨m, le_trans le_add_right hIle⟩
  let qS : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S B) qB
  have hqSsupport : qS ∈ Module.support S N := by
    rw [Module.mem_support_iff']
    obtain ⟨n, hn⟩ := localizedModule_support_witness
      q'.asIdeal.primeCompl Q m (by simpa [B] using le_trans le_add_right hIle)
    refine ⟨n, ?_⟩
    intro r hr hrn
    apply hn r
    · intro hrQ
      apply hr
      exact hrQ
    · exact hrn
  have hqSle : qS.asIdeal ≤ q'.asIdeal := by
    have hdisj : Disjoint (q'.asIdeal.primeCompl : Set S) qS.asIdeal := by
      rw [← PrimeSpectrum.localization_comap_range B q'.asIdeal.primeCompl]
      exact ⟨qB, rfl⟩
    exact disjoint_compl_left_iff.mp hdisj
  have hspec : qS ⤳ q' :=
    (primeSpectrum_specializes_iff_ideal_inclusion q' qS).2 hqSle
  refine ⟨⟨qS, hqSsupport⟩, hspec, ?_⟩
  apply PrimeSpectrum.ext
  ext r
  change algebraMap R B r ∈ Q ↔ r ∈ y.asIdeal
  have hQmembership (a : A) : algebraMap A B a ∈ Q ↔ a ∈ P := by
    change a ∈ Q.comap (algebraMap A B) ↔ a ∈ P
    rw [hQeq]
  calc
    algebraMap R B r ∈ Q ↔ algebraMap A B (algebraMap R A r) ∈ Q := by
      rw [IsScalarTower.algebraMap_apply R A B]
    _ ↔ algebraMap R A r ∈ P := hQmembership _
    _ ↔ fAK (algebraMap R A r) = 0 := by rfl
    _ ↔ algebraMap R K r = 0 := by rw [fAK.commutes]
    _ ↔ r ∈ y.asIdeal := Ideal.algebraMap_residueField_eq_zero

-/

end Formalization.Books.Algebra.Unit41
