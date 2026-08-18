import Formalization.Books.Algebra.Unit40.SupportsAndAnnihilators
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
    rw [← hs0]
    exact IsNilpotent.zero
  let L := Localization M
  have hL : Nontrivial L := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    exact hzero ((IsLocalization.subsingleton_iff).mp hsub)
  letI : Nontrivial L := hL
  letI : Algebra R L :=
    ((algebraMap B L).comp (algebraMap R B)).toAlgebra
  letI : IsScalarTower R B L := IsScalarTower.of_algebraMap_eq' rfl
  let fS : S →ₐ[R] L :=
    (IsScalarTower.toAlgHom R B L).comp
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] B)
  let fK : K →ₐ[R] L :=
    (IsScalarTower.toAlgHom R B L).comp
      (Algebra.TensorProduct.includeRight : K →ₐ[R] B)
  let fSloc : Localization.AtPrime q.asIdeal →ₐ[R] L :=
    IsLocalization.liftAlgHom (f := fS) (fun y => by
      obtain ⟨s, hs⟩ := y
      change IsUnit (algebraMap B L
        ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B) s))
      exact IsLocalization.map_units L
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
  · apply (primeSpectrum_specializes_iff_ideal_inclusion _ q).2
    have hdisj : Disjoint (q.asIdeal.primeCompl : Set S)
        (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q.asIdeal)) q').asIdeal := by
      rw [← PrimeSpectrum.localization_comap_range
        (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl]
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
  constructor
  · ext p
    simp [tensorLocalizationBaseMap, tensorLocalizationMap,
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

theorem map_into_tensor_algebra_isOpenMap
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] :
    IsOpenMap (PrimeSpectrum.comap
      (tensorRightRingHom (k := k) (A := S) (R := R))) := by
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
  exact hcomp

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
      intro y hyI hyM
      obtain ⟨r, hr, rfl⟩ := (Submonoid.mem_map).mp hyM
      exact h ⟨⟨r, hr⟩, Ideal.mem_span_singleton.mp hyI⟩
    obtain ⟨Q, hQprime, hspan, hQdisj⟩ :=
      (Ideal.span ({x} : Set S)).exists_le_prime_disjoint M hdisj
    letI : Q.IsPrime := hQprime
    have hQunder : Q.under R ≤ p := by
      intro r hr
      by_contra hrp
      apply Set.disjoint_left.mp hQdisj hr
      exact ⟨r, hrp, rfl⟩
    rcases hcase with hgu | ⟨hgd, huniq⟩
    · obtain ⟨Q', hQQ', hQ'prime, hQ'over⟩ :=
        letI : Algebra.HasGoingUp R S := hgu
        Q.exists_ideal_ge_liesOver_of_le (p := Q.under R) (q := p) hQunder
      have hQ'eq : Q' = q := hunique Q' hQ'prime hQ'over
      apply hx
      rw [← hQ'eq]
      exact hQQ' (hspan (Ideal.mem_span_singleton_self x))
    · obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
        letI : Algebra.HasGoingDown R S := hgd
        q.exists_ideal_le_liesOver_of_le (p := Q.under R) (q := p) hQunder
      have hQeq : Q' = Q := huniq (Q.under R) (Ideal.IsPrime.under R Q)
        Q' Q hQ'prime hQprime hQ'over (by infer_instance)
      apply hx
      rw [← hQeq]
      exact hQ'Q (hspan (Ideal.mem_span_singleton_self x))
  letI : IsLocalization q.primeCompl (Localization M) :=
    IsLocalization.of_le_of_exists_dvd M q.primeCompl hM hdiv
  exact ⟨(IsLocalization.algEquiv q.primeCompl (Localization M)
    (Localization.AtPrime q)).toRingEquiv⟩

/-! ## Generalizations in the support of a finite flat module -/

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

end

end Formalization.Books.Algebra.Unit41
