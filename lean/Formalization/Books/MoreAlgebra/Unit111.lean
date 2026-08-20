import Formalization.Books.Algebra.Unit46.UniversalHomeomorphisms
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# More on Algebra, Chapter 111: Group actions and integral closure

This chapter records the group-action and invariant-ring interfaces in the
source. The finite-group invariant and stabilizer APIs are Mathlib's
canonical ones; the source's residue-field assertions use the earlier
universal-homeomorphism predicate.
-/

namespace Formalization.Books.MoreAlgebra.Unit111

open scoped Pointwise
open scoped TensorProduct

noncomputable section

universe u v w

/-! ## Fixed rings and equivariant maps -/

/-- The fixed subring of a commutative ring under a group action. -/
abbrev invariantRing (G R : Type*) [Group G] [CommRing R]
    [MulSemiringAction G R] := FixedPoints.subring R G

/-- A ring map carrying a group action equivariantly, as in the first lemma
of the source section. -/
structure EquivariantRingHom (G A B : Type*) [Group G]
    [CommRing A] [CommRing B] [MulSemiringAction G A]
    [MulSemiringAction G B] where
  hom : A →+* B
  surjective : Function.Surjective hom
  map_smul : ∀ (g : G) (a : A), hom (g • a) = g • hom a

/-- The map on fixed subrings induced by an equivariant ring map. -/
def invariantRingMap {G A B : Type*} [Group G]
    [CommRing A] [CommRing B] [MulSemiringAction G A]
    [MulSemiringAction G B] (f : EquivariantRingHom G A B) :
    invariantRing G A →+* invariantRing G B where
  toFun a :=
    ⟨f.hom a, fun g => by
      rw [← f.map_smul, a.2 g]⟩
  map_one' := Subtype.ext f.hom.map_one
  map_mul' _ _ := Subtype.ext (f.hom.map_mul _ _)
  map_zero' := Subtype.ext f.hom.map_zero
  map_add' _ _ := Subtype.ext (f.hom.map_add _ _)

/-! ## Stable ideals and quotient actions -/

/-- The ideal-theoretic stability hypothesis used to descend a group action
to a quotient. -/
def StableUnderGroupAction {G R : Type*} [Group G] [CommRing R]
    [MulSemiringAction G R] (I : Ideal R) : Prop :=
  ∀ (g : G), (g • I : Ideal R) ≤ I

/-- The action induced on a quotient by a group-stable ideal. -/
noncomputable def quotientAction {G R : Type*} [Group G] [CommRing R]
    [MulSemiringAction G R] (I : Ideal R)
    (hI : StableUnderGroupAction (G := G) (R := R) I) :
    MulSemiringAction G (R ⧸ I) := by
  let qsmul : G → (R ⧸ I →+* R ⧸ I) := fun g =>
    Ideal.Quotient.lift I
      ((Ideal.Quotient.mk I).comp (MulSemiringAction.toRingHom G R g))
      (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr
        ((hI g) (Ideal.smul_mem_pointwise_smul g x I hx)))
  exact
    { smul := fun g x => qsmul g x
      one_smul := by
        intro x
        refine Quotient.inductionOn' x ?_
        intro x
        change qsmul 1 (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I x
        rw [Ideal.Quotient.lift_mk]
        exact congrArg (Ideal.Quotient.mk I) (one_smul G x)
      mul_smul := by
        intro g h x
        refine Quotient.inductionOn' x ?_
        intro x
        change qsmul (g * h) (Ideal.Quotient.mk I x) =
          qsmul g (qsmul h (Ideal.Quotient.mk I x))
        rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
        exact congrArg (Ideal.Quotient.mk I) (mul_smul g h x)
      smul_zero := by
        intro g
        exact (qsmul g).map_zero
      smul_add := by
        intro g x y
        exact (qsmul g).map_add x y
      smul_one := by
        intro g
        exact (qsmul g).map_one
      smul_mul := by
        intro g x y
        exact (qsmul g).map_mul x y }

/-- The ideal of the fixed subring cut out by a stable ideal. -/
def invariantIdeal {G R : Type*} [Group G] [CommRing R]
    [MulSemiringAction G R] (I : Ideal R) : Ideal (invariantRing G R) :=
  I.comap (invariantRing G R).subtype

/-- The canonical map from the quotient of the fixed ring to the fixed ring
of the quotient. -/
noncomputable def invariantQuotientMap
    {G R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]
    (I : Ideal R) (hI : StableUnderGroupAction (G := G) (R := R) I) :
    letI := quotientAction I hI
    (invariantRing G R ⧸ invariantIdeal I) →+*
      invariantRing G (R ⧸ I) := by
  letI := quotientAction I hI
  let f : invariantRing G R →+* invariantRing G (R ⧸ I) :=
    { toFun := fun a =>
        ⟨Ideal.Quotient.mk I (a : R), by
          intro g
          change Ideal.Quotient.mk I (g • (a : R)) =
            Ideal.Quotient.mk I (a : R)
          exact congrArg (Ideal.Quotient.mk I) (a.2 g)⟩
      map_one' := Subtype.ext (Ideal.Quotient.mk I).map_one
      map_mul' _ _ := Subtype.ext ((Ideal.Quotient.mk I).map_mul _ _)
      map_zero' := Subtype.ext (Ideal.Quotient.mk I).map_zero
      map_add' _ _ := Subtype.ext ((Ideal.Quotient.mk I).map_add _ _) }
  exact Ideal.Quotient.lift (invariantIdeal I) f (by
    intro x hx
    apply Subtype.ext
    dsimp [f]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx)

/- The fixed subring is an invariant extension in Mathlib's canonical sense. -/
instance fixedRing.isInvariant {G R : Type*} [Group G] [CommRing R]
    [MulSemiringAction G R] :
    Algebra.IsInvariant (invariantRing G R) R G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

/-! ## The polynomial lemmas -/

/-- A fixed element of the target of a finite equivariant surjection lifts to
a monic polynomial over the fixed source whose image is its repeated linear
factor. -/
theorem polynomial_lifting_invariants
    {G A B : Type*} [Group G] [Fintype G]
    [CommRing A] [CommRing B] [MulSemiringAction G A]
    [MulSemiringAction G B] (f : EquivariantRingHom G A B)
    (b : invariantRing G B) :
    ∃ P : Polynomial (invariantRing G A),
      P.Monic ∧
        Polynomial.map (invariantRingMap f) P =
          (Polynomial.X - Polynomial.C b) ^ Fintype.card G := by
  sorry

/-- The coefficients below the leading coefficient of the orbit polynomial
of an element of JR lie in J. -/
theorem orbitPolynomial_coeff_mem_invariantIdeal
    {G R : Type*} [Group G] [Fintype G] [CommRing R]
    [MulSemiringAction G R] (J : Ideal (invariantRing G R))
    (x : R) (hx : x ∈ J.map (invariantRing G R).subtype) :
    let P : Polynomial R := ∏ g : G, (Polynomial.X - Polynomial.C (g • x))
    P.Monic ∧
      ∀ i : Fin (Fintype.card G),
        P.coeff (Fintype.card G - (i.1 + 1)) ∈
          J.map (invariantRing G R).subtype := by
  sorry

/-! ## Quotients of fixed rings -/

/-- The quotient map from the fixed ring to the fixed points of a stable
quotient, with its universal-homeomorphism consequences. -/
theorem invariants_modulo
    {G R : Type*} [Group G] [Fintype G] [CommRing R]
    [MulSemiringAction G R] (I : Ideal R)
    (hI : StableUnderGroupAction (G := G) (R := R) I) :
    letI := quotientAction I hI
    (invariantQuotientMap I hI).IsIntegral ∧
      IsHomeomorph (PrimeSpectrum.comap (invariantQuotientMap I hI)) ∧
        Formalization.Books.Algebra.Unit46.residueFieldExtensionsPurelyInseparable
          (invariantQuotientMap I hI) := by
  sorry

/-- The extended ideal of an ideal of the fixed ring is stable under the
ambient group action. -/
theorem invariantIdeal_map_stable
    {G R : Type*} [Group G] [CommRing R]
    [MulSemiringAction G R] (J : Ideal (invariantRing G R)) :
    StableUnderGroupAction (G := G) (R := R)
      (J.map (invariantRing G R).subtype) := by
  sorry

/-- The same map with the source ideal presented as an ideal of the fixed
subring, as in the strengthened quotient lemma. -/
noncomputable def fixedIdealQuotientMap
    {G R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]
    (J : Ideal (invariantRing G R)) :
    let I := J.map (invariantRing G R).subtype
    let hI := invariantIdeal_map_stable J
    letI := quotientAction I hI
    (invariantRing G R ⧸ J) →+* invariantRing G (R ⧸ I) := by
  let I := J.map (invariantRing G R).subtype
  let hI := invariantIdeal_map_stable J
  letI := quotientAction I hI
  let f : invariantRing G R →+* invariantRing G (R ⧸ I) :=
    { toFun := fun a =>
        ⟨Ideal.Quotient.mk I (a : R), by
          intro g
          change Ideal.Quotient.mk I (g • (a : R)) =
            Ideal.Quotient.mk I (a : R)
          exact congrArg (Ideal.Quotient.mk I) (a.2 g)⟩
      map_one' := Subtype.ext (Ideal.Quotient.mk I).map_one
      map_mul' _ _ := Subtype.ext ((Ideal.Quotient.mk I).map_mul _ _)
      map_zero' := Subtype.ext (Ideal.Quotient.mk I).map_zero
      map_add' _ _ := Subtype.ext ((Ideal.Quotient.mk I).map_add _ _) }
  exact Ideal.Quotient.lift J f (by
    intro x hx
    apply Subtype.ext
    dsimp [f]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem (invariantRing G R).subtype hx))

/-- The strengthened quotient statement, including the two polynomial
properties in the source. -/
theorem invariants_modulo_bis
    {G R : Type*} [Group G] [Fintype G] [CommRing R]
    [MulSemiringAction G R] (J : Ideal (invariantRing G R)) :
    let I := J.map (invariantRing G R).subtype
    let hI := invariantIdeal_map_stable J
    letI := quotientAction I hI
    (∀ b, ∃ P : Polynomial (invariantRing G R ⧸ J),
        P.Monic ∧ Polynomial.map (fixedIdealQuotientMap J) P =
          (Polynomial.X - Polynomial.C b) ^ Fintype.card G) ∧
      (∀ a, fixedIdealQuotientMap J a = 0 →
        (Polynomial.X - Polynomial.C a) ^ Fintype.card G =
          Polynomial.X ^ Fintype.card G) ∧
      (fixedIdealQuotientMap J).IsIntegral ∧
        IsHomeomorph (PrimeSpectrum.comap (fixedIdealQuotientMap J)) ∧
          Formalization.Books.Algebra.Unit46.residueFieldExtensionsPurelyInseparable
            (fixedIdealQuotientMap J) := by
  sorry

/-- If the order of the group is a unit, the quotient map on invariants is an
isomorphism. -/
theorem invariants_modulo_bis_isIso
    {G R : Type*} [Group G] [Fintype G] [CommRing R]
    [MulSemiringAction G R] (J : Ideal (invariantRing G R))
    (hcard : IsUnit (algebraMap ℕ R (Fintype.card G))) :
    let I := J.map (invariantRing G R).subtype
    let hI := invariantIdeal_map_stable J
    letI := quotientAction I hI
    Function.Bijective (fixedIdealQuotientMap J) := by
  sorry

/-! ## Tensoring over the fixed ring -/

/-- The tensor-product action which is trivial on the algebra factor and is
the given action on the ring factor. -/
noncomputable def tensorProductAction
    {G R A : Type*} [Group G] [CommRing R] [CommRing A]
    [MulSemiringAction G R] [Algebra (invariantRing G R) A] :
    MulSemiringAction G (A ⊗[(invariantRing G R)] R) := by
  let smulHom : G → (A ⊗[(invariantRing G R)] R →+*
      A ⊗[(invariantRing G R)] R) := fun g =>
    (Algebra.TensorProduct.map (AlgHom.id (invariantRing G R) A)
      (MulSemiringAction.toAlgHom (invariantRing G R) R g)).toRingHom
  have h_one : smulHom 1 = RingHom.id _ := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext a
      simp [smulHom]
    · ext r
      simp [smulHom]
  have h_mul (g h : G) :
      smulHom (g * h) = (smulHom g).comp (smulHom h) := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext a
      simp [smulHom]
    · ext r
      simp [smulHom, mul_smul]
  exact
    { smul := fun g x => smulHom g x
      one_smul := by
        intro x
        change smulHom 1 x = x
        rw [h_one]
        rfl
      mul_smul := by
        intro g h x
        change smulHom (g * h) x = smulHom g (smulHom h x)
        rw [h_mul]
        rfl
      smul_zero := by intro g; exact (smulHom g).map_zero
      smul_add := by intro g x y; exact (smulHom g).map_add x y
      smul_one := by intro g; exact (smulHom g).map_one
      smul_mul := by intro g x y; exact (smulHom g).map_mul x y }

/-- The fixed subring of the canonical tensor-product action. -/
noncomputable def invariantTensorRing
    {G R A : Type*} [Group G] [CommRing R] [CommRing A]
    [MulSemiringAction G R] [Algebra (invariantRing G R) A] :
    Subring (A ⊗[(invariantRing G R)] R) := by
  letI := tensorProductAction (G := G) (R := R) (A := A)
  exact FixedPoints.subring (A ⊗[(invariantRing G R)] R) G

/-- The invariant polynomial and kernel statements after tensoring with a
fixed-ring algebra. -/
theorem invariants_tensor
    {G R A : Type*} [Group G] [Fintype G] [CommRing R] [CommRing A]
    [MulSemiringAction G R] [Algebra (invariantRing G R) A] :
    ∃ f : A →+* invariantTensorRing (G := G) (R := R) (A := A),
      (∀ a, (f a : A ⊗[(invariantRing G R)] R) =
        algebraMap A (A ⊗[(invariantRing G R)] R) a) ∧
      (∀ b, ∃ P : Polynomial A, P.Monic ∧
        Polynomial.map f P =
          (Polynomial.X - Polynomial.C b) ^ Fintype.card G) ∧
      (∀ a, f a = 0 →
        (Polynomial.X - Polynomial.C a) ^ Fintype.card G =
          Polynomial.X ^ Fintype.card G) := by
  sorry

/-! ## Base change of invariants -/

/-- Base change from the fixed ring into an algebra has the expected
invariant subring, with the source's flat and universal-homeomorphism
conclusions. -/
theorem base_change_invariants
    {G R A : Type*} [Group G] [Finite G] [CommRing R] [CommRing A]
    [MulSemiringAction G R] [Algebra (invariantRing G R) A] :
    ∃ f : A →+* invariantTensorRing (G := G) (R := R) (A := A),
      (∀ a, (f a : A ⊗[(invariantRing G R)] R) =
        algebraMap A (A ⊗[(invariantRing G R)] R) a) ∧
      (Module.Flat (invariantRing G R) A → Function.Bijective f) ∧
      f.IsIntegral ∧
        IsHomeomorph (PrimeSpectrum.comap f) ∧
          Formalization.Books.Algebra.Unit46.residueFieldExtensionsPurelyInseparable f := by
  sorry

/-! ## Prime orbits and residue-field automorphisms -/

/-- Primes of a finite group action lying over the same prime of the fixed
subring form a single orbit. -/
theorem one_orbit
    {G R : Type*} [Group G] [Finite G] [CommRing R]
    [MulSemiringAction G R] (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.under (invariantRing G R) = Q.under (invariantRing G R)) :
    ∃ g : G, Q = g • P := by
  exact Algebra.IsInvariant.exists_smul_of_under_eq
    (invariantRing G R) R G P Q hPQ

/-- The stabilizer action on chosen fraction fields of the residue
quotients. These fraction fields are Mathlib's canonical model of the
residue fields at the two primes. -/
noncomputable def residueStabilizerHom
    {G A B K L : Type*} [Group G]
    [CommRing A] [CommRing B] [Algebra A B]
    [MulSemiringAction G B] [SMulCommClass G A B]
    (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]
    [Field K] [Field L]
    [Algebra (A ⧸ P) K] [Algebra (B ⧸ Q) L]
    [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
    [Algebra K L] [IsScalarTower (A ⧸ P) K L]
    [IsFractionRing (A ⧸ P) K] [IsFractionRing (B ⧸ Q) L] :
    MulAction.stabilizer G Q →* Gal(L/K) :=
  IsFractionRing.stabilizerHom G P Q K L

/-- Over a prime of the fixed ring, the residue-field extension is algebraic
and normal and the prime stabilizer surjects onto its automorphism group. -/
theorem one_orbit_geometric
    {G R K L : Type*} [Group G] [Finite G] [CommRing R]
    [MulSemiringAction G R] (P : Ideal (invariantRing G R))
    (Q : Ideal R) [P.IsPrime] [Q.IsPrime] [Q.LiesOver P]
    [Field K] [Field L]
    [Algebra ((invariantRing G R) ⧸ P) K] [Algebra (R ⧸ Q) L]
    [Algebra ((invariantRing G R) ⧸ P) L]
    [IsScalarTower ((invariantRing G R) ⧸ P) (R ⧸ Q) L]
    [Algebra K L] [IsScalarTower ((invariantRing G R) ⧸ P) K L]
    [IsFractionRing ((invariantRing G R) ⧸ P) K]
    [IsFractionRing (R ⧸ Q) L] :
    Algebra.IsAlgebraic K L ∧ Normal K L ∧
      Function.Surjective
        (residueStabilizerHom (G := G) (A := invariantRing G R) (B := R)
          (K := K) (L := L) P Q) := by
  sorry

theorem one_orbit_geometric_galois
    {A K L : Type*} [CommRing A] [Field K] [Field L]
    [IsDomain A] [IsIntegrallyClosed A]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [IsFractionRing A K] [IsGalois K L]
    (p : Ideal A) (q q' : Ideal (integralClosure A L))
    [p.IsPrime] [q.IsPrime] [q'.IsPrime]
    [q.LiesOver p] [q'.LiesOver p] :
    ∃ σ : Gal(L / K), q' = σ • q := by
  sorry

theorem one_orbit_geometric_galois_residue
    {A K L κp κq : Type*} [CommRing A] [Field K] [Field L]
    [IsDomain A] [IsIntegrallyClosed A]
    [Algebra A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [IsFractionRing A K] [IsGalois K L]
    (p : Ideal A) (q : Ideal (integralClosure A L))
    [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    [Field κp] [Field κq]
    [Algebra (A ⧸ p) κp]
    [Algebra ((integralClosure A L) ⧸ q) κq]
    [Algebra (A ⧸ p) κq]
    [IsScalarTower (A ⧸ p) ((integralClosure A L) ⧸ q) κq]
    [Algebra κp κq] [IsScalarTower (A ⧸ p) κp κq]
    [IsFractionRing (A ⧸ p) κp]
    [IsFractionRing ((integralClosure A L) ⧸ q) κq] :
    Algebra.IsAlgebraic κp κq ∧ Normal κp κq ∧
      Function.Surjective
        (residueStabilizerHom (G := Gal(L / K)) (A := A)
          (B := integralClosure A L) (K := κp) (L := κq) p q) := by
  sorry

theorem one_orbit_geometric_galois_compare
    {A K L M : Type*} [CommRing A] [Field K] [Field L] [Field M]
    [IsDomain A] [IsIntegrallyClosed A]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [Algebra (integralClosure A L) (integralClosure A M)]
    [IsScalarTower A K L] [IsScalarTower A K M]
    [IsScalarTower A L M] [IsScalarTower K L M]
    [IsScalarTower A (integralClosure A L) (integralClosure A M)]
    [IsFractionRing A K] [IsGalois K L] [IsGalois K M]
    [IsGalois L M]
    (res : Gal(M / K) →* Gal(L / K))
    (hres : ∀ (τ : Gal(M / K)) (x : L),
      algebraMap L M ((res τ) • x) = τ • algebraMap L M x)
    (hres_surjective : Function.Surjective res)
    (q : Ideal (integralClosure A L)) (r : Ideal (integralClosure A M))
    [q.IsPrime] [r.IsPrime]
    (hqr : q = r.comap (algebraMap (integralClosure A L)
      (integralClosure A M))) :
    Subgroup.map res (MulAction.stabilizer (Gal(M / K)) r) =
        MulAction.stabilizer (Gal(L / K)) q ∧
      Subgroup.map res (Ideal.inertia (Gal(M / K)) r) =
        Ideal.inertia (Gal(L / K)) q := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit111
