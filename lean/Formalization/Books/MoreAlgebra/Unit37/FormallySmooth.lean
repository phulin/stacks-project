import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.MoreAlgebra.Unit36.TopologicalRings
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.RingHom.Smooth

/-!
# More Algebra, Chapter 37: Formally smooth maps of topological rings

This file records the lifting definition and the formal-smoothness interfaces from the source
section.  The underlying ring-map predicate is kept separate from Mathlib's algebraic
`RingHom.FormallySmooth` predicate, while the adic and completion constructions use Mathlib's
canonical ideals, completions, and tensor products.
-/

namespace Formalization.Books.MoreAlgebra.Unit37

open scoped TensorProduct
open Formalization.Books.MoreAlgebra.Unit36

noncomputable section

universe u v

/-! ## The lifting definition -/

/-- Formal smoothness of a continuous map between linearly topologized topological rings.

The square-zero test object is given the discrete topology, and the quotient is given the
quotient topology induced by its canonical projection.  Thus the two continuity hypotheses in
the quantified diagram are exactly the two topological-ring-map conditions in the source. -/
def FormallySmooth
    {R S : Type u} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S]
    [IsLinearTopology R R] [IsLinearTopology S S]
    (f : R →+* S) : Prop :=
  Continuous f ∧
    ∀ {A : Type u} [CommRing A] (J : Ideal A) (_hJ : J ^ 2 = ⊥),
      letI : TopologicalSpace A := ⊥
      letI : TopologicalSpace (A ⧸ J) :=
        Formalization.Books.Topology.Unit29.quotientRingTopology (Ideal.Quotient.mk J)
      ∀ (g : R →+* A) (ψ : S →+* A ⧸ J),
        Continuous g →
          Continuous ψ →
            ψ.comp f = (Ideal.Quotient.mk J).comp g →
              ∃ lift : S →+* A,
                Continuous lift ∧
                  (Ideal.Quotient.mk J).comp lift = ψ ∧ lift.comp f = g

/-! ## Adic shorthand and the topology-independence lemma -/

/-- Formal smoothness for the `m`-adic topology on the source and the `n`-adic topology on the
target. -/
def FormallySmoothForIdeals
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Ideal R) (n : Ideal S) : Prop :=
  letI : TopologicalSpace R := IAdicRingTopology R m
  letI : NonarchimedeanRing R := m.nonarchimedean
  letI : IsLinearTopology R R := m.isLinearTopology
  letI : TopologicalSpace S := IAdicRingTopology S n
  letI : NonarchimedeanRing S := n.nonarchimedean
  letI : IsLinearTopology S S := n.isLinearTopology
  FormallySmooth f

/-- The source's shorthand: the topology on the source is discrete and only the target ideal is
recorded in the name of the property. -/
def FormallySmoothForIdeal
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (n : Ideal S) : Prop :=
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := discreteTopology_bot R
  letI : IsLinearTopology R R := by infer_instance
  letI : TopologicalSpace S := IAdicRingTopology S n
  letI : NonarchimedeanRing S := n.nonarchimedean
  letI : IsLinearTopology S S := n.isLinearTopology
  FormallySmooth f

/-- Algebraic formal smoothness implies topological formal smoothness for every compatible
linear/pre-adic choice of topologies. -/
theorem formallySmooth_of_ringHom_formallySmooth
    {R S : Type u} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S]
    [IsLinearTopology R R] [IsLinearTopology S S]
    (f : R →+* S) (hf : RingHom.FormallySmooth f)
    (hcont : Continuous f)
    (hS : IsPreAdmissibleTopologicalRing S) :
    FormallySmooth f := by
  sorry

/-- For adic topologies, changing the source topology to the discrete topology does not change
formal smoothness. -/
theorem formallySmooth_iff_discrete_source
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Ideal R) (n : Ideal S)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    FormallySmoothForIdeals f m n ↔ FormallySmoothForIdeal f n := by
  sorry

/-- The source's notation for formal smoothness in the `n`-adic topology. -/
theorem formallySmoothForIdeal_iff_formallySmoothForIdeals
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Ideal R) (n : Ideal S)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    FormallySmoothForIdeal f n ↔ FormallySmoothForIdeals f m n := by
  exact (formallySmooth_iff_discrete_source f m n hcont).symm

/-! ## Completions -/

/-- The extension of an ideal to its adic completion. -/
noncomputable def adicCompletionIdeal
    {R : Type u} [CommRing R] (I : Ideal R) : Ideal (AdicCompletion I R) :=
  I.map (algebraMap R (AdicCompletion I R))

/-- A completed ring map induced by a continuous map of finitely generated adic rings.

The existence theorem below is the completion universal property needed to choose the canonical
map.  The choice is exposed as a definition so later statements can use the completed map rather
than carrying an existential witness. -/
theorem exists_adicCompletionMap
    {R S : Type u} [CommRing R] [CommRing S]
    (m : Ideal R) (n : Ideal S) (f : R →+* S)
    (hm : m.FG) (hn : n.FG)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    ∃ fhat : AdicCompletion m R →+* AdicCompletion n S,
      fhat.comp (algebraMap R (AdicCompletion m R)) =
        (algebraMap S (AdicCompletion n S)).comp f := by
  sorry

noncomputable def adicCompletionMap
    {R S : Type u} [CommRing R] [CommRing S]
    (m : Ideal R) (n : Ideal S) (f : R →+* S)
    (hm : m.FG) (hn : n.FG)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    AdicCompletion m R →+* AdicCompletion n S :=
  Classical.choose (exists_adicCompletionMap m n f hm hn hcont)

theorem adicCompletionMap_comp_algebraMap
    {R S : Type u} [CommRing R] [CommRing S]
    (m : Ideal R) (n : Ideal S) (f : R →+* S)
    (hm : m.FG) (hn : n.FG)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    (adicCompletionMap m n f hm hn hcont).comp
        (algebraMap R (AdicCompletion m R)) =
      (algebraMap S (AdicCompletion n S)).comp f := by
  exact Classical.choose_spec (exists_adicCompletionMap m n f hm hn hcont)

/-- Formal smoothness is unchanged by passing to either adic completion.  The three entries are,
respectively, the original map, the map into the target completion, and the map between both
completions. -/
theorem formallySmooth_completion_tfae
    {R S : Type u} [CommRing R] [CommRing S]
    (m : Ideal R) (n : Ideal S) (f : R →+* S)
    (hm : m.FG) (hn : n.FG)
    (hcont : @Continuous R S (IAdicRingTopology R m) (IAdicRingTopology S n) f) :
    List.TFAE
      [ FormallySmoothForIdeal f n,
        FormallySmoothForIdeal
          ((algebraMap S (AdicCompletion n S)).comp f)
          (adicCompletionIdeal n),
        FormallySmoothForIdeal
          (adicCompletionMap m n f hm hn hcont)
          (adicCompletionIdeal n) ] := by
  sorry

/-! ## The stronger lifting property for adic targets -/

/-- The quotient used in the compatible two-index system in the proof of continuous lifting. -/
abbrev adicLiftingQuotient
    {A : Type u} [CommRing A] (J I : Ideal A) (n m : ℕ) : Type u :=
  A ⧸ (J ^ n ⊔ I ^ m)

/-- The canonical transition map between two quotients in the two-index system. -/
def adicLiftingQuotientMap
    {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    {K L : Ideal A} (h : K ≤ L) : (A ⧸ K) →ₐ[R] (A ⧸ L) :=
  Ideal.Quotient.factorₐ R h

/-- The transition that lowers the `J`-exponent in the two-index quotient system. -/
def adicLiftingQuotient_stepJ
    {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J I : Ideal A) (n m : ℕ) :
    adicLiftingQuotient J I (n + 1) (m + 1) →ₐ[R]
      adicLiftingQuotient J I n (m + 1) :=
  adicLiftingQuotientMap (R := R)
    (sup_le_sup (Ideal.pow_le_pow_right (Nat.le_succ n)) le_rfl)

/-- The transition that lowers the `I`-exponent in the two-index quotient system. -/
def adicLiftingQuotient_stepI
    {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J I : Ideal A) (n m : ℕ) :
    adicLiftingQuotient J I (n + 1) (m + 1) →ₐ[R]
      adicLiftingQuotient J I (n + 1) m :=
  adicLiftingQuotientMap (R := R)
    (sup_le_sup le_rfl (Ideal.pow_le_pow_right (Nat.le_succ m)))

/-- The `J`-transition in the lower-right square of the two-index system. -/
def adicLiftingQuotient_JTransition
    {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J I : Ideal A) (n m : ℕ) :
    adicLiftingQuotient J I (n + 1) m →ₐ[R] adicLiftingQuotient J I n m :=
  adicLiftingQuotientMap (R := R)
    (sup_le_sup (Ideal.pow_le_pow_right (Nat.le_succ n)) le_rfl)

/-- The `I`-transition in the lower-left square of the two-index system. -/
def adicLiftingQuotient_ITransition
    {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J I : Ideal A) (n m : ℕ) :
    adicLiftingQuotient J I n (m + 1) →ₐ[R] adicLiftingQuotient J I n m :=
  adicLiftingQuotientMap (R := R)
    (sup_le_sup le_rfl (Ideal.pow_le_pow_right (Nat.le_succ m)))

/-- The quotient-system assertion used in the proof of continuous lifting: each elementary square
has a surjective map to its fibre product with square-zero kernel. -/
theorem exists_adicLiftingQuotient_square_zero
    {R : Type v} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (J I : Ideal A) (n m : ℕ) :
    ∃ q : adicLiftingQuotient J I (n + 1) (m + 1) →ₐ[R]
        AlgHom.pullback
          (adicLiftingQuotient_ITransition (R := R) J I n m)
          (adicLiftingQuotient_JTransition (R := R) J I n m),
      Function.Surjective q ∧
        (RingHom.ker q.toRingHom) ^ 2 = ⊥ ∧
        (AlgHom.pullbackFst
            (adicLiftingQuotient_ITransition (R := R) J I n m)
            (adicLiftingQuotient_JTransition (R := R) J I n m)).comp q =
          adicLiftingQuotient_stepJ (R := R) J I n m ∧
        (AlgHom.pullbackSnd
            (adicLiftingQuotient_ITransition (R := R) J I n m)
            (adicLiftingQuotient_JTransition (R := R) J I n m)).comp q =
          adicLiftingQuotient_stepI (R := R) J I n m := by
  sorry

/-- A continuous lifting statement for an adic target and a closed quotient ideal. -/
theorem exists_continuous_lift
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    (f : R →+* S) (n : Ideal S) (hf : FormallySmoothForIdeal f n)
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsAdicTopologicalRing A)
    (J : Ideal A) (hJclosed : IsClosed (J : Set A))
    (hJpower : ∃ (I : Ideal A) (t : ℕ),
      IsIdealOfDefinition A I ∧ 1 ≤ t ∧ J ^ t ≤ I)
    (g : R →+* A)
    (hg : @Continuous R A (⊥ : TopologicalSpace R) inferInstance g)
    (ψ : S →+* A ⧸ J)
    (hψ : @Continuous S (A ⧸ J)
      (IAdicRingTopology S n)
      (Formalization.Books.Topology.Unit29.quotientRingTopology
        (Ideal.Quotient.mk J)) ψ)
    (hcomm : ψ.comp f = (Ideal.Quotient.mk J).comp g) :
    ∃ lift : S →+* A,
      @Continuous S A (IAdicRingTopology S n) inferInstance lift ∧
        (Ideal.Quotient.mk J).comp lift = ψ ∧ lift.comp f = g := by
  sorry

/-! ## Permanence properties -/

/-- Enlarging the target ideal preserves formal smoothness in the adic shorthand. -/
theorem formallySmoothForIdeal_of_le
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {n n' : Ideal S} (hnn' : n ≤ n') :
    FormallySmoothForIdeal f n → FormallySmoothForIdeal f n' := by
  sorry

/-- Composition of formally smooth continuous maps of linearly topologized rings is formally
smooth. -/
theorem formallySmooth_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace T]
    [IsTopologicalRing R] [IsTopologicalRing S] [IsTopologicalRing T]
    [IsLinearTopology R R] [IsLinearTopology S S] [IsLinearTopology T T]
    (f : R →+* S) (g : S →+* T)
    (hf : FormallySmooth f) (hg : FormallySmooth g) :
    FormallySmooth (g.comp f) := by
  sorry

/-- The target ideal after tensor-product base change. -/
noncomputable def baseChangeIdeal
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (n : Ideal S) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    Ideal (S ⊗[R] R') := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  exact n.map (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g)

/-- Formal smoothness in the target-ideal shorthand is preserved by arbitrary base change. -/
theorem formallySmooth_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (n : Ideal S)
    (hf : FormallySmoothForIdeal f n) :
    FormallySmoothForIdeal
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
      (baseChangeIdeal f g n) := by
  sorry

/-! ## Descent along a split base change -/

/-- The ring map `R → R'` is a module retraction: `R` is a direct summand of `R'` as an
`R`-module.  The complementary summand is only an `R`-module; it is not asserted to be an ideal
of `R'`. -/
def IsModuleRetract
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') : Prop :=
  letI : Algebra R R' := g.toAlgebra
  ∃ r : R' →ₗ[R] R,
    r.comp (Algebra.linearMap R R') = LinearMap.id

/-- Formal smoothness descends from a split tensor-product base change. -/
theorem formallySmooth_of_moduleRetract
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (n : Ideal S)
    (hRetract : IsModuleRetract g)
    (hf : FormallySmoothForIdeal
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)
      (baseChangeIdeal f g n)) :
    FormallySmoothForIdeal f n := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit37
