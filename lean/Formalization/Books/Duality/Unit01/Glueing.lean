import Formalization.Books.Duality.Unit01.DualityTheory

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure situation_dualizing where
  base : Scheme.{u}
  baseDualizing : DerivedObject base
  baseNoetherian : IsNoetherianScheme base
  isDualizing : IsDualizingComplexOn baseDualizing

abbrev DualizingSituation := situation_dualizing

structure FiniteSchemeCover (X : Scheme.{u}) where
  cardinality : ℕ
  member : Fin cardinality → Scheme.{u}
  inclusion : ∀ i, member i ⟶ X
  openMember : ∀ i, IsOpenImmersionMorphism (inclusion i)
  separatedOverBase : Prop

structure NormalizedDualizingComplex (s : DualizingSituation)
    (X : Scheme.{u}) (cover : FiniteSchemeCover X) where
  complex : DerivedObject X
  localObject : ∀ i : Fin cover.cardinality, DerivedObject (cover.member i)
  localComparison : ∀ i : Fin cover.cardinality,
    Isomorphic ((LPullback (cover.inclusion i)).obj complex) (localObject i)
  transition : ∀ _i _j : Fin cover.cardinality, Prop
  cocycle : ∀ _i _j _k : Fin cover.cardinality, Prop

def GoodDualizing (s : DualizingSituation) (X : Scheme.{u})
    (cover : FiniteSchemeCover X) : Prop :=
  Nonempty (NormalizedDualizingComplex s X cover)

def item_cocycle_glueing (d : NormalizedDualizingComplex s X cover) : Prop :=
  ∀ i j k : Fin cover.cardinality, d.cocycle i j k

theorem lemma_good_dualizing_unique (s : DualizingSituation) (X : Scheme.{u})
    (cover : FiniteSchemeCover X) (h : GoodDualizing s X cover) :
    ∀ K K' : NormalizedDualizingComplex s X cover,
      Isomorphic K.complex K'.complex := by
  sorry

theorem lemma_good_dualizing_independence_covering (s : DualizingSituation)
    (X : Scheme.{u}) (cover cover' : FiniteSchemeCover X)
    (h : GoodDualizing s X cover) :
    GoodDualizing s X cover' ∧
      ∀ K K' : NormalizedDualizingComplex s X cover',
        Isomorphic K.complex K'.complex := by
  sorry

theorem lemma_existence_good_dualizing (s : DualizingSituation) (X : Scheme.{u})
    (cover : FiniteSchemeCover X) : GoodDualizing s X cover := by
  sorry

def definition_good_dualizing (s : DualizingSituation) (X : Scheme.{u})
    (cover : FiniteSchemeCover X) : Prop :=
  GoodDualizing s X cover

theorem lemma_good_over_both (s : DualizingSituation) (X : Scheme.{u})
    (cover : FiniteSchemeCover X) (h : GoodDualizing s X cover) :
    ∃ K : DerivedObject X, IsDualizingComplexOn K := by
  sorry

theorem lemma_open_immersion_good_dualizing_complex
    (s : DualizingSituation) (X : Scheme.{u}) (cover : FiniteSchemeCover X)
    (h : GoodDualizing s X cover) (i : Fin cover.cardinality) :
    ∀ d : NormalizedDualizingComplex s X cover,
      Isomorphic ((LPullback (cover.inclusion i)).obj d.complex)
        (d.localObject i) := by
  sorry

theorem lemma_proper_map_good_dualizing_complex
    (s : DualizingSituation) (X Y : Scheme.{u}) (f : X ⟶ Y)
    (a : RightAdjointData f) (h : IsDualizingComplexOn (StructureSheaf Y)) :
    ∃ K : DerivedObject X, IsDualizingComplexOn K := by
  sorry

theorem lemma_duality_bootstrap (s : DualizingSituation) (X : Scheme.{u})
    (cover : FiniteSchemeCover X) (h : GoodDualizing s X cover) :
    ∃ K : DerivedObject X, IsDualizingComplexOn K := by
  sorry

def remark_independent_omega_S (s : DualizingSituation) : Prop :=
  IsDualizingComplexOn s.baseDualizing

theorem example_trace_proper {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (K : DerivedObject Y) :
    ∃ t : (RPushforward f).obj (a.rightAdjoint.obj K) ⟶ K, t = Trace a K := by
  sorry

def remark_dualizing_finite {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_a : RightAdjointData f) : Prop :=
  Nonempty (RightAdjointData f)

def remark_relative_dualizing_complex_shriek {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f) : DerivedObject X :=
  RelativeDualizingComplex f a

end

end Formalization.Books.Duality.Unit01
