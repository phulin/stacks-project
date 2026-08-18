import Formalization.Books.Duality.Unit01.FundamentalClass

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def ExtensionByZero {U X : Scheme.{u}} (j : U ⟶ X)
    (K : DerivedObject U) : DerivedObject X :=
  (RPushforward j).obj K

structure ExtensionByZeroData {U X : Scheme.{u}} (j : U ⟶ X)
    (K : DerivedObject U) where
  extension : DerivedObject X
  comparison : Isomorphic extension (ExtensionByZero j K)

structure LiftMapData {U X : Scheme.{u}} (j : U ⟶ X)
    (K : DerivedObject U) (L : DerivedObject X) where
  map : ExtensionByZero j K ⟶ L
  compatibility : Prop

structure DerivedTriangleData {U : Scheme.{u}}
    (K L M : DerivedObject U) where
  toMiddle : K ⟶ L
  toRight : L ⟶ M
  toShift : M ⟶ Shift K 1
  distinguished : Prop

structure DeligneSystem {X : Scheme.{u}} where
  term : ℕ → DerivedObject X
  transition : ∀ n, term (n + 1) ⟶ term n

structure DeligneSystemMorphism {X : Scheme.{u}}
    (A B : DeligneSystem (X := X)) where
  map : ∀ n, A.term n ⟶ B.term n
  compatible : ∀ n, Prop
  quasiIsomorphism : Prop

structure OpenDeligneSystem {U X : Scheme.{u}} (j : U ⟶ X)
    (K : DerivedObject U) where
  system : DeligneSystem (X := X)
  restriction : ∀ n,
    Isomorphic ((LPullback j).obj (system.term n)) K

structure ExtensionByZeroTriangleData {U X : Scheme.{u}}
    (j : U ⟶ X) {K L M : DerivedObject U}
    (t : DerivedTriangleData K L M) where
  Ksystem : OpenDeligneSystem j K
  Lsystem : OpenDeligneSystem j L
  Msystem : OpenDeligneSystem j M
  triangle : ∀ _n : ℕ, Prop

theorem lemma_lift_map {U X : Scheme.{u}} (j : U ⟶ X) (K : DerivedObject U)
    (L : DerivedObject X) (h : Prop) :
    Nonempty (LiftMapData j K L) := by
  sorry

theorem lemma_lift_map_plus {U X : Scheme.{u}} (j : U ⟶ X) (K : DerivedObject U)
    (L : DerivedObject X) (h : Prop) :
    Nonempty (LiftMapData j K L) := by
  sorry

theorem lemma_extension_by_zero {U X : Scheme.{u}} (j : U ⟶ X)
    (K : DerivedObject U) : Nonempty (ExtensionByZeroData j K) := by
  exact ⟨⟨ExtensionByZero j K, ⟨Iso.refl _⟩⟩⟩

theorem lemma_extension_by_zero_triangle {U X : Scheme.{u}} (j : U ⟶ X)
    {K L M : DerivedObject U} (t : DerivedTriangleData K L M) :
    Nonempty (ExtensionByZeroTriangleData j t) := by
  sorry

def remark_extension_by_zero {U X : Scheme.{u}} (j : U ⟶ X)
    (K : DerivedObject U) : Prop :=
  Nonempty (ExtensionByZeroData j K)

def remark_extension_by_zero_linear_pro_system {U X : Scheme.{u}}
    (j : U ⟶ X) : Prop := IsOpenImmersionMorphism j

theorem lemma_deligne_system_2_out_of_3 {X : Scheme.{u}}
    (A B C : DeligneSystem (X := X))
    (hAB : Nonempty (DeligneSystemMorphism A B))
    (hBC : Nonempty (DeligneSystemMorphism B C)) :
    Nonempty (DeligneSystemMorphism A C) := by
  sorry

def lemma_consequence_Artin_Rees_bis {X : Scheme.{u}}
    (_A : DeligneSystem (X := X)) (h : Prop) : Prop :=
  ∃ c : ℕ, 0 < c ∧ h

def lemma_characterize_extension_by_zero_algebra {U X : Scheme.{u}}
    (j : U ⟶ X) (K : DerivedObject U) : Prop :=
  IsOpenImmersionMorphism j ∧ Nonempty (ExtensionByZeroData j K)

def lemma_characterize_extension_by_zero {U X : Scheme.{u}}
    (j : U ⟶ X) (K : DerivedObject U) : Prop :=
  IsOpenImmersionMorphism j ∧ Nonempty (ExtensionByZeroData j K)

theorem lemma_tensoring_Deligne_system {X : Scheme.{u}}
    (_A : DeligneSystem (X := X)) (K : DerivedObject X) :
    Nonempty (DeligneSystem (X := X)) := by
  sorry

end

end Formalization.Books.Duality.Unit01
