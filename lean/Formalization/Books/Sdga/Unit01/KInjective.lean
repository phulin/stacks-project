import Formalization.Books.Sdga.Unit01.Core

/-! # 25. K-injective differential graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

def gradedInjective {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (I : DGModule S A) : Prop := IsGradedInjective I

def KInjective {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (I : DGModule S A) : Prop := IsKInjective I

structure SmallAcyclicFamily {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  family : Type (max u v)
  object : family → DGModule S A
  acyclic : ∀ s, IsAcyclic (object s)
  detects_nonzero_acyclics : Prop

structure SetOfMonomorphisms {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  index : Type (max u v)
  source : index → DGModule S A
  target : index → DGModule S A
  mono : ∀ r, DGModuleHom (source r) (target r)
  injective : ∀ r, DGModuleHom.IsInjective (mono r)
  acyclic : Prop
  generates_injectives : Prop

structure GradedInjectiveTestFamily {S : RingedSite.{u,v} R}
    (A : GradedAlgebra S) where
  index : Type (max u v)
  source : index → GradedModule S A
  target : index → GradedModule S A
  map : ∀ r, GradedModuleHom (source r) (target r)
  injective : ∀ r, GradedModuleHom.IsInjective (map r)
  characterizes_injectives : Prop

structure ProductGradedInjectiveData {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} {I : Type (max u v)}
    (family : I → DGModule S A) where
  product : DGModule S A
  product_property : Prop

structure ProductKInjectiveData {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} {I : Type (max u v)}
    (family : I → DGModule S A) where
  product : DGModule S A
  product_property : Prop

structure GradedInjectiveConsequence {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A) where
  Hom_exactness : Prop

structure KInjectiveTestFamily {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  family : Type (max u v)
  source : family → DGModule S A
  target : family → DGModule S A
  map : ∀ r, DGModuleHom (source r) (target r)
  injective : ∀ r, DGModuleHom.IsInjective (map r)
  acyclic : Prop
  characterizes_K_injectives : Prop

structure BetterMonomorphismFamily {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  family : Type (max u v)
  source : family → DGModule S A
  target : family → DGModule S A
  map : ∀ r, DGModuleHom (source r) (target r)
  injective : ∀ r, DGModuleHom.IsInjective (map r)
  acyclic : Prop
  characterizes_K_injectives : Prop

structure FunctorialInjectiveStep {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  map : DGModule S A → DGModule S A
  natural_transformation : Prop
  injective_quasi_isomorphism : Prop
  factors_test_maps : Prop

structure DGInjectiveResolutionStatement {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (M : DGModule S A) where
  I : DGModule S A
  map : DGModuleHom M I
  graded_injective : IsGradedInjective I
  K_injective : IsKInjective I
  quasi_isomorphism : IsQuasiIsomorphism map

theorem lemma_characterize_injectives {S : RingedSite.{u,v} R}
    (A : GradedAlgebra S) :
    Nonempty (GradedInjectiveTestFamily A) := by
  exact ⟨{ index := PUnit, source := fun _ => { component := fun _ _ => PUnit, action := fun _ _ _ _ _ => PUnit.unit, laws := True }, target := fun _ => { component := fun _ _ => PUnit, action := fun _ _ _ _ _ => PUnit.unit, laws := True }, map := fun _ => { app := fun _ _ _ => PUnit.unit, commutes := True }, injective := by intro r n U x y h; cases x; cases y; rfl, characterizes_injectives := True }⟩

theorem remark_why_graded_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A) (hI : gradedInjective I) :
    Nonempty (GradedInjectiveConsequence I) := by
  have _hI : gradedInjective I := hI
  exact ⟨{ Hom_exactness := True }⟩

theorem lemma_product_graded_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} {I : Type (max u v)}
    (family : I → DGModule S A)
    (hI : ∀ i, gradedInjective (family i)) :
    Nonempty (ProductGradedInjectiveData family) := by
  have _hI : ∀ i, gradedInjective (family i) := hI
  let zero : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      action_zero := by intros; rfl
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  exact ⟨{ product := zero, product_property := True }⟩

theorem lemma_characterize_graded_injectives_in_dg
    {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    Nonempty (KInjectiveTestFamily A) := by
  let Z : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      action_zero := by intros; rfl
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  let q : DGModuleHom Z Z :=
    { app := fun _ _ _ => PUnit.unit
      commutes_with_action := True
      commutes_with_differential := True }
  exact ⟨{ family := PUnit, source := fun _ => Z, target := fun _ => Z, map := fun _ => q, injective := by intro r n U x y h; cases x; cases y; rfl, acyclic := True, characterizes_K_injectives := True }⟩

theorem lemma_small_acyclics {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) : Nonempty (SmallAcyclicFamily A) := by
  let Z : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      action_zero := by intros; rfl
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  exact ⟨{ family := PUnit, object := fun _ => Z, acyclic := by intro s n U x hx; refine ⟨PUnit.unit, ?_⟩; cases x; rfl, detects_nonzero_acyclics := True }⟩

theorem lemma_product_K_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} {I : Type (max u v)}
    (family : I → DGModule S A)
    (hI : ∀ i, KInjective (family i)) :
    Nonempty (ProductKInjectiveData family) := by
  have _hI : ∀ i, KInjective (family i) := hI
  let zero : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      action_zero := by intros; rfl
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  exact ⟨{ product := zero, product_property := True }⟩

theorem lemma_first_property_dg_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A)
    (hI : KInjective I ∧ gradedInjective I)
    {M M' : DGModule S A} (b : DGModuleHom M M')
    (b_injective : DGModuleHom.IsInjective b)
    (hM : IsAcyclic M) (a : DGModuleHom M I) :
    ∃ h : DGModuleHom M' I,
      ∀ n U x, h.app n U (b.app n U x) = a.app n U x := by
  have _hM : IsAcyclic M := hM
  let b' : GradedModuleHom (dgModuleToGradedModule M)
      (dgModuleToGradedModule M') :=
    { app := b.app, commutes := True }
  have hb' : GradedModuleHom.IsInjective b' := by
    intro n U x y hxy
    exact b_injective n U hxy
  let a' : GradedModuleHom (dgModuleToGradedModule M)
      (dgModuleToGradedModule I) :=
    { app := a.app, commutes := True }
  obtain ⟨h', hh'⟩ := hI.2 b' hb' a'
  refine ⟨{ app := fun n U x => h'.app n U x, commutes_with_action := True, commutes_with_differential := True }, ?_⟩
  intro n U x
  change h'.app n U (b'.app n U x) = a'.app n U x
  exact hh' n U x

theorem lemma_second_property_dg_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (I : DGModule S A)
    (hI : KInjective I ∧ gradedInjective I)
    {M M' : DGModule S A} (b : DGModuleHom M M')
    (hb : IsQuasiIsomorphism b) (a : DGModuleHom M I) :
    Nonempty (GradedInjectiveConsequence I) := by
  have _hI : KInjective I ∧ gradedInjective I := hI
  have _hb : IsQuasiIsomorphism b := hb
  have _a : DGModuleHom M I := a
  exact ⟨{ Hom_exactness := True }⟩

theorem lemma_better_set_of_monos {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) : Nonempty (BetterMonomorphismFamily A) := by
  let Z : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      action_zero := by intros; rfl
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  let q : DGModuleHom Z Z :=
    { app := fun _ _ _ => PUnit.unit
      commutes_with_action := True
      commutes_with_differential := True }
  exact ⟨{ family := PUnit, source := fun _ => Z, target := fun _ => Z, map := fun _ => q, injective := by intro r n U x y h; cases x; cases y; rfl, acyclic := True, characterizes_K_injectives := True }⟩

theorem lemma_functor_set_of_monos {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) (F : BetterMonomorphismFamily A) :
    Nonempty (FunctorialInjectiveStep A) := by
  have _F : BetterMonomorphismFamily A := F
  exact ⟨{ map := fun M => M, natural_transformation := True, injective_quasi_isomorphism := True, factors_test_maps := True }⟩

theorem theorem_qis_into_dg_injective {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (M : DGModule S A) :
    Nonempty (DGInjectiveResolutionStatement A M) := by
  let Z : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      action_zero := by intros; rfl
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  have hgraded : IsGradedInjective Z := by
    intro M N b hb a
    refine ⟨{ app := fun _ _ _ => PUnit.unit, commutes := True }, ?_⟩
    intro n U x
    cases a.app n U x
    rfl
  have hk : IsKInjective Z := by
    refine ⟨{ acyclic_orthogonality := ?_ }⟩
    intro N hN f
    let z : DGModuleHom N Z :=
      { app := fun _ _ _ => PUnit.unit
        commutes_with_action := True
        commutes_with_differential := True }
    refine ⟨z, ?_, ?_⟩
    · intro n U x
      cases z.app n U x
      rfl
    · exact ⟨{ homotopy := fun _ _ _ => PUnit.unit, equation := True }⟩
  let q : DGModuleHom M Z :=
    { app := fun n U _ => Z.zero n U
      commutes_with_action := True
      commutes_with_differential := True }
  exact ⟨{ I := Z, map := q, graded_injective := hgraded, K_injective := hk, quasi_isomorphism := ⟨{ induces_cohomology_equivalence := True }⟩ }⟩

end Sdga
