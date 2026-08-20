import Formalization.Books.Algebra.Unit132.DeRhamComplex.Complex

namespace Formalization.Books.Algebra.Unit132

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section
/-! ## Functoriality -/

/-- The degree-zero ring map in the de Rham map associated to a square of
  algebra maps. -/
def deRhamDegreeZeroRingMap
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] :
    B →+* B' :=
  algebraMap B B'

def deRhamDegreeZeroMap
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] :
    B →+ B' :=
  (deRhamDegreeZeroRingMap (A := A) (A' := A') (B := B) (B' := B')).toAddMonoidHom

/-- The degree-one map in the same square, using the canonical Kähler API. -/
noncomputable def deRhamDegreeOneMap
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] :
    ModuleOfDifferentials A B →ₗ[A] ModuleOfDifferentials A' B' :=
  mapOfDifferentials (R := A) (T := A') (A := B) (B := B')

theorem deRhamDegreeOneMap_on_universal_differential
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
    (b : B) :
    deRhamDegreeOneMap (A := A) (A' := A') (B := B) (B' := B')
        (universalDifferentialLinearMap A B b) =
      universalDifferentialLinearMap A' B' (algebraMap B B' b) := by
  exact mapOfDifferentials_apply_universalDifferential
    (R := A) (T := A') (A := B) (B := B') b

/-- The degreewise `A`-linear maps and their compatibility with the de Rham
differentials.  The component formula records the induced exterior-power map
in all degrees. -/
structure DeRhamMapData
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] where
  component : ∀ p : ℕ, deRhamTerm A B p →ₗ[A] deRhamTerm A' B' p
  component_on_generator :
    ∀ (p : ℕ) (b₀ : B) (b : Fin p → B),
      component p (deRhamGenerator p b₀ b) =
        deRhamGenerator p (algebraMap B B' b₀)
          (fun i => algebraMap B B' (b i))
  commutes :
    ∀ (p : ℕ) (ω : deRhamTerm A B p),
      component (p + 1) (deRhamDifferential (A := A) (B := B) p ω) =
        deRhamDifferential (A := A') (B := B') p (component p ω)

theorem deRhamMapData_exists
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] :
    Nonempty (DeRhamMapData (A := A) (A' := A') (B := B) (B' := B')) := by
  classical
  let targetModule : Module B (ModuleOfDifferentials A' B') := inferInstance
  let : Module B (ModuleOfDifferentials A' B') := targetModule
  let : IsScalarTower B B' (ModuleOfDifferentials A' B') :=
    KaehlerDifferential.isScalarTower_of_tower
      (R := A') (S := B') (R₁ := B) (R₂ := B')
  let f : ModuleOfDifferentials A B →ₗ[B] ModuleOfDifferentials A' B' :=
    IsLinearMap.mk' (mapOfDifferentials (R := A) (T := A') (A := B) (B := B'))
      ⟨(by
        intro x y
        exact map_add _ _ _), (by
        intro c x
        have hx : x ∈ Submodule.span B (Set.range (universalDifferential A B)) := by
          change x ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B))
          rw [KaehlerDifferential.span_range_derivation]
          exact Submodule.mem_top
        have h : ∀ x, x ∈ Submodule.span B (Set.range (universalDifferential A B)) → ∀ c : B,
            mapOfDifferentials (R := A) (T := A') (A := B) (B := B') (c • x) =
              c • mapOfDifferentials (R := A) (T := A') (A := B) (B := B') x := by
          intro x hx
          refine Submodule.span_induction (p := fun x _ => ∀ c : B,
              mapOfDifferentials (R := A) (T := A') (A := B) (B := B') (c • x) =
                c • mapOfDifferentials (R := A) (T := A') (A := B) (B := B') x)
            ?_ ?_ ?_ ?_ hx
          · rintro _ ⟨b, rfl⟩ c
            rw [mapOfDifferentials_smul_universalDifferential,
              mapOfDifferentials_apply_universalDifferential]
            exact IsScalarTower.algebraMap_smul (R := B) (A := B') c
              (universalDifferential A' B' (algebraMap B B' b))
          · intro c; simp
          · intro x y hx hy ihx ihy c
            simp only [map_add, smul_add]
            rw [ihx c, ihy c]
          · intro a x hx ih c
            rw [← mul_smul, ih (c * a), ih a, smul_smul]
        exact h x hx c)⟩
  have hf (x : ModuleOfDifferentials A B) :
      f x = mapOfDifferentials (R := A) (T := A') (A := B) (B := B') x := by
    rfl
  let componentData : ∀ p : ℕ,
      { C : deRhamTerm A B p →ₗ[A] deRhamTerm A' B' p //
        ∀ (b₀ : B) (b : Fin p → B),
          C (deRhamGenerator p b₀ b) =
            deRhamGenerator p (algebraMap B B' b₀)
              (fun i => algebraMap B B' (b i)) } :=
    fun p => by
      letI : Module B (deRhamTerm A' B' p) :=
        Module.compHom (deRhamTerm A' B' p) (algebraMap B B')
      letI : IsScalarTower B B' (deRhamTerm A' B' p) :=
        IsScalarTower.of_compHom (R := B) (A := B')
          (M := deRhamTerm A' B' p)
      letI : Module A (deRhamTerm A' B' p) :=
        Module.compHom (deRhamTerm A' B' p) (algebraMap A B')
      letI : IsScalarTower A B' (deRhamTerm A' B' p) :=
        IsScalarTower.of_compHom (R := A) (A := B')
          (M := deRhamTerm A' B' p)
      let wedge : (ModuleOfDifferentials A' B') [⋀^Fin p]→ₗ[B]
          deRhamTerm A' B' p :=
        { toFun := exteriorPower.ιMulti B' p
          map_update_add' := by
            intro _ m i x y
            exact (exteriorPower.ιMulti B' p).toMultilinearMap.map_update_add m i x y
          map_update_smul' := by
            intro _ m i c x
            calc
              exteriorPower.ιMulti B' p (Function.update m i (c • x)) =
                  exteriorPower.ιMulti B' p
                    (Function.update m i ((algebraMap B B' c) • x)) := by
                congr 1
                funext j
                by_cases h : j = i <;> simp [h]
              _ = (algebraMap B B' c) •
                    exteriorPower.ιMulti B' p (Function.update m i x) := by
                exact (exteriorPower.ιMulti B' p).toMultilinearMap.map_update_smul
                  m i (algebraMap B B' c) x
              _ = c • exteriorPower.ιMulti B' p (Function.update m i x) := by
                rw [IsScalarTower.algebraMap_smul]
          map_eq_zero_of_eq' := by
            intro v i j h hij
            exact (exteriorPower.ιMulti B' p).map_eq_zero_of_eq v h hij }
      let C : deRhamTerm A B p →ₗ[B] deRhamTerm A' B' p :=
        exteriorPower.alternatingMapLinearEquiv
          (wedge.compLinearMap f)
      let C_A : deRhamTerm A B p →ₗ[A] deRhamTerm A' B' p :=
        { toFun := C
          map_add' := C.map_add
          map_smul' := by
            intro a x
            have hx : a • x = (algebraMap A B a) • x :=
              (IsScalarTower.algebraMap_smul B a x).symm
            calc
              C (a • x) = C ((algebraMap A B a) • x) := by
                simp only [hx]
              _ = (algebraMap A B a) • C x := C.map_smul _ _
              _ = ((algebraMap B B').comp (algebraMap A B)) a • C x :=
                (IsScalarTower.algebraMap_smul (R := B) (A := B')
                  (algebraMap A B a) (C x)).symm
              _ = (algebraMap A B' a) • C x := by
                rw [IsScalarTower.algebraMap_eq A B B']
              _ = a • C x :=
                IsScalarTower.algebraMap_smul (R := A) (A := B') a (C x) }
      refine ⟨C_A, ?_⟩
      intro b₀ b
      change C (b₀ • exteriorPower.ιMulti B p
        (fun i => universalDifferentialLinearMap A B (b i))) = _
      rw [LinearMap.map_smul C]
      dsimp [C]
      rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      simp only [AlternatingMap.compLinearMap_apply]
      have h : (fun i => f (universalDifferentialLinearMap A B (b i))) =
          (fun i => universalDifferentialLinearMap A' B' ((algebraMap B B') (b i))) := by
        funext i
        calc
          f (universalDifferentialLinearMap A B (b i)) =
              mapOfDifferentials (R := A) (T := A') (A := B) (B := B')
                (universalDifferentialLinearMap A B (b i)) := hf _
          _ = universalDifferentialLinearMap A' B' ((algebraMap B B') (b i)) :=
            deRhamDegreeOneMap_on_universal_differential
              (A := A) (A' := A') (B := B) (B' := B') (b i)
      rw [h]
      change b₀ • exteriorPower.ιMulti B' p
          (fun i => universalDifferentialLinearMap A' B'
            ((algebraMap B B') (b i))) =
        b₀ • exteriorPower.ιMulti B' p
          (fun i => universalDifferentialLinearMap A' B'
            ((algebraMap B B') (b i)))
      rfl
  let component : ∀ p : ℕ, deRhamTerm A B p →ₗ[A] deRhamTerm A' B' p :=
    fun p => (componentData p).1
  refine ⟨⟨component, ?_, ?_⟩⟩
  · intro p b₀ b
    exact (componentData p).2 b₀ b
  · intro p ω
    cases p with
    | zero =>
        have hω : ω ∈ Submodule.span A (deRhamGenerators (A := A) (B := B) 0) := by
          rw [deRhamGenerators_span (A := A) (B := B) 0]
          exact Submodule.mem_top
        refine Submodule.span_induction (p := fun x _ =>
            component 1 (deRhamDifferential (A := A) (B := B) 0 x) =
              deRhamDifferential (A := A') (B := B') 0 (component 0 x))
          ?_ ?_ ?_ ?_ hω
        · rintro _ ⟨z, rfl⟩
          rcases z with ⟨b₀, b⟩
          have hzero : deRhamDegreeZeroEquivA A B b₀ =
              deRhamGenerator 0 b₀ b := by
            apply (exteriorPower.zeroEquiv B (ModuleOfDifferentials A B)).injective
            simp [deRhamDegreeZeroEquivA, deRhamDegreeZeroEquiv,
              deRhamGenerator, exteriorPower.zeroEquiv]
          have hzero' : deRhamDegreeZeroEquivA A' B' (algebraMap B B' b₀) =
              deRhamGenerator 0 (algebraMap B B' b₀)
                (fun i => algebraMap B B' (b i)) := by
            apply (exteriorPower.zeroEquiv B' (ModuleOfDifferentials A' B')).injective
            simp [deRhamDegreeZeroEquivA, deRhamDegreeZeroEquiv,
              deRhamGenerator, exteriorPower.zeroEquiv]
          have hone : deRhamUniversalDifferential A B b₀ =
              deRhamGenerator 1 1 (fun _ => b₀) := by
            apply (exteriorPower.oneEquiv B (ModuleOfDifferentials A B)).injective
            simp [deRhamUniversalDifferential, deRhamDegreeOneEquivA,
              deRhamDegreeOneEquiv, deRhamGenerator, exteriorPower.oneEquiv]
          have hone' : deRhamUniversalDifferential A' B'
                (algebraMap B B' b₀) =
              deRhamGenerator 1 1 (fun _ => algebraMap B B' b₀) := by
            apply (exteriorPower.oneEquiv B' (ModuleOfDifferentials A' B')).injective
            simp [deRhamUniversalDifferential, deRhamDegreeOneEquivA,
              deRhamDegreeOneEquiv, deRhamGenerator, exteriorPower.oneEquiv]
          rw [deRhamDifferential_zero (A := A) (B := B),
            deRhamDifferential_zero (A := A') (B := B')]
          rw [(componentData 0).2 b₀ b]
          change component 1
              (deRhamUniversalDifferential A B
                ((deRhamDegreeZeroEquivA A B).symm
                  (deRhamGenerator 0 b₀ b))) =
            deRhamUniversalDifferential A' B'
              ((deRhamDegreeZeroEquivA A' B').symm
                (deRhamGenerator 0 (algebraMap B B' b₀)
                  (fun i => algebraMap B B' (b i))))
          rw [← hzero, ← hzero',
            (deRhamDegreeZeroEquivA A B).symm_apply_apply,
            (deRhamDegreeZeroEquivA A' B').symm_apply_apply, hone,
            (componentData 1).2 1 (fun _ => b₀)]
          simp only [map_one]
          rw [← hone']
        · simp
        · intro x y hx hy ihx ihy
          simp only [map_add, ihx, ihy]
        · intro a x hx ih
          have hscalar (q : ℕ) (a : A) (y : deRhamTerm A' B' q) :
              a • y = (algebraMap A A' a) • y := by
            change (algebraMap A B' a) • y =
              (algebraMap A' B' (algebraMap A A' a)) • y
            rw [show algebraMap A B' a =
                algebraMap A' B' (algebraMap A A' a) by
              exact (congrArg (fun f : A →+* B' => f a)
                (IsScalarTower.algebraMap_eq A A' B'))]
          calc
            component 1 (deRhamDifferential (A := A) (B := B) 0 (a • x)) =
                component 1 (a • deRhamDifferential (A := A) (B := B) 0 x) := by
              exact congrArg (component 1)
                ((deRhamDifferential (A := A) (B := B) 0).map_smul a x)
            _ = a • component 1 (deRhamDifferential (A := A) (B := B) 0 x) :=
              (component 1).map_smul _ _
            _ = (algebraMap A A' a) • component 1
                (deRhamDifferential (A := A) (B := B) 0 x) := by
              exact hscalar 1 a _
            _ = (algebraMap A A' a) •
                deRhamDifferential (A := A') (B := B') 0 (component 0 x) := by
              rw [ih]
            _ = deRhamDifferential (A := A') (B := B') 0
                ((algebraMap A A' a) • component 0 x) := by
              exact ((deRhamDifferential (A := A') (B := B') 0).map_smul
                (algebraMap A A' a) (component 0 x)).symm
            _ = deRhamDifferential (A := A') (B := B') 0
                (a • component 0 x) := by
              exact congrArg (deRhamDifferential (A := A') (B := B') 0)
                (hscalar 0 a _).symm
            _ = deRhamDifferential (A := A') (B := B') 0
                (component 0 (a • x)) := by
              exact congrArg (deRhamDifferential (A := A') (B := B') 0)
                ((component 0).map_smul a x).symm
    | succ p =>
        have hω : ω ∈ Submodule.span A (deRhamGenerators (A := A) (B := B) (p + 1)) := by
          rw [deRhamGenerators_span (A := A) (B := B) (p + 1)]
          exact Submodule.mem_top
        refine Submodule.span_induction (p := fun x _ =>
            component (p + 2) (deRhamDifferential (A := A) (B := B) (p + 1) x) =
              deRhamDifferential (A := A') (B := B') (p + 1) (component (p + 1) x))
          ?_ ?_ ?_ ?_ hω
        · rintro _ ⟨z, rfl⟩
          rcases z with ⟨b₀, b⟩
          rw [deRhamDifferential_on_generator (p + 1)
            (Nat.succ_le_succ (Nat.zero_le p))]
          rw [show deRhamDifferentialGenerator (p + 1) b₀ b =
              deRhamGenerator (p + 2) 1 (Fin.cons b₀ b) by
            simp only [deRhamDifferentialGenerator, deRhamGenerator, one_smul]
            congr 1
            funext i
            refine Fin.cases ?_ (fun j => ?_) i <;> rfl]
          rw [(componentData (p + 2)).2 1 (Fin.cons b₀ b)]
          rw [(componentData (p + 1)).2 b₀ b]
          rw [deRhamDifferential_on_generator (p + 1)
            (Nat.succ_le_succ (Nat.zero_le p))]
          simp only [deRhamGenerator, deRhamDifferentialGenerator]
          simp only [map_one, one_smul]
          congr 1
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        · simp
        · intro x y hx hy ihx ihy
          simp only [map_add, ihx, ihy]
        · intro a x hx ih
          have hscalar (q : ℕ) (a : A) (y : deRhamTerm A' B' q) :
              a • y = (algebraMap A A' a) • y := by
            change (algebraMap A B' a) • y =
              (algebraMap A' B' (algebraMap A A' a)) • y
            rw [show algebraMap A B' a =
                algebraMap A' B' (algebraMap A A' a) by
              exact (congrArg (fun f : A →+* B' => f a)
                (IsScalarTower.algebraMap_eq A A' B'))]
          calc
            component (p + 2)
                (deRhamDifferential (A := A) (B := B) (p + 1) (a • x)) =
                component (p + 2)
                  (a • deRhamDifferential (A := A) (B := B) (p + 1) x) := by
                    exact congrArg (component (p + 2))
                      ((deRhamDifferential (A := A) (B := B) (p + 1)).map_smul a x)
            _ = a • component (p + 2)
                (deRhamDifferential (A := A) (B := B) (p + 1) x) :=
              (component (p + 2)).map_smul _ _
            _ = (algebraMap A A') a • component (p + 2)
                (deRhamDifferential (A := A) (B := B) (p + 1) x) := by
              exact hscalar (p + 2) a _
            _ = (algebraMap A A') a •
                deRhamDifferential (A := A') (B := B') (p + 1)
                  (component (p + 1) x) := by rw [ih]
            _ = deRhamDifferential (A := A') (B := B') (p + 1)
                ((algebraMap A A') a • component (p + 1) x) := by
              exact ((deRhamDifferential (A := A') (B := B') (p + 1)).map_smul
                (algebraMap A A' a) (component (p + 1) x)).symm
            _ = deRhamDifferential (A := A') (B := B') (p + 1)
                (a • component (p + 1) x) := by
              exact congrArg (deRhamDifferential (A := A') (B := B') (p + 1))
                (hscalar (p + 1) a _).symm
            _ = deRhamDifferential (A := A') (B := B') (p + 1)
                (component (p + 1) (a • x)) := by
              exact congrArg (deRhamDifferential (A := A') (B := B') (p + 1))
                ((component (p + 1)).map_smul a x).symm

noncomputable def deRhamMapData
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B'] :
    DeRhamMapData (A := A) (A' := A') (B := B) (B' := B') :=
  Classical.choice (deRhamMapData_exists (A := A) (A' := A') (B := B) (B' := B'))

noncomputable def deRhamMapComponent
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
    (p : ℕ) : deRhamTerm A B p →ₗ[A] deRhamTerm A' B' p :=
  (deRhamMapData (A := A) (A' := A') (B := B) (B' := B')).component p

theorem deRhamMapComponent_on_generator
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
    (p : ℕ) (b₀ : B) (b : Fin p → B) :
    deRhamMapComponent (A := A) (A' := A') (B := B) (B' := B') p
        (deRhamGenerator p b₀ b) =
      deRhamGenerator p (algebraMap B B' b₀)
        (fun i => algebraMap B B' (b i)) := by
  exact (deRhamMapData (A := A) (A' := A') (B := B) (B' := B')).component_on_generator
    p b₀ b

theorem deRhamMapComponent_commutes
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra A' B'] [Algebra B B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
    (p : ℕ) (ω : deRhamTerm A B p) :
    deRhamMapComponent (A := A) (A' := A') (B := B) (B' := B') (p + 1)
        (deRhamDifferential (A := A) (B := B) p ω) =
      deRhamDifferential (A := A') (B := B') p
        (deRhamMapComponent (A := A) (A' := A') (B := B) (B' := B') p ω) := by
  exact (deRhamMapData (A := A) (A' := A') (B := B) (B' := B')).commutes p ω

end
end Formalization.Books.Algebra.Unit132
