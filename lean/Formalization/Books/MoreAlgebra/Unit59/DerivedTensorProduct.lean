import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.FinitePresentation
import Formalization.Books.MoreAlgebra.Unit56.DerivedCategoriesOfModules
import Formalization.Books.MoreAlgebra.Unit58.TensorProductsOfComplexes

/-!
# More on Algebra, Chapter 59: Derived tensor product

The source's complexes, total tensor products, homotopy categories, and
derived categories use the canonical constructions from the preceding
chapters.  This file adds the K-flat predicates and the source-facing
interfaces for their resolutions and for derived tensor products.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit09
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit10
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit58
open ComplexShape
open HomologicalComplex
open scoped BigOperators

universe w u v

namespace Formalization.Books.MoreAlgebra.Unit59

/-! ## Complexes and the K-flat predicate -/

/-- The source's category `Comp(R)` of integer-indexed cochain complexes of
`R`-modules. -/
abbrev Comp (R : Type u) [CommRing R] :=
  Formalization.Books.MoreAlgebra.Unit58.Comp R

/-- The source's homotopy category `K(R)`. -/
abbrev K (R : Type u) [CommRing R] :=
  Formalization.Books.MoreAlgebra.Unit58.K R

/-- The source's derived category `D(R)`. -/
abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  Formalization.Books.MoreAlgebra.Unit56.D R

/-- The quotient functor from complexes to the homotopy category. -/
noncomputable abbrev homotopyQuotient (R : Type u) [CommRing R] :
    Comp R ⥤ K R :=
  HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)

/-- The quotient functor from complexes to the derived category. -/
noncomputable abbrev derivedComplexQuotient (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Comp R ⥤ D R :=
  DerivedCategory.Q

/-- A complex is acyclic when all of its homology objects are zero. -/
abbrev IsAcyclic {R : Type u} [CommRing R] (K : Comp R) : Prop :=
  Formalization.Books.Derived.Unit11.AcyclicComplex K

/-- A complex is K-flat when tensoring it with every acyclic complex gives an
acyclic total tensor product. -/
def IsKFlat {R : Type u} [CommRing R] (K : Comp R) : Prop :=
  ∀ (M : Comp R), IsAcyclic M →
    IsAcyclic (tensorProductComplex R M K)

/-- Tensoring a complex with a module means tensoring with the stalk complex
concentrated in degree zero. -/
noncomputable abbrev tensorWithModule
    {R : Type u} [CommRing R] (K : Comp R) (M : ModuleCat.{u} R) : Comp R :=
  tensorProductComplex R K
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)

/-- Extension of scalars applied degreewise to a cochain complex. -/
noncomputable abbrev baseChangeComplex
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (K : Comp R) : Comp S :=
  ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K

/-- Flatness of every term of a complex. -/
def TermwiseFlat {R : Type u} [CommRing R] (K : Comp R) : Prop :=
  ∀ n : ℤ, Module.Flat R (K.X n : Type u)

/-- Surjectivity of every component of a map of module complexes. -/
def TermwiseSurjective {R : Type u} [CommRing R]
    {K L : Comp R} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, Function.Surjective (f.f n).hom

/-- The K-flat property on an object of the homotopy category, expressed by
the existence of a K-flat complex representative. -/
def IsKFlatObject {R : Type u} [CommRing R] (X : K R) : Prop :=
  ∃ P : Comp R,
    Nonempty ((homotopyQuotient R).obj P ≅ X) ∧ IsKFlat P

/-! ## Permanence properties of K-flat complexes -/

/-- A K-flat complex makes tensoring on the right preserve quasi-isomorphisms
in the homotopy category. -/
theorem kFlat_preserves_quasiIso
    {R : Type u} [CommRing R] (P : Comp R) (hP : IsKFlat P)
    {L M : K R} (f : L ⟶ M)
    (hf : Formalization.Books.MoreAlgebra.Unit56.quasiIsoInK R f) :
    Formalization.Books.MoreAlgebra.Unit56.quasiIsoInK R
      ((tensorRightHomotopyFunctor R P).map f) := by
  sorry

/-- Base change of a K-flat complex is K-flat. -/
theorem baseChange_kFlat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (K : Comp R) (hK : IsKFlat K) :
    IsKFlat (baseChangeComplex f K) := by
  sorry

/-- The total tensor product of two K-flat complexes is K-flat. -/
theorem tensorProduct_kFlat
    {R : Type u} [CommRing R] (K L : Comp R)
    (hK : IsKFlat K) (hL : IsKFlat L) :
    IsKFlat (tensorProductComplex R K L) := by
  sorry

/-- Two K-flat objects in a distinguished triangle force the third object to
be K-flat. -/
theorem kFlat_two_of_three_triangle₁₂
    {R : Type u} [CommRing R] (T : Triangle (K R))
    (hT : T ∈ distTriang (K R))
    (h₁₂ : IsKFlatObject T.obj₁ ∧ IsKFlatObject T.obj₂) :
    IsKFlatObject T.obj₃ := by
  sorry

theorem kFlat_two_of_three_triangle₂₃
    {R : Type u} [CommRing R] (T : Triangle (K R))
    (hT : T ∈ distTriang (K R))
    (h₂₃ : IsKFlatObject T.obj₂ ∧ IsKFlatObject T.obj₃) :
    IsKFlatObject T.obj₁ := by
  sorry

theorem kFlat_two_of_three_triangle₁₃
    {R : Type u} [CommRing R] (T : Triangle (K R))
    (hT : T ∈ distTriang (K R))
    (h₁₃ : IsKFlatObject T.obj₁ ∧ IsKFlatObject T.obj₃) :
    IsKFlatObject T.obj₂ := by
  sorry

/-- Two K-flat complexes in a short exact sequence force the third one to be
K-flat when the quotient is termwise flat. -/
theorem kFlat_two_of_three_shortExact₁₂
    {R : Type u} [CommRing R] {S : ShortComplex (Comp R)}
    (hS : S.ShortExact) (hflat : TermwiseFlat S.X₃)
    (h₁₂ : IsKFlat S.X₁ ∧ IsKFlat S.X₂) :
    IsKFlat S.X₃ := by
  sorry

theorem kFlat_two_of_three_shortExact₂₃
    {R : Type u} [CommRing R] {S : ShortComplex (Comp R)}
    (hS : S.ShortExact) (hflat : TermwiseFlat S.X₃)
    (h₂₃ : IsKFlat S.X₂ ∧ IsKFlat S.X₃) :
    IsKFlat S.X₁ := by
  sorry

theorem kFlat_two_of_three_shortExact₁₃
    {R : Type u} [CommRing R] {S : ShortComplex (Comp R)}
    (hS : S.ShortExact) (hflat : TermwiseFlat S.X₃)
    (h₁₃ : IsKFlat S.X₁ ∧ IsKFlat S.X₃) :
    IsKFlat S.X₂ := by
  sorry

/-- A bounded-above complex of flat modules is K-flat. -/
theorem boundedAbove_flat_isKFlat
    {R : Type u} [CommRing R] (P : Comp R)
    (hP : Formalization.Books.Derived.Unit08.IsBoundedAbove P)
    (hflat : TermwiseFlat P) :
    IsKFlat P := by
  sorry

/-- A filtered colimit of K-flat complexes is K-flat. -/
theorem filteredColimit_kFlat
    {R : Type u} [CommRing R] {J : Type v} [Category.{w} J]
    [IsFilteredOrEmpty J] (F : J ⥤ Comp R) [HasColimit F]
    (hF : ∀ j : J, IsKFlat (F.obj j)) :
    IsKFlat (colimit F) := by
  sorry

/-- The sequential-colimit instance of filtered-colimit preservation. -/
theorem sequentialColimit_kFlat
    {R : Type u} [CommRing R] (F : ℕ ⥤ Comp R) [HasColimit F]
    (hF : ∀ n : ℕ, IsKFlat (F.obj n)) :
    IsKFlat (colimit F) := by
  sorry

/-- A complex which becomes acyclic after tensoring with every finitely
presented module is K-flat. -/
theorem universallyAcyclic_isKFlat
    {R : Type u} [CommRing R] (K : Comp R)
    (hK : ∀ (M : ModuleCat.{u} R),
      Module.FinitePresentation R (M : Type u) →
        IsAcyclic (tensorWithModule K M)) :
    IsKFlat K := by
  sorry

/-! ## K-flat resolutions -/

/-- A K-flat resolution with flat terms, a quasi-isomorphism, and termwise
surjective augmentation. -/
structure KFlatResolution
    {R : Type u} [CommRing R] (M : Comp R) where
  complex : Comp R
  map : complex ⟶ M
  kFlat : IsKFlat complex
  flat : TermwiseFlat complex
  quasiIso : QuasiIso map
  surjective : TermwiseSurjective map

/-- Every complex admits a K-flat resolution with flat terms and termwise
surjective quasi-isomorphism. -/
theorem exists_kFlatResolution
    {R : Type u} [CommRing R] (M : Comp R) :
    Nonempty (KFlatResolution M) := by
  sorry

/-! ## The filtered resolution remark -/

/-- A direct sum of shifts of the tensor unit complex. -/
noncomputable def IsDirectSumOfUnitShifts
    {R : Type u} [CommRing R] (X : Comp R) : Prop :=
  ∃ (I : Type u) (k : I → ℤ),
    Nonempty ((∐ fun i : I =>
      (shiftFunctor (Comp R) (k i)).obj (tensorUnit R)) ≅ X)

/-- A filtered complex whose successive inclusions split termwise and whose
successive quotients are direct sums of shifts of `R`.  The indexing starts
at `F₀`; the source's `F₋₁ = 0` is the canonical initial zero convention. -/
structure SplitFreeFiltration
    {R : Type u} [CommRing R] (P : Comp R) where
  system : ℕ ⥤ Comp R
  exhaustive : Nonempty (colimit system ≅ P)
  inclusions_split : ∀ n : ℕ,
    termwiseSplitInjection
      (system.map (homOfLE (Nat.le_succ n)))
  graded_piece : ∀ n : ℕ,
    IsDirectSumOfUnitShifts
      (cokernel (system.map (homOfLE (Nat.le_succ n))))

/-- The direct sum of the stages of a split-free filtration. -/
noncomputable abbrev filtrationDirectSum
    {R : Type u} [CommRing R] {P : Comp R}
    (F : SplitFreeFiltration P) : Comp R :=
  ∐ fun n : ℕ => F.system.obj n

/-- The shift map on the direct sum of a split-free filtration. -/
noncomputable def filtrationShiftMap
    {R : Type u} [CommRing R] {P : Comp R}
    (F : SplitFreeFiltration P) :
    filtrationDirectSum F ⟶ filtrationDirectSum F :=
  Limits.Sigma.desc (fun n =>
    F.system.map (homOfLE (Nat.le_succ n)) ≫
      Limits.Sigma.ι (fun n : ℕ => F.system.obj n) (n + 1))

/-- The telescope endomorphism `1 - shift` on a filtered direct sum. -/
noncomputable def filtrationTelescopeMap
    {R : Type u} [CommRing R] {P : Comp R}
    (F : SplitFreeFiltration P) :
    filtrationDirectSum F ⟶ filtrationDirectSum F :=
  𝟙 _ - filtrationShiftMap F

/-- The augmentation from the filtered direct sum to a target of a filtered
resolution. -/
noncomputable def filtrationAugmentation
    {R : Type u} [CommRing R] {M P : Comp R}
    (f : P ⟶ M) (F : SplitFreeFiltration P) :
    filtrationDirectSum F ⟶ M :=
  Limits.Sigma.desc (fun n =>
    Limits.colimit.ι F.system n ≫ (Classical.choice F.exhaustive).hom ≫ f)

/-- Every complex has a quasi-isomorphic split-free filtered resolution. -/
theorem exists_splitFreeFiltration_resolution
    {R : Type u} [CommRing R] (M : Comp R) :
    ∃ (P : Comp R) (f : P ⟶ M), QuasiIso f ∧
      Nonempty (SplitFreeFiltration P) := by
  sorry

/-- The distinguished triangle on the direct sum of the filtration stages
and the resolved complex. -/
theorem splitFreeFiltration_distinguished_triangle
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {M P : Comp R} (f : P ⟶ M) (hf : QuasiIso f)
    (F : SplitFreeFiltration P) :
    ∃ (c : (derivedComplexQuotient R).obj M ⟶
          (shiftFunctor (D R) (1 : ℤ)).obj
            ((derivedComplexQuotient R).obj (filtrationDirectSum F))),
      Triangle.mk
          ((derivedComplexQuotient R).map (filtrationTelescopeMap F))
          ((derivedComplexQuotient R).map (filtrationAugmentation f F)) c ∈
        distTriang (D R) := by
  sorry

/-- Closure of a property of derived objects under direct sums, distinguished
triangles, and shifts of the tensor unit. -/
def StableDerivedProperty
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P : D R → Prop) : Prop :=
  (∀ {I : Type u} (X : I → D R) [HasCoproduct X],
      (∀ i : I, P (X i)) → P (∐ X)) ∧
    (∀ (T : Triangle (D R)), T ∈ distTriang (D R) →
      ((P T.obj₁ ∧ P T.obj₂) → P T.obj₃) ∧
      ((P T.obj₂ ∧ P T.obj₃) → P T.obj₁) ∧
      ((P T.obj₁ ∧ P T.obj₃) → P T.obj₂)) ∧
    (∀ k : ℤ, P ((shiftFunctor (D R) k).obj
      ((derivedComplexQuotient R).obj (tensorUnit R))))

/-- The filtered resolution criterion propagates such a stable property to
every object of the derived category. -/
theorem stableDerivedProperty_holds_everywhere
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P : D R → Prop) (hP : StableDerivedProperty P) :
    ∀ X : D R, P X := by
  sorry

/-! ## Tensoring on the other side -/

/-- A quasi-isomorphism between K-flat complexes remains a quasi-isomorphism
after tensoring on the other side by any complex. -/
theorem tensor_left_quasiIso_of_kFlat
    {R : Type u} [CommRing R] {P Q : Comp R}
    (α : P ⟶ Q) (hα : QuasiIso α)
    (hP : IsKFlat P) (hQ : IsKFlat Q) (L : Comp R) :
    QuasiIso ((tensorLeftComplexFunctor R L).map α) := by
  sorry

/-! ## Derived tensor product -/

/- The slice of a bifunctor in the second variable.  This keeps the
source's one-sided functor `- ⊗ᴸ M` while retaining functoriality in both
variables for the symmetry and associativity interfaces below. -/
noncomputable def tensorFunctorSlice
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (F : (D R × D R) ⥤ D R) (M : D R) : D R ⥤ D R where
  obj X := F.obj (X, M)
  map {X X'} f := F.map (f, 𝟙 M)
  map_id X := by
    change F.map (𝟙 X, 𝟙 M) = 𝟙 (F.obj (X, M))
    rw [← F.map_id (X, M)]
    rfl
  map_comp {X Y Z} f g := by
    change F.map (Prod.mkHom (f ≫ g) (𝟙 M)) =
      F.map (Prod.mkHom f (𝟙 M)) ≫ F.map (Prod.mkHom g (𝟙 M))
    rw [← F.map_comp]
    congr 1
    ext <;> simp

/-- Data for the derived tensor bifunctor, including its K-flat
representative computation and exactness in each fixed variable. -/
structure DerivedTensorProductData
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  functor : (D R × D R) ⥤ D R
  exact_in_second : ∀ M : D R,
    Nonempty (ExactTriangulatedFunctorData (tensorFunctorSlice functor M))
  represented : ∀ (X Y : D R),
    ∃ (K L : Comp R),
      Nonempty ((derivedComplexQuotient R).obj K ≅ X) ∧
      Nonempty ((derivedComplexQuotient R).obj L ≅ Y) ∧
      IsKFlat K ∧ IsKFlat L ∧
      Nonempty (functor.obj (X, Y) ≅
        (derivedComplexQuotient R).obj (tensorProductComplex R K L))

/-- Existence of the derived tensor bifunctor from K-flat resolutions. -/
theorem exists_derivedTensorProductData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Nonempty (DerivedTensorProductData R) := by
  sorry

/-- A chosen derived tensor bifunctor. -/
noncomputable def derivedTensorProductData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    DerivedTensorProductData R :=
  Classical.choice (exists_derivedTensorProductData (R := R))

/-- The derived tensor bifunctor. -/
noncomputable abbrev derivedTensorProductFunctor
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (D R × D R) ⥤ D R :=
  (derivedTensorProductData (R := R)).functor

/-- The derived tensor product of two objects of `D(R)`. -/
noncomputable abbrev derivedTensor
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (X Y : D R) : D R :=
  (derivedTensorProductFunctor (R := R)).obj (X, Y)

/-- The source's one-sided functor `- ⊗ᴸ_R M`. -/
noncomputable abbrev derivedTensorFunctor
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (M : D R) : D R ⥤ D R :=
  tensorFunctorSlice (derivedTensorProductFunctor (R := R)) M

/-- The map induced by two maps of derived objects. -/
noncomputable abbrev derivedTensorMap
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {X X' Y Y' : D R} (f : X ⟶ X') (g : Y ⟶ Y') :
    derivedTensor X Y ⟶ derivedTensor X' Y' :=
  (derivedTensorProductFunctor (R := R)).map (f, g)

/-- The chosen derived tensor functor is exact and is computed on K-flat
representatives by ordinary total tensor product. -/
theorem derivedTensorFunctor_exact
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (M : D R) :
    Nonempty (ExactTriangulatedFunctorData (derivedTensorFunctor M)) :=
  (derivedTensorProductData (R := R)).exact_in_second M

theorem derivedTensor_represented
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (X Y : D R) :
    ∃ (K L : Comp R),
      Nonempty ((derivedComplexQuotient R).obj K ≅ X) ∧
      Nonempty ((derivedComplexQuotient R).obj L ≅ Y) ∧
      IsKFlat K ∧ IsKFlat L ∧
      Nonempty (derivedTensor X Y ≅
        (derivedComplexQuotient R).obj (tensorProductComplex R K L)) := by
  exact (derivedTensorProductData (R := R)).represented X Y

/-- The choice of K-flat representatives does not affect the derived tensor
functor, up to the canonical natural isomorphism supplied by localization. -/
theorem derivedTensorProduct_choice_independent
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (A B : DerivedTensorProductData R) :
    Nonempty (A.functor ≅ B.functor) := by
  sorry

/-! ## Symmetry and associativity -/

/-- The signed symmetry of derived tensor products, with its naturality in
both variables. -/
structure DerivedTensorSymmetryData
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  iso : ∀ X Y : D R, derivedTensor X Y ≅ derivedTensor Y X
  natural : ∀ {X X' Y Y' : D R} (f : X ⟶ X') (g : Y ⟶ Y'),
    derivedTensorMap f g ≫ (iso X' Y').hom =
      (iso X Y).hom ≫ derivedTensorMap g f

/-- Existence of the derived tensor symmetry. -/
theorem exists_derivedTensorSymmetryData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Nonempty (DerivedTensorSymmetryData R) := by
  sorry

/-- A chosen signed symmetry isomorphism. -/
noncomputable def derivedTensorSymmetryData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    DerivedTensorSymmetryData R :=
  Classical.choice (exists_derivedTensorSymmetryData (R := R))

/-- The canonical flip isomorphism for derived tensor products. -/
theorem derivedTensor_flip
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (X Y : D R) :
    Nonempty (derivedTensor X Y ≅ derivedTensor Y X) := by
  exact ⟨(derivedTensorSymmetryData (R := R)).iso X Y⟩

/-- Naturality of the canonical flip. -/
theorem derivedTensor_flip_natural
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {X X' Y Y' : D R} (f : X ⟶ X') (g : Y ⟶ Y') :
    derivedTensorMap f g ≫
        ((derivedTensorSymmetryData (R := R)).iso X' Y').hom =
      ((derivedTensorSymmetryData (R := R)).iso X Y).hom ≫
        derivedTensorMap g f := by
  exact (derivedTensorSymmetryData (R := R)).natural f g

/-- The derived tensor associator, natural in all three variables. -/
structure DerivedTensorAssociativityData
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  iso : ∀ X Y Z : D R,
    derivedTensor (derivedTensor X Y) Z ≅
      derivedTensor X (derivedTensor Y Z)
  natural : ∀ {X X' Y Y' Z Z' : D R}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
    derivedTensorMap (derivedTensorMap f g) h ≫
        (iso X' Y' Z').hom =
      (iso X Y Z).hom ≫
        derivedTensorMap f (derivedTensorMap g h)

/-- Existence of the associativity isomorphism for derived tensor products. -/
theorem exists_derivedTensorAssociativityData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Nonempty (DerivedTensorAssociativityData R) := by
  sorry

/-- A chosen derived tensor associator. -/
noncomputable def derivedTensorAssociativityData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    DerivedTensorAssociativityData R :=
  Classical.choice (exists_derivedTensorAssociativityData (R := R))

/-- The canonical associativity isomorphism. -/
theorem derivedTensor_triple
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (X Y Z : D R) :
    Nonempty (derivedTensor (derivedTensor X Y) Z ≅
      derivedTensor X (derivedTensor Y Z)) := by
  exact ⟨(derivedTensorAssociativityData (R := R)).iso X Y Z⟩

/-! ## Factorization through a K-flat complex -/

/-- A map out of a K-flat complex factors, up to homotopy, through a
K-flat complex by a quasi-isomorphism. -/
theorem factor_through_kFlat
    {R : Type u} [CommRing R] {K L : Comp R} (a : K ⟶ L)
    (hK : IsKFlat K) :
    ∃ (N : Comp R) (b : K ⟶ N) (c : N ⟶ L),
      IsKFlat N ∧ QuasiIso c ∧
        Nonempty (Homotopy a (b ≫ c)) ∧
        (TermwiseFlat K → TermwiseFlat N) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit59
