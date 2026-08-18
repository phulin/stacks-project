import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Formalization.Books.Derived.Unit37.CompactObjects
import Formalization.Books.Algebra.Unit76.FunctorialitiesForTor
import Formalization.Books.Homology.Unit24.FilteredComplexes
import Formalization.Books.MoreAlgebra.Unit56.DerivedCategoriesOfModules
import Formalization.Books.MoreAlgebra.Unit57.ComputingTor
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
open Formalization.Books.MoreAlgebra.Unit57
open Formalization.Books.MoreAlgebra.Unit58
open Formalization.Books.Algebra.Unit71
open Formalization.Books.Homology.Unit19
open Formalization.Books.Homology.Unit24
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

/- The source uses the scalar extension identity
`(K ⊗_R S) ⊗_S L = K ⊗_R L`.  The right-hand side is regarded as an
`S`-complex by extending scalars; `restrictScalarsComplex` records the
underlying `R`-complex of `L`. -/
theorem baseChange_tensorProduct_iso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (K : Comp R) (L : Comp S) :
    Nonempty (tensorProductComplex S (baseChangeComplex f K) L ≅
      baseChangeComplex f
        (tensorProductComplex R K (restrictScalarsComplex f L))) := by
  sorry

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

/- The displayed identity used in the proof is the canonical reassociation
of total tensor products, written in the source's order. -/
theorem tensorProductComplex_nested_iso
    {R : Type u} [CommRing R] (M K L : Comp R) :
    Nonempty (tensorProductComplex R M (tensorProductComplex R K L) ≅
      tensorProductComplex R (tensorProductComplex R M K) L) := by
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

/-- A direct sum of shifts of the tensor unit complex, using the generic
    construction from Derived Categories, Chapter 37. -/
noncomputable abbrev IsDirectSumOfUnitShifts
    {R : Type u} [CommRing R] (X : Comp R) : Prop :=
  Formalization.Books.Derived.Unit37.IsDirectSumOfShifts
    (C := Comp R) (fun _ : ULift.{u} PUnit => tensorUnit R) X

/-- A filtered complex whose successive inclusions split termwise and whose
successive quotients are direct sums of shifts of `R`.  The indexing starts
at `F₀`; the source's `F₋₁ = 0` is the canonical initial zero convention. -/
structure SplitFreeFiltration
    {R : Type u} [CommRing R] (P : Comp R) where
  system : ℕ ⥤ Comp R
  exhaustive : Nonempty (colimit system ≅ P)
  /-- The quotient `F₀/F₋₁`, with `F₋₁ = 0`, is free in the source's sense. -/
  initial_piece : IsDirectSumOfUnitShifts (system.obj 0)
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
  exact_in_first : ∀ M : D R,
    Nonempty (ExactTriangulatedFunctorData (tensorFunctorSlice functor M))
  represented : ∀ (X Y : D R),
    ∃ (K L : Comp R),
      Nonempty ((derivedComplexQuotient R).obj K ≅ X) ∧
      Nonempty ((derivedComplexQuotient R).obj L ≅ Y) ∧
      IsKFlat K ∧ IsKFlat L ∧
      Nonempty (functor.obj (X, Y) ≅
        (derivedComplexQuotient R).obj (tensorProductComplex R K L))
  extends_boundedAbove : ∀ (M : ModuleCat.{u} R),
    Nonempty (
      (DerivedCategory.Minus.ι (C := ModuleCat.{u} R) ⋙
        tensorFunctorSlice functor
          ((DerivedCategory.Minus.ι (C := ModuleCat.{u} R)).obj
            (moduleInDMinus R M))) ≅
      (derivedTensorModuleFunctor R M ⋙
        DerivedCategory.Minus.ι (C := ModuleCat.{u} R)))

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

/- A K-flat representative of a derived object.  This is the resolution
choice used in the source construction; the representative-level
independence statement below is the precise interface needed to make the
resulting derived tensor product independent of that choice. -/
structure KFlatRepresentative
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (X : D R) where
  complex : Comp R
  iso : Nonempty ((derivedComplexQuotient R).obj complex ≅ X)
  kFlat : IsKFlat complex

theorem kFlatRepresentative_tensor_independent
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {X Y : D R} (K K' : KFlatRepresentative R X)
    (L L' : KFlatRepresentative R Y) :
    Nonempty ((derivedComplexQuotient R).obj
        (tensorProductComplex R K.complex L.complex) ≅
      (derivedComplexQuotient R).obj
        (tensorProductComplex R K'.complex L'.complex)) := by
  sorry

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
  (derivedTensorProductData (R := R)).exact_in_first M

/- The unbounded construction extends the bounded-above derived tensor
   functor from the preceding chapter.  The inclusion of the bounded-above
   derived category into the unbounded one is the canonical full-subcategory
   inclusion supplied by Mathlib. -/
theorem derivedTensor_extends_boundedAbove
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) :
    Nonempty (
      (DerivedCategory.Minus.ι (C := ModuleCat.{u} R) ⋙
        derivedTensorFunctor
          ((DerivedCategory.Minus.ι (C := ModuleCat.{u} R)).obj
            (moduleInDMinus R M))) ≅
      (derivedTensorModuleFunctor R M ⋙
        DerivedCategory.Minus.ι (C := ModuleCat.{u} R))) := by
  exact (derivedTensorProductData (R := R)).extends_boundedAbove M

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

/- The signed flip on K-flat representatives is induced by the canonical
   Koszul-signed braiding of total tensor products from Chapter 58. -/
theorem derivedTensor_flip_on_representatives
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : Comp R) :
    Nonempty ((derivedComplexQuotient R).obj (tensorProductComplex R K L) ≅
      (derivedComplexQuotient R).obj (tensorProductComplex R L K)) := by
  sorry

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

theorem derivedTensor_triple_on_representatives
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L M : Comp R) :
    Nonempty ((derivedComplexQuotient R).obj
        (tensorProductComplex R (tensorProductComplex R K L) M) ≅
      (derivedComplexQuotient R).obj
        (tensorProductComplex R K (tensorProductComplex R L M))) := by
  sorry

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

/-! ## Derived change of rings -/

/- The ordinary tensor product of a complex of `R`-modules with a complex of
   `A`-modules is represented using extension of scalars followed by the
   canonical total tensor product over `A`.  This is the source's concrete
   model for the cross-ring tensor product. -/
noncomputable abbrev crossTensorComplex
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (K : Comp R) (N : Comp A) : Comp A :=
  tensorProductComplex A (baseChangeComplex f K) N

/- A package for the left derived functor with values in complexes of
   `A`-modules.  The represented field records the K-flat computation used in
   the source construction. -/
structure DerivedTensorOverData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) (N : Comp A) where
  functor : D R ⥤ D A
  exact : Nonempty (ExactTriangulatedFunctorData functor)
  represented : ∀ (K : Comp R), IsKFlat K →
    Nonempty (functor.obj ((derivedComplexQuotient R).obj K) ≅
      (derivedComplexQuotient A).obj (crossTensorComplex f K N))

theorem exists_derivedTensorOverData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) (N : Comp A) :
    Nonempty (DerivedTensorOverData f N) := by
  sorry

noncomputable def derivedTensorOverFunctor
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) (N : Comp A) :
    D R ⥤ D A :=
  (Classical.choice (exists_derivedTensorOverData f N)).functor

theorem derivedTensorOver_exact
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) (N : Comp A) :
    Nonempty (ExactTriangulatedFunctorData (derivedTensorOverFunctor f N)) := by
  exact (Classical.choice (exists_derivedTensorOverData f N)).exact

theorem derivedTensorOver_represented
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) (N : Comp A)
    (K : Comp R) (hK : IsKFlat K) :
    Nonempty ((derivedTensorOverFunctor f N).obj ((derivedComplexQuotient R).obj K) ≅
      (derivedComplexQuotient A).obj (crossTensorComplex f K N)) := by
  exact (Classical.choice (exists_derivedTensorOverData f N)).represented K hK

/- Functoriality in the fixed complex is recorded separately because the
   source constructs it by changing a K-flat resolution. -/
theorem derivedTensorOver_map
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    {L N : Comp A} (g : L ⟶ N) :
    Nonempty (derivedTensorOverFunctor f L ⟶ derivedTensorOverFunctor f N) := by
  sorry

theorem derivedTensorOver_map_iso_of_quasiIso
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    {L N : Comp A} (g : L ⟶ N) (hg : QuasiIso g) :
    Nonempty (derivedTensorOverFunctor f L ≅ derivedTensorOverFunctor f N) := by
  sorry

/- The derived base-change functor is the special case in which the second
   complex is the tensor unit. -/
noncomputable abbrev derivedBaseChangeFunctor
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    D R ⥤ D A :=
  derivedTensorOverFunctor f (tensorUnit A)

theorem derivedBaseChange_extends_boundedAbove
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    Nonempty (
      (DerivedCategory.Minus.ι (C := ModuleCat.{u} R) ⋙
        derivedBaseChangeFunctor f) ≅
      (derivedTensorAlgebraFunctor f ⋙
        DerivedCategory.Minus.ι (C := ModuleCat.{u} A))) := by
  sorry

/- Restriction of scalars on derived categories.  Keeping this as a chosen
   datum makes the adjunction statement independent of a particular model of
   the localization. -/
structure DerivedRestrictionData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) where
  functor : D A ⥤ D R
  exact : Nonempty (ExactTriangulatedFunctorData functor)

theorem exists_derivedRestrictionData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    Nonempty (DerivedRestrictionData f) := by
  sorry

noncomputable def derivedRestrictionFunctor
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    D A ⥤ D R :=
  (Classical.choice (exists_derivedRestrictionData f)).functor

theorem derivedBaseChange_leftAdjoint
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    Nonempty (Adjunction (derivedBaseChangeFunctor f)
      (derivedRestrictionFunctor f)) := by
  sorry

/- The associativity statement for a chain of ring maps. -/
theorem derived_double_baseChange
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    [HasDerivedCategory.{w} (ModuleCat.{u} C)]
    (f : A →+* B) (g : B →+* C) (N : Comp B) (K : Comp C) :
    Nonempty ((derivedTensorOverFunctor f N ⋙
        derivedTensorOverFunctor g K) ≅
      derivedTensorOverFunctor (g.comp f) (crossTensorComplex g N K)) := by
  sorry

/-! ## Tor independence and the comparison map -/

structure RingMapSquare
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] where
  rToA : R →+* A
  rToR' : R →+* R'
  aToA' : A →+* A'
  r'ToA' : R' →+* A'
  commutes : ∀ x : R, aToA' (rToA x) = r'ToA' (rToR' x)

def TorIndependent
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) : Prop :=
  ∀ i : ℕ, 0 < i →
    IsZero (Tor (algebraAsRModule f) (algebraAsRModule g) i)

structure DerivedComparisonData
    (S : RingMapSquare R A R' A')
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')] where
  comparison : ∀ K : D A,
    (derivedBaseChangeFunctor S.rToR').obj
        ((derivedRestrictionFunctor S.rToA).obj K) ⟶
      (derivedRestrictionFunctor S.r'ToA').obj
        ((derivedBaseChangeFunctor S.aToA').obj K)

theorem exists_derivedComparisonData
    (S : RingMapSquare R A R' A')
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')] :
    Nonempty (DerivedComparisonData S) := by
  sorry

noncomputable def derivedComparisonMap
    (S : RingMapSquare R A R' A')
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')] (K : D A) :
    (derivedBaseChangeFunctor S.rToR').obj
        ((derivedRestrictionFunctor S.rToA).obj K) ⟶
      (derivedRestrictionFunctor S.r'ToA').obj
        ((derivedBaseChangeFunctor S.aToA').obj K) :=
  (Classical.choice (exists_derivedComparisonData S)).comparison K

def IsTensorBaseChange
    (S : RingMapSquare R A R' A') : Prop :=
  letI : Algebra R A := S.rToA.toAlgebra
  letI : Algebra R R' := S.rToR'.toAlgebra
  ∃ e : A' ≃+* A ⊗[R] R',
    e.toRingHom.comp S.aToA' =
        Algebra.TensorProduct.includeLeftRingHom (A := A) ∧
      e.toRingHom.comp S.r'ToA' =
        Algebra.TensorProduct.includeRight.toRingHom (A := R')

theorem derivedComparison_iso_of_torIndependent
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (S : RingMapSquare R A R' A') (hS : IsTensorBaseChange S)
    (hTor : TorIndependent S.rToA S.rToR') (K : D A) :
    IsIso (derivedComparisonMap S K) := by
  sorry

def ModuleTorIndependent
    {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) : Prop :=
  ∀ i : ℕ, 0 < i → IsZero (Tor M N i)

theorem flat_baseChange_preserves_torIndependent
    {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (hf : RingHom.Flat f)
    (M N : ModuleCat.{u} R) (h : ModuleTorIndependent M N) :
    ModuleTorIndependent (extendedModule f M) (extendedModule f N) := by
  sorry

theorem tor_flat_baseChange_iso
    {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (hf : RingHom.Flat f)
    (M N : ModuleCat.{u} R) (i : ℕ) :
    IsIso (Formalization.Books.Algebra.Unit76.torFlatBaseChangeMap f M N i) := by
  exact Formalization.Books.Algebra.Unit76.flat_base_change_tor f hf M N i

structure TorPrimeTriple
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) where
  p : Ideal A
  q : Ideal B
  r : Ideal R
  hp : p.IsPrime
  hq : q.IsPrime
  hr : r.IsPrime
  p_over_r : r = p.comap f
  q_over_r : r = q.comap g

def TorIndependentLocalAtPrime
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) (P : TorPrimeTriple f g) : Prop :=
  letI := P.hp
  letI := P.hq
  letI := P.hr
  ∀ i : ℕ, 0 < i →
    IsZero (Tor
      ((ModuleCat.restrictScalars
        (Localization.localRingHom P.r P.p f P.p_over_r)).obj
        (ModuleCat.of (Localization.AtPrime P.p) (Localization.AtPrime P.p)))
      ((ModuleCat.restrictScalars
        (Localization.localRingHom P.r P.q g P.q_over_r)).obj
        (ModuleCat.of (Localization.AtPrime P.q) (Localization.AtPrime P.q))) i)

def TorIndependentAtPrimes
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) : Prop :=
  ∀ P : TorPrimeTriple f g, TorIndependentLocalAtPrime f g P

theorem torIndependent_iff_localized_at_primes
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) :
    TorIndependent f g ↔ TorIndependentAtPrimes f g := by
  sorry

/- A canonical `A`-module structure on `Tor_R(M,A)` supplied by the
   change-of-rings construction from the preceding algebra chapters. -/
noncomputable def torOverAlgebra
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (M : ModuleCat.{u} R) (i : ℕ) : ModuleCat.{u} A :=
  let T := Classical.choice
    (Formalization.Books.Algebra.Unit76.exists_target_tor_module f M
      (ModuleCat.of A A) i)
  letI : Module A
      (Formalization.Books.Algebra.Unit76.restrictedTor f M
        (ModuleCat.of A A) i) := T.module
  ModuleCat.of A
    (Formalization.Books.Algebra.Unit76.restrictedTor f M
      (ModuleCat.of A A) i)

/-! ## Spectral sequences for Tor -/

def ChainComplexBoundedBelow {R : Type u} [CommRing R]
    (K : ModuleChainComplex R) : Prop :=
  ∃ b : ℕ, ∀ n : ℕ, n < b → IsZero (K.X n)

/- The two spectral sequences in the double-complex example.  The page
   objects and the displayed differentials are kept as categorical module
   maps; the abutment is recorded by its degree-indexed family. -/
structure CohomologyTensorSpectralSequence
    {R : Type u} [CommRing R] (K : ModuleChainComplex R)
    (M : ModuleCat.{u} R) where
  page : ℕ → ℕ → ℕ → ModuleCat.{u} R
  abutment : ℕ → ModuleCat.{u} R
  e₂ : ∀ i j : ℕ,
    Nonempty (page 2 i j ≅ Tor (chainHomology K i) M j)
  e₁ : ∀ i j : ℕ,
    Nonempty (page 1 i j ≅ Tor (K.X i) M j)
  d₂ : ∀ i j : ℕ,
    Tor (chainHomology K i) M j ⟶
      Tor (chainHomology K (i + 1)) M (j - 2)
  d₁ : ∀ i j : ℕ,
    Tor (K.X (i + 1)) M j ⟶ Tor (K.X i) M j

theorem exists_cohomologyTensorSpectralSequence
    {R : Type u} [CommRing R] (K : ModuleChainComplex R)
    (hK : ChainComplexBoundedBelow K) (M : ModuleCat.{u} R) :
    Nonempty (CohomologyTensorSpectralSequence K M) := by
  sorry

/- The change-of-rings spectral sequence is naturally mixed-valued: its page
   is an `S`-module while its abutment is the underlying `R`-module. -/
structure TorChangeRingsSpectralSequence
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) where
  page : ℕ → ℕ → Type u
  e₂ : ∀ n m : ℕ,
    Nonempty (page n m ≃
      (Tor (torOverAlgebra f M m) N n : Type u))
  abutment : ℕ → Type u
  abutment_formula : ∀ k : ℕ,
    Nonempty (abutment k ≃
      (Tor M (ModuleCat.restrictScalars f).obj N k : Type u))

theorem exists_torChangeRingsSpectralSequence
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) :
    Nonempty (TorChangeRingsSpectralSequence f M N) := by
  sorry

structure TorBaseChangeSpectralSequence
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (aToB : A →+* B) (aToA' : A →+* A') (bToB' : B →+* B')
    (M N : ModuleCat.{u} B) where
  page : ℕ → ℕ → Type u
  e₂ : ∀ i j : ℕ,
    Nonempty (page i j ≃
      (Tor
        ((ModuleCat.restrictScalars aToB).obj (Tor M N j))
        ((ModuleCat.restrictScalars aToA').obj (ModuleCat.of A' A')) i : Type u))
  abutment : ℕ → Type u
  abutment_formula : ∀ k : ℕ,
    Nonempty (abutment k ≃
      (Tor
        ((ModuleCat.extendScalars bToB').obj M)
        ((ModuleCat.extendScalars bToB').obj N) k : Type u))

theorem exists_torBaseChangeSpectralSequence
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (aToB : A →+* B) (aToA' : A →+* A') (bToB' : B →+* B')
    (M N : ModuleCat.{u} B)
    (hB : Module.Flat A ((ModuleCat.restrictScalars aToB).obj
      (ModuleCat.of B B) : Type u))
    (hM : Module.Flat A ((ModuleCat.restrictScalars aToB).obj M : Type u))
    (hN : Module.Flat A ((ModuleCat.restrictScalars aToB).obj N : Type u)) :
    Nonempty (TorBaseChangeSpectralSequence aToB aToA' bToB' M N) := by
  sorry

noncomputable abbrev dMinusCohomologyObject
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (n : ℤ) (K : DMinus R) : ModuleCat.{u} R :=
  (dMinusCohomologyFunctor (C := Mod R) n).obj K

noncomputable abbrev derivedTorCohomologyPage
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : DMinus R) (p q : ℤ) : ModuleCat.{u} R :=
  (dMinusCohomologyFunctor (C := Mod R) p).obj
    ((derivedTensorModuleFunctor R (dMinusCohomologyObject q L)).obj K)

structure DerivedTorSpectralSequences
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L : DMinus R) where
  firstPage : ℕ → ℤ → ℤ → ModuleCat.{u} R
  secondPage : ℕ → ℤ → ℤ → ModuleCat.{u} R
  firstE₂ : ∀ p q : ℤ,
    Nonempty (firstPage 2 p q ≅ derivedTorCohomologyPage K L p q)
  secondE₂ : ∀ p q : ℤ,
    Nonempty (secondPage 2 p q ≅
      (dMinusCohomologyFunctor (C := Mod R) p).obj
        ((derivedTensorModuleFunctor R (dMinusCohomologyObject q K)).obj L))
  firstD₂ : ∀ p q : ℤ,
    firstPage 2 p q ⟶ firstPage 2 (p + 2) (q - 1)
  secondD₂ : ∀ p q : ℤ,
    secondPage 2 p q ⟶ secondPage 2 (p + 2) (q - 1)

theorem exists_derivedTorSpectralSequences
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L : DMinus R) :
    Nonempty (DerivedTorSpectralSequences K L) := by
  sorry

/-! ## Products and Tor -/

noncomputable abbrev derivedCohomologyFunctor
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (n : ℤ) :
    D R ⥤ ModuleCat.{u} R :=
  derivedComplexQuotient R ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) n

noncomputable abbrev derivedCohomologyObject
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (n : ℤ) (K : D R) :
    ModuleCat.{u} R :=
  (derivedCohomologyFunctor n).obj K

noncomputable abbrev cohomologyTensorSource
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : D R) (i j : ℤ) : ModuleCat.{u} R :=
  ModuleCat.of R (TensorProduct R
    (derivedCohomologyObject i K : Type u)
    (derivedCohomologyObject j L : Type u))

theorem exists_derivedCohomologyProductMap
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : D R) (i j : ℤ) :
    Nonempty (cohomologyTensorSource K L i j ⟶
      derivedCohomologyObject (i + j) (derivedTensor K L)) := by
  sorry

noncomputable def derivedCohomologyProductMap
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : D R) (i j : ℤ) :
    cohomologyTensorSource K L i j ⟶
      derivedCohomologyObject (i + j) (derivedTensor K L) :=
  Classical.choice (exists_derivedCohomologyProductMap K L i j)

theorem derivedTensor_pullback_iso
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K L : D R) :
    Nonempty (
      derivedTensor ((derivedBaseChangeFunctor f).obj K)
        ((derivedBaseChangeFunctor f).obj L) ≅
      (derivedBaseChangeFunctor f).obj (derivedTensor K L)) := by
  sorry

noncomputable abbrev torProductSource
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (M N : ModuleCat.{u} R) (n m : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A (TensorProduct A
    (torOverAlgebra f M n : Type u) (torOverAlgebra f N m : Type u))

theorem exists_torProductMap
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (M N : ModuleCat.{u} R) (n m : ℕ) :
    Nonempty (torProductSource f M N n m ⟶
      torOverAlgebra f (MonoidalCategory.tensor M N) (n + m)) := by
  sorry

noncomputable def torProductMap
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (M N : ModuleCat.{u} R) (n m : ℕ) :
    torProductSource f M N n m ⟶
      torOverAlgebra f (MonoidalCategory.tensor M N) (n + m) :=
  Classical.choice (exists_torProductMap f M N n m)

/- The multiplication special case is packaged as a graded `A`-algebra
   datum.  The two maps in the source are retained separately. -/
structure TorStarAlgebraData
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) where
  degree : ℕ → ModuleCat.{u} A
  degree_formula : ∀ n : ℕ,
    Nonempty (degree n ≅ torOverAlgebra f (algebraAsRModule g) n)
  product_to_tensor : ∀ n m : ℕ,
    ModuleCat.of A (TensorProduct A (degree n : Type u) (degree m : Type u)) ⟶
      torOverAlgebra f (MonoidalCategory.tensor (algebraAsRModule g)
        (algebraAsRModule g)) (n + m)
  multiplication : ∀ n m : ℕ,
    torOverAlgebra f (MonoidalCategory.tensor (algebraAsRModule g)
      (algebraAsRModule g)) (n + m) ⟶ degree (n + m)

noncomputable def torStarTensorMap
    {R A : Type u} [CommRing R] [CommRing A]
    {M M' N N' : ModuleCat.{u} A} (f : M ⟶ M') (g : N ⟶ N') :
    ModuleCat.of A (TensorProduct A (M : Type u) (N : Type u)) ⟶
      ModuleCat.of A (TensorProduct A (M' : Type u) (N' : Type u)) :=
  ModuleCat.ofHom (TensorProduct.map f.hom g.hom)

theorem exists_torStarAlgebraData
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) :
    Nonempty (TorStarAlgebraData f g) := by
  sorry

noncomputable def torStarAlgebraData
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) : TorStarAlgebraData f g :=
  Classical.choice (exists_torStarAlgebraData f g)

structure TorStarAlgebraHom
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    (f : R →+* A) (gB : R →+* B) (gC : R →+* C)
    (h : B →+* C) (commutes : ∀ r : R, h (gB r) = gC r) where
  component : ∀ n : ℕ,
    (torStarAlgebraData f gB).degree n ⟶ (torStarAlgebraData f gC).degree n
  preserves_product : ∀ n m : ℕ,
    (torStarAlgebraData f gB).product_to_tensor n m ≫
        (torStarAlgebraData f gB).multiplication n m ≫ component (n + m) =
      torStarTensorMap (component n) (component m) ≫
        (torStarAlgebraData f gC).product_to_tensor n m ≫
          (torStarAlgebraData f gC).multiplication n m

theorem exists_torStarAlgebraHom
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    (f : R →+* A) (gB : R →+* B) (gC : R →+* C)
    (h : B →+* C) (commutes : ∀ r : R, h (gB r) = gC r) :
    Nonempty (TorStarAlgebraHom f gB gC h commutes) := by
  sorry

/-! ## Künneth spectral sequence -/

abbrev FilteredComp (R : Type u) [CommRing R] :=
  FilteredComplex (ModuleCat.{u} R)

noncomputable abbrev forgetFilteredComplex
    {R : Type u} [CommRing R] (K : FilteredComp R) : Comp R :=
  filteredComplexUnderlying K

noncomputable def forgetFilteredComplexMap
    {R : Type u} [CommRing R] {K L : FilteredComp R} (f : K ⟶ L) :
    forgetFilteredComplex K ⟶ forgetFilteredComplex L :=
  ((filteredComplexForgetful (C := ModuleCat.{u} R)).mapHomologicalComplex
    (.up ℤ)).map f

def KunnethSummandIndex (n : ℤ) :=
  {ij : ℤ × ℤ // ij.1 + ij.2 = n}

noncomputable abbrev KunnethGradedSum
    {R : Type u} [CommRing R] (K L : FilteredComp R) (n : ℤ) : Comp R :=
  ∐ fun ij : KunnethSummandIndex n =>
    tensorProductComplex R (filteredComplexGradedPiece K ij.1)
      (filteredComplexGradedPiece L ij.2)

/- The filtered total complex and the associated-graded direct-sum formula. -/
structure KunnethFilteredTensorData
    {R : Type u} [CommRing R] (K L : FilteredComp R) where
  total : FilteredComp R
  total_iso : Nonempty (forgetFilteredComplex total ≅
    tensorProductComplex R (forgetFilteredComplex K) (forgetFilteredComplex L))
  graded_piece : ∀ n : ℤ,
    Nonempty (filteredComplexGradedPiece total n ≅ KunnethGradedSum K L n)

def KunnethTermwiseFlat
    {R : Type u} [CommRing R] (K : FilteredComp R) : Prop :=
  ∀ n i : ℤ,
    Module.Flat R ((K.X n).carrier : Type u) ∧
    Module.Flat R (((K.X n).filtration.obj i : ModuleCat.{u} R) : Type u) ∧
    Module.Flat R (gradedPiece (K.X n) i : Type u)

def KunnethFilteredKFlat
    {R : Type u} [CommRing R] (K : FilteredComp R) : Prop :=
  IsKFlat (forgetFilteredComplex K) ∧
    (∀ i : ℤ, IsKFlat (filteredComplexFiltrationStep K i)) ∧
    (∀ i : ℤ, IsKFlat (filteredComplexGradedPiece K i))

theorem exists_kunnethFilteredTensorData
    {R : Type u} [CommRing R] (K L : FilteredComp R)
    (hK : KunnethTermwiseFlat K) (hL : KunnethTermwiseFlat L) :
    Nonempty (KunnethFilteredTensorData K L) := by
  sorry

noncomputable def kunnethFilteredTensorData
    {R : Type u} [CommRing R] (K L : FilteredComp R)
    (hK : KunnethTermwiseFlat K) (hL : KunnethTermwiseFlat L) :
    KunnethFilteredTensorData K L :=
  Classical.choice (exists_kunnethFilteredTensorData K L hK hL)

def FilteredStepAcyclic
    {R : Type u} [CommRing R] (K : FilteredComp R) (i : ℤ) : Prop :=
  IsAcyclic (filteredComplexFiltrationStep K i)

def FilteredStepQuasiIsoBelow
    {R : Type u} [CommRing R] (K : FilteredComp R) : Prop :=
  ∃ a : ℤ, ∀ i : ℤ, i < a,
    QuasiIso (filteredComplexStepToUnderlying K i)

structure KunnethConvergenceHypotheses
    {R : Type u} [CommRing R] (K L : FilteredComp R) where
  termwiseFlat_K : KunnethTermwiseFlat K
  termwiseFlat_L : KunnethTermwiseFlat L
  kFlat_K : KunnethFilteredKFlat K
  kFlat_L : KunnethFilteredKFlat L
  finite_or_asymptotic :
    (FilteredComplexFiniteFiltration K ∧ FilteredComplexFiniteFiltration L) ∨
      ((∃ b : ℤ, ∀ i : ℤ, b < i → FilteredStepAcyclic K i) ∧
       FilteredStepQuasiIsoBelow K ∧
       (∃ b : ℤ, ∀ i : ℤ, b < i → FilteredStepAcyclic L i) ∧
       FilteredStepQuasiIsoBelow L)

noncomputable abbrev kunnethE₁Term
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : FilteredComp R) (p q : ℤ) : ModuleCat.{u} R :=
  ∐ fun ij : KunnethSummandIndex p =>
    derivedCohomologyObject (p + q)
      (derivedTensor
        ((derivedComplexQuotient R).obj (filteredComplexGradedPiece K ij.1))
        ((derivedComplexQuotient R).obj (filteredComplexGradedPiece L ij.2)))

structure KunnethFilteredSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L : FilteredComp R)
    (T : KunnethFilteredTensorData K L) where
  spectral : FilteredComplexSpectralSequence T.total
  first_page : ∀ p q : ℤ,
    Nonempty (spectral.page 1 (p, q) ≅ kunnethE₁Term K L p q)

theorem exists_kunnethFilteredSpectralSequence
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : FilteredComp R) (h : KunnethConvergenceHypotheses K L) :
    Nonempty (KunnethFilteredSpectralSequenceData K L
      (kunnethFilteredTensorData K L h.termwiseFlat_K h.termwiseFlat_L)) := by
  sorry

structure FilteredComplexResolutionData
    {R : Type u} [CommRing R] (K : FilteredComp R) where
  P : FilteredComp R
  map : P ⟶ K
  termwiseFlat : KunnethTermwiseFlat P
  termwise_free : ∀ n i : ℤ,
    Module.Free R ((P.X n).carrier : Type u) ∧
    Module.Free R (((P.X n).filtration.obj i : ModuleCat.{u} R) : Type u) ∧
    Module.Free R (gradedPiece (P.X n) i : Type u)
  kFlat : KunnethFilteredKFlat P
  quasiIso : QuasiIso (forgetFilteredComplexMap map)
  filtration_quasiIso : ∀ i : ℤ,
    ∃ f : filteredComplexFiltrationStep P i ⟶
      filteredComplexFiltrationStep K i, QuasiIso f
  graded_quasiIso : ∀ i : ℤ,
    ∃ f : filteredComplexGradedPiece P i ⟶ filteredComplexGradedPiece K i,
      QuasiIso f

theorem exists_filteredComplexResolutionData
    {R : Type u} [CommRing R] (K : FilteredComp R) :
    Nonempty (FilteredComplexResolutionData K) := by
  sorry

structure KunnethFilteredPropositionData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : FilteredComp R) where
  resolution_K : FilteredComplexResolutionData K
  resolution_L : FilteredComplexResolutionData L
  tensor : KunnethFilteredTensorData resolution_K.P resolution_L.P
    resolution_K.termwiseFlat resolution_L.termwiseFlat
  spectral : KunnethFilteredSpectralSequenceData resolution_K.P resolution_L.P tensor
  bounded : filteredComplexBounded spectral.spectral
  finite_abutment_filtration :
    FilteredComplexCohomologyFiniteFiltration tensor.total
  converges : filteredComplexConverges tensor.total

theorem exists_kunnethFilteredPropositionData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : FilteredComp R) :
    Nonempty (KunnethFilteredPropositionData K L) := by
  sorry

def IsBoundedCochain
    {R : Type u} [CommRing R] (K : Comp R) : Prop :=
  (∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.X n)) ∧
  (∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (K.X n))

def IsBoundedDerivedObject
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K : D R) : Prop :=
  ∃ P : Comp R, Nonempty ((derivedComplexQuotient R).obj P ≅ K) ∧
    IsBoundedCochain P

def kunnethE₂Term
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : D R) (p q : ℤ) : ModuleCat.{u} R :=
  if h : p ≤ 0 then
    ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = q} =>
      Tor (derivedCohomologyObject ij.1 K) (derivedCohomologyObject ij.2 L)
        (-p).toNat
  else 0

structure KunnethSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L : D R) where
  page : ℕ → ℤ → ℤ → ModuleCat.{u} R
  differential : ∀ r : ℕ, ∀ p q : ℤ,
    page r p q ⟶ page r (p + r) (q - r + 1)
  e₂ : ∀ p q : ℤ,
    Nonempty (page 2 p q ≅ kunnethE₂Term K L p q)
  abutment : ℤ → ModuleCat.{u} R
  abutment_formula : ∀ n : ℤ,
    Nonempty (abutment n ≅ derivedCohomologyObject n (derivedTensor K L))

theorem exists_kunnethSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L : D R)
    (hK : IsBoundedDerivedObject K) (hL : IsBoundedDerivedObject L) :
    Nonempty (KunnethSpectralSequenceData K L) := by
  sorry

theorem tor_vanishes_above_one_of_dedekind
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (M N : ModuleCat.{u} R) {i : ℕ} (hi : 1 < i) :
    IsZero (Tor M N i) := by
  sorry

structure KunnethDedekindShortExact
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L : D R) (n : ℤ) where
  left : ModuleCat.{u} R
  middle : ModuleCat.{u} R
  right : ModuleCat.{u} R
  sequence : ShortComplex (ModuleCat.{u} R)
  shortExact : sequence.ShortExact
  left_formula : Nonempty (left ≅
    ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} =>
      ModuleCat.of R (TensorProduct R
        (derivedCohomologyObject ij.1 K : Type u)
        (derivedCohomologyObject ij.2 L : Type u)))
  middle_formula : Nonempty (middle ≅ derivedCohomologyObject n (derivedTensor K L))
  right_formula : Nonempty (right ≅
    ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n + 1} =>
      Tor (derivedCohomologyObject ij.1 K) (derivedCohomologyObject ij.2 L) 1)

theorem exists_kunnethDedekindShortExact
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L : D R)
    (hK : IsBoundedDerivedObject K) (hL : IsBoundedDerivedObject L) (n : ℤ) :
    Nonempty (KunnethDedekindShortExact K L n) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit59
