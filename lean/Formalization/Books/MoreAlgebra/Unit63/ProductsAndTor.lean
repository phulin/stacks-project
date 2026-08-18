import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Formalization.Books.MoreAlgebra.Unit59.DerivedTensorProduct

/-!
# More on Algebra, Chapter 63: Products and Tor

This file records the product maps in cohomology and Tor.  The derived tensor
product and cohomology functors are the canonical constructions exposed by
Chapters 56--59; the interfaces below package the additional canonical maps
used in this section.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit57
open Formalization.Books.MoreAlgebra.Unit58
open Formalization.Books.MoreAlgebra.Unit59

universe w u v

namespace Formalization.Books.MoreAlgebra.Unit63

/-! ## Derived cohomology products -/

abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] := Unit56.D R

abbrev Comp (R : Type u) [CommRing R] := Unit59.Comp R

noncomputable abbrev derivedCohomology
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (i : ℤ) : D R ⥤ Mod R :=
  DerivedCategory.homologyFunctor (Mod R) i

noncomputable abbrev cochainCohomology
    (R : Type u) [CommRing R] (i : ℤ) : Comp R ⥤ Mod R :=
  HomologicalComplex.homologyFunctor (Mod R) (.up ℤ) i

/- The first displayed map in the source.  It is stated as a `Nonempty`
interface so that clients do not depend on a choice of K-flat resolutions. -/
theorem exists_derivedCohomologyProduct
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K L : D R) (i j : ℤ) :
    Nonempty
      (MonoidalCategory.tensorObj
          ((derivedCohomology R i).obj K)
          ((derivedCohomology R j).obj L) ⟶
        (derivedCohomology R (i + j)).obj (derivedTensor K L)) := by
  sorry

noncomputable def derivedCohomologyProduct
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K L : D R) (i j : ℤ) :
    MonoidalCategory.tensorObj
        ((derivedCohomology R i).obj K)
        ((derivedCohomology R j).obj L) ⟶
      (derivedCohomology R (i + j)).obj (derivedTensor K L) :=
  Classical.choice (exists_derivedCohomologyProduct R K L i j)

/- The cocycle-level construction from the source, for representatives by
K-flat complexes.  The target is ordinary cohomology of the total tensor
product, so the class of `k ⊗ l` is represented by this map. -/
theorem exists_cochainCohomologyProduct
    (R : Type u) [CommRing R] (P Q : Comp R) (i j : ℤ) :
    Nonempty
      (MonoidalCategory.tensorObj
          ((cochainCohomology R i).obj P)
          ((cochainCohomology R j).obj Q) ⟶
        (cochainCohomology R (i + j)).obj
          (tensorProductComplex R P Q)) := by
  sorry

noncomputable def cochainCohomologyProduct
    (R : Type u) [CommRing R] (P Q : Comp R) (i j : ℤ) :
    MonoidalCategory.tensorObj
        ((cochainCohomology R i).obj P)
        ((cochainCohomology R j).obj Q) ⟶
      (cochainCohomology R (i + j)).obj (tensorProductComplex R P Q) :=
  Classical.choice (exists_cochainCohomologyProduct R P Q i j)

def TermwiseProjective {R : Type u} [CommRing R] (P : Comp R) : Prop :=
  ∀ n : ℤ, Projective (P.X n)

theorem boundedAbove_projective_isKFlat
    {R : Type u} [CommRing R] (P : Comp R)
    (hP : IsBoundedAbove P) (hprojective : TermwiseProjective P) :
    IsKFlat P := by
  sorry

/-! ## Base change and the derived tensor product -/

structure DerivedBaseChangeData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) where
  functor : D R ⥤ Unit56.D A
  represented : ∀ (P : Comp R), IsKFlat P →
    Nonempty ((derivedComplexQuotient A).obj (baseChangeComplex f P) ≅
      functor.obj ((derivedComplexQuotient R).obj P))
  tensor : ∀ (K L : D R),
    Nonempty (derivedTensor (R := A) (functor.obj K) (functor.obj L) ≅
      functor.obj (derivedTensor K L))

theorem exists_derivedBaseChangeData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    Nonempty (DerivedBaseChangeData f) := by
  sorry

noncomputable def derivedBaseChangeData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    DerivedBaseChangeData f :=
  Classical.choice (exists_derivedBaseChangeData f)

noncomputable abbrev derivedBaseChange
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    D R ⥤ Unit56.D A :=
  (derivedBaseChangeData f).functor

theorem derivedBaseChange_on_kFlat
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (P : Comp R) (hP : IsKFlat P) :
    Nonempty ((derivedComplexQuotient A).obj (baseChangeComplex f P) ≅
      (derivedBaseChange f).obj ((derivedComplexQuotient R).obj P)) := by
  exact (derivedBaseChangeData f).represented P hP

noncomputable def derivedBaseChange_tensor_iso
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K L : D R) :
    derivedTensor (R := A) ((derivedBaseChange f).obj K)
        ((derivedBaseChange f).obj L) ≅
      (derivedBaseChange f).obj (derivedTensor K L) :=
  Classical.choice ((derivedBaseChangeData f).tensor K L)

theorem baseChange_tensorProduct_representative_iso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (P Q : Comp R) :
    Nonempty (tensorProductComplex A (baseChangeComplex f P)
        (baseChangeComplex f Q) ≅
      baseChangeComplex f (tensorProductComplex R P Q)) := by
  sorry

/-! ## Products on Tor -/

/- Tor of a derived object is the cohomology of its derived base change;
for a module this specializes, via Chapter 57, to `derivedTorAlgebra`. -/
noncomputable abbrev derivedTorComponent
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K : D R) (n : ℕ) : ModuleCat.{u} A :=
  (derivedCohomology A (-((n : ℤ)))).obj
    ((derivedBaseChange f).obj K)

theorem exists_derivedTorProductMap
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K L : D R) (n m : ℕ) :
    Nonempty (MonoidalCategory.tensorObj (derivedTorComponent f K n)
        (derivedTorComponent f L m) ⟶
      derivedTorComponent f (derivedTensor K L) (n + m)) := by
  sorry

noncomputable abbrev torComponent
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (M : Mod R) (n : ℕ) : ModuleCat.{u} A :=
  derivedTorAlgebra f M n

theorem exists_torProductMap
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (M N : Mod R) (n m : ℕ) :
    Nonempty (MonoidalCategory.tensorObj (torComponent f M n)
        (torComponent f N m) ⟶
      torComponent f (MonoidalCategory.tensorObj M N) (n + m)) := by
  sorry

noncomputable def torProductMap
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (M N : Mod R) (n m : ℕ) :
    MonoidalCategory.tensorObj (torComponent f M n)
        (torComponent f N m) ⟶
      torComponent f (MonoidalCategory.tensorObj M N) (n + m) :=
  Classical.choice (exists_torProductMap f M N n m)

/- The multiplication map `B ⊗_R B → B` used in the algebra case. -/
noncomputable def algebraMultiplication
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] :
    MonoidalCategory.tensorObj (ModuleCat.of R B) (ModuleCat.of R B) ⟶
      ModuleCat.of R B :=
  ModuleCat.ofHom (TensorProduct.lift (LinearMap.mul R B))

theorem exists_torMultiplicationMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (μ : MonoidalCategory.tensorObj (ModuleCat.of R B) (ModuleCat.of R B) ⟶
      ModuleCat.of R B) (n m : ℕ) :
    Nonempty
      (torComponent f (MonoidalCategory.tensorObj (ModuleCat.of R B)
          (ModuleCat.of R B)) (n + m) ⟶
        torComponent f (ModuleCat.of R B) (n + m)) := by
  sorry

noncomputable def torMultiplicationMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (n m : ℕ) :
    torComponent f (MonoidalCategory.tensorObj (ModuleCat.of R B)
        (ModuleCat.of R B)) (n + m) ⟶
      torComponent f (ModuleCat.of R B) (n + m) :=
  Classical.choice (exists_torMultiplicationMap f (algebraMultiplication (R := R)
    (B := B)) n m)

noncomputable def torAlgebraProduct
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (n m : ℕ) :
    MonoidalCategory.tensorObj (torComponent f (ModuleCat.of R B) n)
        (torComponent f (ModuleCat.of R B) m) ⟶
      torComponent f (ModuleCat.of R B) (n + m) :=
  torProductMap f (ModuleCat.of R B) (ModuleCat.of R B) n m ≫
    torMultiplicationMap f n m

/-! ## The graded A-algebra carried by Tor-star -/

structure GradedModuleAlgebraData
    (A : Type u) [CommRing A] (V : ℕ → ModuleCat.{u} A) where
  mul : ∀ n m, MonoidalCategory.tensorObj (V n) (V m) ⟶ V (n + m)
  one : MonoidalCategory.tensorUnit (ModuleCat.{u} A) ⟶ V 0
  assoc : ∀ n m k,
    (MonoidalCategory.tensorHom (mul n m) (𝟙 (V k)) ≫ mul (n + m) k) ≫
        eqToHom (by simp [Nat.add_assoc]) =
      (MonoidalCategory.associator (V n) (V m) (V k)).hom ≫
        MonoidalCategory.tensorHom (𝟙 (V n)) (mul m k) ≫ mul n (m + k)
  left_unit : ∀ n,
    (MonoidalCategory.leftUnitor (V n)).hom =
      MonoidalCategory.tensorHom one (𝟙 (V n)) ≫ mul 0 n ≫
        eqToHom (by simp)
  right_unit : ∀ n,
    (MonoidalCategory.rightUnitor (V n)).hom =
      MonoidalCategory.tensorHom (𝟙 (V n)) one ≫ mul n 0 ≫
        eqToHom (by simp)

noncomputable abbrev torStarComponents
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (B : Type u) [CommRing B] [Algebra R B] : ℕ → ModuleCat.{u} A :=
  fun n => torComponent f (ModuleCat.of R B) n

structure TorStarAlgebraData
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) where
  algebra : GradedModuleAlgebraData A (torStarComponents f B)
  product_eq : ∀ n m, algebra.mul n m = torAlgebraProduct f n m

theorem exists_torStarAlgebra
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    Nonempty (TorStarAlgebraData (B := B) f) := by
  sorry

noncomputable def torStarAlgebra
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    TorStarAlgebraData (B := B) f :=
  Classical.choice (exists_torStarAlgebra f)

structure GradedModuleAlgebraHom
    {A : Type u} [CommRing A] {V W : ℕ → ModuleCat.{u} A}
    (v : GradedModuleAlgebraData A V)
    (w : GradedModuleAlgebraData A W) where
  map : ∀ n, V n ⟶ W n
  map_one : v.one ≫ map 0 = w.one
  map_mul : ∀ n m,
    v.mul n m ≫ map (n + m) =
      MonoidalCategory.tensorHom (map n) (map m) ≫ w.mul n m

theorem exists_torComponentMap
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (φ : B →ₐ[R] C) (n : ℕ) :
    Nonempty (torComponent f (ModuleCat.of R B) n ⟶
      torComponent f (ModuleCat.of R C) n) := by
  sorry

noncomputable def torComponentMap
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (φ : B →ₐ[R] C) (n : ℕ) :
    torComponent f (ModuleCat.of R B) n ⟶
      torComponent f (ModuleCat.of R C) n :=
  Classical.choice (exists_torComponentMap f φ n)

theorem torStar_functoriality
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C]
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (φ : B →ₐ[R] C) :
    Nonempty { h : GradedModuleAlgebraHom (torStarAlgebra (B := B) f).algebra
        (torStarAlgebra (B := C) f).algebra //
      ∀ n, h.map n = torComponentMap f φ n } := by
  sorry

end Formalization.Books.MoreAlgebra.Unit63
