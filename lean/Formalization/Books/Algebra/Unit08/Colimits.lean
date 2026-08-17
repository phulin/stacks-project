import Formalization.Books.Categories.Unit19.FilteredColimits
import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
# Commutative Algebra, Chapter 8: Colimits

This file formalizes the precise definitions, constructions, examples, and
exactness statements in the `Colimits` section of `books/algebra.tex`.
Systems of modules are represented by the existing functor category over a
preorder; the explicit quotient models use Mathlib's direct-sum and directed
colimit constructions.
-/

namespace Formalization.Books.Algebra.Unit08

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21

universe u v w v' w'

noncomputable section

variable {R : Type u} [CommRing R] {I : Type v} [Preorder I]

/-! ## Systems of modules and the general colimit quotient -/

/-- A system of `R`-modules over a preorder, represented by the canonical
functor from the associated preorder category. -/
abbrev ModuleSystem (R : Type u) [CommRing R] (I : Type v) [Preorder I] :=
  I ⥤ ModuleCat.{max v w} R

/-- The transition linear map attached to a morphism in a module system. -/
def moduleSystemMap (M : ModuleSystem R I) {i j : I} (h : i ≤ j) :
    (M.obj i : Type (max v w)) →ₗ[R] (M.obj j : Type (max v w)) :=
  (M.map (homOfLE h)).hom

/- The identity and composition requirements in the source definition are
   precisely `Functor.map_id` and `Functor.map_comp` for `M`. -/
theorem moduleSystemMap_id (M : ModuleSystem R I) (i : I)
    (x : (M.obj i : Type (max v w))) :
    moduleSystemMap M (le_refl i) x = x := by
  sorry

theorem moduleSystemMap_comp (M : ModuleSystem R I) {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) (x : (M.obj i : Type (max v w))) :
    moduleSystemMap M hjk (moduleSystemMap M hij x) =
      moduleSystemMap M (hij.trans hjk) x := by
  sorry

/-- The categorical colimit of a module system. -/
abbrev moduleSystemColimit (M : ModuleSystem R I) : ModuleCat.{max v w} R :=
  colimit M

/- The direct sum of the stages and its canonical inclusions. -/
abbrev moduleColimitDirectSum (M : ModuleSystem R I) :=
  DirectSum I (fun i => (M.obj i : Type (max v w)))

noncomputable def moduleColimitDirectSumInclusion (M : ModuleSystem R I) (i : I) :
    (M.obj i : Type (max v w)) →ₗ[R] moduleColimitDirectSum M := by
  classical
  exact DirectSum.lof R I (fun i => (M.obj i : Type (max v w))) i

/- The relation generators in the source's quotient presentation. -/
def moduleColimitRelationSet (M : ModuleSystem R I) :
    Set (moduleColimitDirectSum M) :=
  {x | ∃ (i j : I) (h : i ≤ j) (m : (M.obj i : Type (max v w))),
    x = moduleColimitDirectSumInclusion M i m -
      moduleColimitDirectSumInclusion M j (moduleSystemMap M h m)}

def moduleColimitRelations (M : ModuleSystem R I) :
    Submodule R (moduleColimitDirectSum M) :=
  Submodule.span R (moduleColimitRelationSet M)

/-- The quotient module in the direct-sum presentation of the colimit. -/
abbrev moduleColimitQuotient (M : ModuleSystem R I) :=
  moduleColimitDirectSum M ⧸ moduleColimitRelations M

/-- The projection from the direct sum to the quotient presentation. -/
def moduleColimitProjection (M : ModuleSystem R I) :
    moduleColimitDirectSum M →ₗ[R] moduleColimitQuotient M :=
  (moduleColimitRelations M).mkQ

/-- The canonical map from a stage into the quotient presentation. -/
def moduleColimitQuotientInclusion (M : ModuleSystem R I) (i : I) :
    (M.obj i : Type (max v w)) →ₗ[R] moduleColimitQuotient M :=
  (moduleColimitProjection M).comp (moduleColimitDirectSumInclusion M i)

/- This is the source's assertion that the relation generators vanish and that
   the maps from stages form a cocone. -/
theorem moduleColimitQuotient_relation_generator_eq_zero
    (M : ModuleSystem R I) {i j : I} (h : i ≤ j)
    (m : (M.obj i : Type (max v w))) :
    moduleColimitProjection M
        (moduleColimitDirectSumInclusion M i m -
          moduleColimitDirectSumInclusion M j (moduleSystemMap M h m)) = 0 := by
  sorry

theorem moduleColimitQuotientInclusion_compatibility
    (M : ModuleSystem R I) {i j : I} (h : i ≤ j) :
    (moduleColimitQuotientInclusion M j).comp (moduleSystemMap M h) =
      moduleColimitQuotientInclusion M i := by
  sorry

/- The quotient maps form the cocone displayed in the source. -/
def moduleColimitQuotientCocone (M : ModuleSystem R I) : Cocone M where
  pt := ModuleCat.of R (moduleColimitQuotient M)
  ι :=
    { app := fun i => ModuleCat.ofHom (moduleColimitQuotientInclusion M i)
      naturality := by
        intro i j h
        ext x
        exact congrArg (fun f => f x)
          (moduleColimitQuotientInclusion_compatibility M h.le) }

/- The direct-sum quotient is canonically the categorical colimit. -/
theorem moduleColimitQuotient_is_colimit_exists
    (M : ModuleSystem R I) :
    Nonempty (IsColimit (moduleColimitQuotientCocone M)) := by
  sorry

noncomputable def moduleColimitQuotient_is_colimit
    (M : ModuleSystem R I) :
    IsColimit (moduleColimitQuotientCocone M) :=
  (moduleColimitQuotient_is_colimit_exists M).some

/-! ## Directed colimits -/

instance moduleSystemDirectedSystem (M : ModuleSystem R I) :
    DirectedSystem (fun i => (M.obj i : Type (max v w)))
      (fun _i _j h => moduleSystemMap M h) where
  map_self := by
    intro i x
    exact moduleSystemMap_id M i x
  map_map := by
    intro i j k hij hjk x
    exact moduleSystemMap_comp M hij hjk x

/-- The directed colimit as Mathlib's direct-sum quotient. -/
abbrev directedModuleColimit (M : ModuleSystem R I)
    (_hI : IsDirectedSet I) : Type (max v w) :=
  moduleColimitQuotient M

/-- The same directed colimit presented as the quotient of the disjoint union. -/
noncomputable abbrev directedModuleColimitDisjointUnion (M : ModuleSystem R I)
    (hI : IsDirectedSet I) : Type (max v w) := by
  classical
  letI : IsDirectedOrder I := hI.2
  exact _root_.DirectLimit
    (fun i => (M.obj i : Type (max v w)))
    (fun i j h => moduleSystemMap M h)

/- The canonical linear map from a stage to the disjoint-union presentation. -/
noncomputable def directedModuleColimitDisjointUnionMap (M : ModuleSystem R I)
    (hI : IsDirectedSet I) (i : I) :
    letI : IsDirectedOrder I := hI.2
    letI : Nonempty I := hI.1
    (M.obj i : Type (max v w)) →ₗ[R] directedModuleColimitDisjointUnion M hI := by
  classical
  letI : IsDirectedOrder I := hI.2
  letI : Nonempty I := hI.1
  exact _root_.DirectLimit.Module.of R I
    (fun i => (M.obj i : Type (max v w)))
    (fun _i _j h => moduleSystemMap M h) i

/- The class of an element of a stage in the directed-colimit quotient. -/
noncomputable def directedModuleColimitClass (M : ModuleSystem R I)
    (hI : IsDirectedSet I) (i : I) (x : (M.obj i : Type (max v w))) :
    directedModuleColimit M hI :=
  moduleColimitQuotientInclusion M i x

noncomputable def directedModuleColimitDisjointUnionClass (M : ModuleSystem R I)
    (hI : IsDirectedSet I) (i : I) (x : (M.obj i : Type (max v w))) :
    directedModuleColimitDisjointUnion M hI := by
  exact directedModuleColimitDisjointUnionMap M hI i x

theorem directedModuleColimit_disjointUnion_equiv (M : ModuleSystem R I)
    (hI : IsDirectedSet I) :
    letI : IsDirectedOrder I := hI.2
    letI : Nonempty I := hI.1
    Nonempty
      (directedModuleColimit M hI ≃ₗ[R] directedModuleColimitDisjointUnion M hI) := by
  sorry

theorem directedModuleColimit_eq_iff (M : ModuleSystem R I)
    (hI : IsDirectedSet I) {i j : I}
    (x : (M.obj i : Type (max v w))) (y : (M.obj j : Type (max v w))) :
    directedModuleColimitClass M hI i x = directedModuleColimitClass M hI j y ↔
      ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
        moduleSystemMap M hik x = moduleSystemMap M hjk y := by
  sorry

theorem directedModuleColimit_add (M : ModuleSystem R I)
    (hI : IsDirectedSet I) {i j : I}
    (x : (M.obj i : Type (max v w))) (y : (M.obj j : Type (max v w)))
    (k : I) (hik : i ≤ k) (hjk : j ≤ k) :
    letI : IsDirectedOrder I := hI.2
    letI : Nonempty I := hI.1
    directedModuleColimitClass M hI i x +
        directedModuleColimitClass M hI j y =
      directedModuleColimitClass M hI k
        (moduleSystemMap M hik x + moduleSystemMap M hjk y) := by
  sorry

theorem directedModuleColimit_smul (M : ModuleSystem R I)
    (hI : IsDirectedSet I) {i : I}
    (r : R) (x : (M.obj i : Type (max v w))) :
    letI : IsDirectedOrder I := hI.2
    letI : Nonempty I := hI.1
    r • directedModuleColimitClass M hI i x =
      directedModuleColimitClass M hI i (r • x) := by
  sorry

/-- The canonical maps into the directed-colimit quotient. -/
def directedModuleColimitMap (M : ModuleSystem R I) (hI : IsDirectedSet I) (i : I) :
    (M.obj i : Type (max v w)) →ₗ[R] directedModuleColimit M hI :=
  moduleColimitQuotientInclusion M i

theorem directedModuleColimitMap_apply (M : ModuleSystem R I)
    (hI : IsDirectedSet I) (i : I)
    (x : (M.obj i : Type (max v w))) :
    directedModuleColimitMap M hI i x = directedModuleColimitClass M hI i x := by
  rfl

theorem directedModuleColimitMap_compatibility (M : ModuleSystem R I)
    (hI : IsDirectedSet I) {i j : I} (h : i ≤ j) :
    (directedModuleColimitMap M hI j).comp (moduleSystemMap M h) =
      directedModuleColimitMap M hI i := by
  sorry

/- The canonical quotient maps form the directed colimit cocone. -/
def directedModuleColimitCocone (M : ModuleSystem R I)
    (hI : IsDirectedSet I) : Cocone M where
  pt := ModuleCat.of R (directedModuleColimit M hI)
  ι :=
    { app := fun i => ModuleCat.ofHom (directedModuleColimitMap M hI i)
      naturality := by
        intro i j h
        ext x
        exact congrArg (fun f => f x)
          (directedModuleColimitMap_compatibility M hI h.le) }

/- The directed-colimit quotient is canonically a colimit of the system. -/
theorem directedModuleColimit_is_colimit_exists (M : ModuleSystem R I)
    (hI : IsDirectedSet I) :
    Nonempty (IsColimit (directedModuleColimitCocone M hI)) := by
  sorry

noncomputable def directedModuleColimit_is_colimit (M : ModuleSystem R I)
    (hI : IsDirectedSet I) :
    IsColimit (directedModuleColimitCocone M hI) :=
  (directedModuleColimit_is_colimit_exists M hI).some

/-- The zero criterion for an element in a directed module colimit. -/
theorem moduleSystemColimit_ι_eq_zero_iff
    (M : ModuleSystem R I) (hI : IsDirectedSet I) {i : I}
    (x : (M.obj i : Type (max v w))) :
    (colimit.ι M i) x = 0 ↔
      ∃ (j : I) (hij : i ≤ j), moduleSystemMap M hij x = 0 := by
  sorry

/-! ## The three-object fork example -/

abbrev ThreeForkIndex := WalkingSpan

/-- A system over the fork `a → b`, `a → c`, with arbitrary stage modules and
transition maps. -/
def threeForkSystem {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    ThreeForkIndex ⥤ ModuleCat.{w} R :=
  span uab uac

/-- The map `M_a → M_b ⊕ M_c` given by `μ_ab ⊕ -μ_ac`. -/
def threeForkRelationLinearMap {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    (A : Type w) →ₗ[R] (B × C) where
  toFun x := (uab.hom x, -uac.hom x)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' r x := by simp

def threeForkRelationMap {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    A ⟶ ModuleCat.of R (B × C) :=
  ModuleCat.ofHom (threeForkRelationLinearMap uab uac)

/-- The cokernel presentation of the fork colimit. -/
def threeForkCokernel {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) : ModuleCat.{w} R :=
  cokernel (threeForkRelationMap uab uac)

theorem threeFork_colimit_is_cokernel {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    Nonempty
      (colimit (threeForkSystem uab uac) ≅ threeForkCokernel uab uac) := by
  sorry

/- The following are the two kernel calculations displayed in the source;
   `⊔` is the submodule sum. -/
theorem threeFork_kernel_at_a {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    LinearMap.ker (colimit.ι (threeForkSystem uab uac) .zero).hom =
      LinearMap.ker uab.hom ⊔ LinearMap.ker uac.hom := by
  sorry

theorem threeFork_kernel_at_b {R : Type u} [CommRing R]
    {A B C : ModuleCat.{w} R} (uab : A ⟶ B) (uac : A ⟶ C) :
    LinearMap.ker (colimit.ι (threeForkSystem uab uac) .left).hom =
      Submodule.map uab.hom (LinearMap.ker uac.hom) := by
  sorry

/-! ## Homomorphisms of systems -/

/-- A homomorphism of module systems is the existing natural-transformation
interface between the associated functors. -/
abbrev ModuleSystemHom (M N : ModuleSystem R I) := M ⟶ N

/-- The homomorphism induced on categorical colimits. -/
noncomputable def moduleSystemColimitMap {M N : ModuleSystem R I}
    (Φ : ModuleSystemHom M N) : moduleSystemColimit M ⟶ moduleSystemColimit N :=
  colim.map Φ

theorem moduleSystemColimitMap_ι {M N : ModuleSystem R I}
    (Φ : ModuleSystemHom M N) (i : I) :
    colimit.ι M i ≫ moduleSystemColimitMap Φ =
      Φ.app i ≫ colimit.ι N i := by
  exact colimit.ι_map Φ i

theorem moduleSystemColimitMap_unique {M N : ModuleSystem R I}
    (Φ : ModuleSystemHom M N) (g : moduleSystemColimit M ⟶ moduleSystemColimit N)
    (hg : ∀ i : I, colimit.ι M i ≫ g = Φ.app i ≫ colimit.ι N i) :
    g = moduleSystemColimitMap Φ := by
  sorry

/-! A concrete instance of the fork illustrates why the zero criterion needs
directedness. -/

abbrev integerZeroModule : ModuleCat ℤ := ModuleCat.of ℤ (Fin 0 → ℤ)

def nonDirectedSourceSystem : ThreeForkIndex ⥤ ModuleCat ℤ :=
  threeForkSystem
    (0 : integerZeroModule ⟶ ModuleCat.of ℤ ℤ)
    (0 : integerZeroModule ⟶ ModuleCat.of ℤ ℤ)

def nonDirectedTargetSystem : ThreeForkIndex ⥤ ModuleCat ℤ :=
  threeForkSystem (𝟙 (ModuleCat.of ℤ ℤ)) (𝟙 (ModuleCat.of ℤ ℤ))

def nonDirectedSystemMap :
    nonDirectedSourceSystem ⟶ nonDirectedTargetSystem :=
  spanHomMk (0 : integerZeroModule ⟶ ModuleCat.of ℤ ℤ)
    (𝟙 (ModuleCat.of ℤ ℤ)) (𝟙 (ModuleCat.of ℤ ℤ))

theorem nonDirectedSystemMap_stagewise_injective :
    ∀ i : ThreeForkIndex,
      Function.Injective ((nonDirectedSystemMap.app i).hom) := by
  sorry

theorem nonDirected_colimit_map_not_injective :
    ¬ Function.Injective ((colim.map nonDirectedSystemMap).hom) := by
  sorry

/-! ## Exactness of directed colimits -/

/-- The system of short complexes associated to levelwise maps of systems. -/
def moduleSystemShortComplex {R : Type u} [CommRing R]
    {I : Type v} [Preorder I]
    {L M N : ModuleSystem R I} (φ : L ⟶ M) (ψ : M ⟶ N)
    (hcomplex : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    I ⥤ ShortComplex (ModuleCat.{max v w} R) where
  obj i := ShortComplex.mk (φ.app i) (ψ.app i) (hcomplex i)
  map {i j} h :=
    ShortComplex.homMk (L.map h) (M.map h) (N.map h)
      (φ.naturality h) (ψ.naturality h)
  map_id := by
    intro i
    apply ShortComplex.hom_ext <;> simp
  map_comp := by
    intro i j k hij hjk
    apply ShortComplex.hom_ext <;> simp

/-! The homology modules form the induced system of homology objects. -/
noncomputable def moduleSystemHomologySystem {R : Type u} [CommRing R]
    {I : Type v} [Preorder I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v w} R)) :
    I ⥤ ModuleCat.{max v w} R :=
  S ⋙ ShortComplex.homologyFunctor (ModuleCat.{max v w} R)

/- The first and second maps of a system of short complexes. -/
def moduleShortComplexFirstMap {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    (S ⋙ ShortComplex.π₁) ⟶ (S ⋙ ShortComplex.π₂) where
  app i := (S.obj i).f
  naturality _i _j f := (S.map f).comm₁₂

def moduleShortComplexSecondMap {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    (S ⋙ ShortComplex.π₂) ⟶ (S ⋙ ShortComplex.π₃) where
  app i := (S.obj i).g
  naturality _i _j f := (S.map f).comm₂₃

/-- The sequence obtained by taking colimits of a system of short complexes is
a complex. -/
theorem moduleShortComplexColimit_is_complex {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    colim.map (moduleShortComplexFirstMap S) ≫
        colim.map (moduleShortComplexSecondMap S) = 0 := by
  sorry

/-- The colimit short complex associated to a system of short complexes. -/
noncomputable def moduleShortComplexColimit {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    ShortComplex (ModuleCat.{max v v' w} R) :=
  ShortComplex.mk (colim.map (moduleShortComplexFirstMap S))
    (colim.map (moduleShortComplexSecondMap S))
    (moduleShortComplexColimit_is_complex S)

theorem directed_colimit_homology {R : Type u} [CommRing R]
    {I : Type v} [Preorder I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v w} R)) (hI : IsDirectedSet I) :
    Nonempty
      ((moduleShortComplexColimit S).homology ≅
        colimit (moduleSystemHomologySystem S)) := by
  sorry

theorem directed_colimit_exact {R : Type u} [CommRing R]
    {I : Type v} [Preorder I]
    {L M N : ModuleSystem R I} (φ : L ⟶ M) (ψ : M ⟶ N)
    (hcomplex : ∀ i : I, φ.app i ≫ ψ.app i = 0)
    (hI : IsDirectedSet I) :
    Nonempty
      ((moduleShortComplexColimit (moduleSystemShortComplex φ ψ hcomplex)).homology ≅
        colimit (moduleSystemHomologySystem
          (moduleSystemShortComplex φ ψ hcomplex))) := by
  exact directed_colimit_homology (moduleSystemShortComplex φ ψ hcomplex) hI

theorem directed_colimit_exact_of_exact {R : Type u} [CommRing R]
    {I : Type v} [Preorder I]
    (S : I ⥤ ShortComplex (ModuleCat.{max v w} R)) (hI : IsDirectedSet I)
    (hS : ∀ i : I, (S.obj i).Exact) :
    (moduleShortComplexColimit S).Exact := by
  sorry

/-! ## Coproducts and the almost-directed statement -/

def discreteShortComplexSystem {R : Type u} [CommRing R]
    {J : Type v} (S : J → ShortComplex (ModuleCat.{max v w} R)) :
    Discrete J ⥤ ShortComplex (ModuleCat.{max v w} R) :=
  Discrete.functor S

/-- The categorical direct-sum sequence attached to a family of short
complexes. -/
abbrev directSumShortComplex {R : Type u} [CommRing R]
    {J : Type v} (S : J → ShortComplex (ModuleCat.{max v w} R)) :=
  moduleShortComplexColimit (discreteShortComplexSystem S)

theorem direct_sum_of_exact_short_complexes {R : Type u} [CommRing R]
    {J : Type v} (S : J → ShortComplex (ModuleCat.{max v w} R))
    (hS : ∀ j : J, (S j).Exact) :
    (directSumShortComplex S).Exact := by
  sorry

theorem almost_directed_colimit_homology {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (hspan : Formalization.Books.Categories.Unit19.HasCoconesForSpans I)
    (heq : Formalization.Books.Categories.Unit19.HasParallelEqualizers I)
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R)) :
    Nonempty
      ((moduleShortComplexColimit S).homology ≅
        colimit (S ⋙ ShortComplex.homologyFunctor
          (ModuleCat.{max v v' w} R))) := by
  sorry

theorem almost_directed_colimit_exact {R : Type u} [CommRing R]
    {I : Type v} [Category.{v'} I]
    (hspan : Formalization.Books.Categories.Unit19.HasCoconesForSpans I)
    (heq : Formalization.Books.Categories.Unit19.HasParallelEqualizers I)
    (S : I ⥤ ShortComplex (ModuleCat.{max v v' w} R))
    (hS : ∀ i : I, (S.obj i).Exact) :
    (moduleShortComplexColimit S).Exact := by
  sorry

end

end Formalization.Books.Algebra.Unit08
