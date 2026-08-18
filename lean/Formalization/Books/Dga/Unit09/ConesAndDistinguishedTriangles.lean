import Formalization.Books.Dga.Unit06.Cone

/-!
# Differential Graded Algebra, Chapter 9: Cones and distinguished triangles

The preceding DGA chapters provide the differential graded module category,
its homotopy quotient, shifts, and mapping cones.  This file records the
remaining triangle language used by the source section.  In particular, the
homotopy quotient in the DGA development does not yet carry Mathlib's
`Pretriangulated` instance, so the small `DgmTriangle` interface below keeps
the same objects and quotient morphisms while exposing the shifted third map.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit04
open Formalization.Books.Dga.Unit05
open Formalization.Books.Dga.Unit06

universe u

namespace Formalization.Books.Dga.Unit09

/-! ## The homotopy-category triangle interface -/

abbrev DgmHomotopyCategory {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :=
  DifferentialGradedModuleHomotopyCategory A

abbrev DgmHomotopyQuotient {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    DifferentialGradedModuleCategory A ⥤ DgmHomotopyCategory A :=
  differentialGradedModuleHomotopyQuotient A

/-- A triangle in the DGA homotopy category, with its third target made
explicit because the existing DGA shift API is object-level. -/
structure DgmTriangle {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} where
  obj₁ : DifferentialGradedModule A
  obj₂ : DifferentialGradedModule A
  obj₃ : DifferentialGradedModule A
  mor₁ : (DgmHomotopyQuotient A).obj obj₁ ⟶
    (DgmHomotopyQuotient A).obj obj₂
  mor₂ : (DgmHomotopyQuotient A).obj obj₂ ⟶
    (DgmHomotopyQuotient A).obj obj₃
  mor₃ : (DgmHomotopyQuotient A).obj obj₃ ⟶
    (DgmHomotopyQuotient A).obj (dgmShift obj₁ (1 : ℤ))

/-- Homotopy equivalence in the source's sense: an isomorphism after passing
to the homotopy quotient. -/
def DgmHomotopyEquivalence {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom M N) : Prop :=
  IsIso ((DgmHomotopyQuotient A).map f)

/-! ## Graded module splittings -/

/-- A map of graded right `A`-modules, with no compatibility condition on the
differentials.  Its homogeneous components are maps of `R`-modules. -/
structure DgmGradedMap {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M N : DifferentialGradedModule A) where
  hom : ∀ n : ℤ, M.complex.X n ⟶ N.complex.X n
  map_action :
    ∀ (n m : ℤ) (x : M.complex.X n) (a : A.complex.X m),
      (hom (n + m)).hom (M.actionOnHomogeneous n m x a) =
        N.actionOnHomogeneous n m ((hom n).hom x) a

namespace DgmGradedMap

/-- The identity graded module map. -/
def id {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) : DgmGradedMap M M where
  hom := fun _ => 𝟙 _
  map_action := by simp

/-- Composition of graded module maps. -/
def comp {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N P : DifferentialGradedModule A}
    (f : DgmGradedMap M N) (g : DgmGradedMap N P) : DgmGradedMap M P where
  hom := fun n => f.hom n ≫ g.hom n
  map_action := by
    intro n m x a
    change (g.hom (n + m)).hom
        ((f.hom (n + m)).hom (M.actionOnHomogeneous n m x a)) =
      P.actionOnHomogeneous n m
        ((g.hom n).hom ((f.hom n).hom x)) a
    rw [f.map_action, g.map_action]

end DgmGradedMap

/-- A graded splitting of a composable pair `K ⟶ L ⟶ M`. -/
structure DgmGradedSplitting {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L)
    (g : DifferentialGradedModuleHom L M) where
  sectionMap : DgmGradedMap M L
  retraction : DgmGradedMap L K
  section_rightInverse :
    ∀ n : ℤ, sectionMap.hom n ≫ g.underlying.f n = 𝟙 _
  retraction_leftInverse :
    ∀ n : ℤ, f.underlying.f n ≫ retraction.hom n = 𝟙 _

/-- The DGA version of an admissible short exact sequence.  Exactness is the
canonical `ShortComplex.ShortExact` predicate, while admissibility is the
source's splitting condition in graded right `A`-modules. -/
structure DgmAdmissibleShortExact {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (K L M : DifferentialGradedModule A) where
  f : DifferentialGradedModuleHom K L
  g : DifferentialGradedModuleHom L M
  zero : f.underlying ≫ g.underlying = 0
  exact : (ShortComplex.mk f.underlying g.underlying zero).ShortExact
  splitting : Nonempty (DgmGradedSplitting f g)

noncomputable def dgmAdmissibleSplitting
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (S : DgmAdmissibleShortExact K L M) :
    DgmGradedSplitting S.f S.g :=
  Classical.choice S.splitting

/-! ## Connecting maps and associated triangles -/

/-- A witness that the connecting map is induced by the chosen graded
splitting.  The component formula is the source's
`π ∘ d_L ∘ s : M ⟶ K[1]`. -/
structure DgmConnectingWitness
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (S : DgmAdmissibleShortExact K L M) where
  map : DifferentialGradedModuleHom M (dgmShift K (1 : ℤ))
  component_formula :
    ∀ n : ℤ,
      map.underlying.f n =
        (dgmAdmissibleSplitting S).sectionMap.hom n ≫
          L.complex.d n (n + 1) ≫
          (dgmAdmissibleSplitting S).retraction.hom (n + 1)

theorem dgmConnectingWitness_exists
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (S : DgmAdmissibleShortExact K L M) :
    Nonempty (DgmConnectingWitness S) := by
  sorry

/-- The connecting morphism attached to an admissible short exact sequence. -/
noncomputable def dgmConnectingMap
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (S : DgmAdmissibleShortExact K L M) :
    DifferentialGradedModuleHom M (dgmShift K (1 : ℤ)) :=
  (Classical.choice (dgmConnectingWitness_exists S)).map

theorem dgmConnectingMap_component
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (S : DgmAdmissibleShortExact K L M) (n : ℤ) :
    (dgmConnectingMap S).underlying.f n =
      (dgmAdmissibleSplitting S).sectionMap.hom n ≫
        L.complex.d n (n + 1) ≫
        (dgmAdmissibleSplitting S).retraction.hom (n + 1) := by
  exact (Classical.choice (dgmConnectingWitness_exists S)).component_formula n

/-- The triangle associated to an admissible short exact sequence. -/
noncomputable def dgmAssociatedTriangle
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (S : DgmAdmissibleShortExact K L M) : DgmTriangle (A := A) where
  obj₁ := K
  obj₂ := L
  obj₃ := M
  mor₁ := (DgmHomotopyQuotient A).map S.f
  mor₂ := (DgmHomotopyQuotient A).map S.g
  mor₃ := (DgmHomotopyQuotient A).map (dgmConnectingMap S)

/-- The nested shift is canonically isomorphic to the original object.  The
existing DGA shift API is object-level, so this small wrapper records the
corresponding cancellation isomorphism in the DGA module category. -/
theorem dgmShiftCancelIso_exists
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (k : ℤ) :
    Nonempty (dgmShift (dgmShift M k) (-k) ≅ M) := by
  sorry

noncomputable def dgmShiftCancelIso
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) (k : ℤ) :
    dgmShift (dgmShift M k) (-k) ≅ M :=
  Classical.choice (dgmShiftCancelIso_exists M k)

/-- The shifted connecting map `δ[-1]`, with the canonical cancellation of the
double shift on its target. -/
noncomputable def dgmConnectingShiftedMap
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (S : DgmAdmissibleShortExact K L M) :
    DifferentialGradedModuleHom (dgmShift M (-1 : ℤ)) K :=
  dgmShiftMap (dgmConnectingMap S) (-1 : ℤ) ≫
    (dgmShiftCancelIso K (1 : ℤ)).hom

/-! The third map of an inverse-rotated triangle has target the nested shift
of its first object; it is the original map followed by the inverse of the
same canonical cancellation isomorphism. -/
noncomputable def dgmDoubleShiftMap
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {L M : DifferentialGradedModule A}
    (g : DifferentialGradedModuleHom L M) :
    DifferentialGradedModuleHom L
      (dgmShift (dgmShift M (-1 : ℤ)) (1 : ℤ)) :=
  g ≫ (dgmShiftCancelIso M (-1 : ℤ)).inv

/-! ## Cone triangles -/

/-- The cone triangle `K ⟶ L ⟶ C(f) ⟶ K[1]`. -/
noncomputable def dgmConeTriangle
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) : DgmTriangle (A := A) where
  obj₁ := K
  obj₂ := L
  obj₃ := dgmCone f
  mor₁ := (DgmHomotopyQuotient A).map f
  mor₂ := (DgmHomotopyQuotient A).map (dgmConeInclusionHom f)
  mor₃ := (DgmHomotopyQuotient A).map (dgmConeProjectionHom f)

/-- The sign convention used when a cone triangle is viewed as an associated
distinguished triangle. -/
noncomputable def dgmSignedConeTriangle
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) : DgmTriangle (A := A) where
  obj₁ := K
  obj₂ := L
  obj₃ := dgmCone f
  mor₁ := (DgmHomotopyQuotient A).map f
  mor₂ := (DgmHomotopyQuotient A).map (dgmConeInclusionHom f)
  mor₃ := (DgmHomotopyQuotient A).map (-dgmConeProjectionHom f)

/-- The rotated cone triangle `(L, C(f), K[1], i, p, f[1])`. -/
noncomputable def dgmRotatedConeTriangle
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) : DgmTriangle (A := A) where
  obj₁ := L
  obj₂ := dgmCone f
  obj₃ := dgmShift K (1 : ℤ)
  mor₁ := (DgmHomotopyQuotient A).map (dgmConeInclusionHom f)
  mor₂ := (DgmHomotopyQuotient A).map (dgmConeProjectionHom f)
  mor₃ := (DgmHomotopyQuotient A).map (dgmShiftMap f (1 : ℤ))

/-- A cone short exact sequence, including the graded splitting required by
the source's admissibility condition. -/
theorem dgmConeAdmissibleShortExact_exists
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) :
    Nonempty {S : DgmAdmissibleShortExact L (dgmCone f)
        (dgmShift K (1 : ℤ)) //
      S.f = dgmConeInclusionHom f ∧
      S.g = dgmConeProjectionHom f} := by
  sorry

noncomputable def dgmConeAdmissibleShortExact
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) :
    DgmAdmissibleShortExact L (dgmCone f) (dgmShift K (1 : ℤ)) :=
  (Classical.choice (dgmConeAdmissibleShortExact_exists f)).1

/-! ## Isomorphisms of triangles -/

/-- A morphism of cone triangles.  The first square is recorded here in
addition to the two cone squares already supplied by Unit 06. -/
structure DgmConeTriangleMorphism
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule A}
    {f₁ : DifferentialGradedModuleHom K₁ L₁}
    {f₂ : DifferentialGradedModuleHom K₂ L₂}
    {a : DifferentialGradedModuleHom K₁ K₂}
    {b : DifferentialGradedModuleHom L₁ L₂}
    (c : DifferentialGradedModuleHom (dgmCone f₁) (dgmCone f₂)) where
  coneSquares :
    Formalization.Books.Dga.Unit06.DgmConeTriangleMorphism
      (a := a) (b := b) c
  comm_first :
    (DgmHomotopyQuotient A).map f₁ ≫
        (DgmHomotopyQuotient A).map b =
      (DgmHomotopyQuotient A).map a ≫
        (DgmHomotopyQuotient A).map f₂

/-- A triangle isomorphism with chosen differential graded representatives of
its three components. -/
structure DgmTriangleIsomorphism
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (T U : DgmTriangle (A := A)) where
  e₁ : DifferentialGradedModuleHom T.obj₁ U.obj₁
  e₂ : DifferentialGradedModuleHom T.obj₂ U.obj₂
  e₃ : DifferentialGradedModuleHom T.obj₃ U.obj₃
  e₁_iso : DgmHomotopyEquivalence e₁
  e₂_iso : DgmHomotopyEquivalence e₂
  e₃_iso : DgmHomotopyEquivalence e₃
  comm₁ : T.mor₁ ≫ (DgmHomotopyQuotient A).map e₂ =
    (DgmHomotopyQuotient A).map e₁ ≫ U.mor₁
  comm₂ : T.mor₂ ≫ (DgmHomotopyQuotient A).map e₃ =
    (DgmHomotopyQuotient A).map e₂ ≫ U.mor₂
  comm₃ : T.mor₃ ≫ (DgmHomotopyQuotient A).map (dgmShiftMap e₁ (1 : ℤ)) =
    (DgmHomotopyQuotient A).map e₃ ≫ U.mor₃

/-- A triangle is distinguished when it is isomorphic to one associated to an
admissible short exact sequence. -/
def DgmDistinguishedTriangle
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (T : DgmTriangle (A := A)) : Prop :=
  ∃ (K L M : DifferentialGradedModule A)
    (S : DgmAdmissibleShortExact K L M),
    Nonempty (DgmTriangleIsomorphism (dgmAssociatedTriangle S) T)

/-! ## Source lemmas -/

/-- The rotated cone is the triangle associated to its canonical admissible
short exact sequence. -/
theorem dgm_rotate_cone
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) :
    dgmAssociatedTriangle (dgmConeAdmissibleShortExact f) =
      dgmRotatedConeTriangle f := by
  sorry

/-- Rotating a triangle associated to an admissible short exact sequence gives
the cone triangle of the shifted connecting map. -/
theorem dgm_rotate_triangle
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (S : DgmAdmissibleShortExact K L M) :
    Nonempty (DgmTriangleIsomorphism
      (DgmTriangle.mk (A := A)
        (obj₁ := dgmShift M (-1 : ℤ)) (obj₂ := K) (obj₃ := L)
        (mor₁ := (DgmHomotopyQuotient A).map (dgmConnectingShiftedMap S))
        (mor₂ := (DgmHomotopyQuotient A).map S.f)
        (mor₃ := (DgmHomotopyQuotient A).map (dgmDoubleShiftMap S.g)))
      (dgmConeTriangle (dgmConnectingShiftedMap S))) := by
  sorry

/-- In a morphism of cone triangles, homotopy equivalences on the first two
objects force a homotopy equivalence on the cone. -/
theorem dgm_third_isomorphism
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule A}
    {f₁ : DifferentialGradedModuleHom K₁ L₁}
    {f₂ : DifferentialGradedModuleHom K₂ L₂}
    {a : DifferentialGradedModuleHom K₁ K₂}
    {b : DifferentialGradedModuleHom L₁ L₂}
    (c : DifferentialGradedModuleHom (dgmCone f₁) (dgmCone f₂))
    (h : DgmConeTriangleMorphism (a := a) (b := b) c)
    (ha : DgmHomotopyEquivalence a)
    (hb : DgmHomotopyEquivalence b) :
    DgmHomotopyEquivalence c := by
  sorry

/-- Cones and triangles associated to admissible short exact sequences agree
up to isomorphism, with the source's sign convention. -/
theorem dgm_same_up_to_isomorphisms
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L M : DifferentialGradedModule A}
    (S : DgmAdmissibleShortExact K L M) :
    ∃ u : DifferentialGradedModuleHom (dgmCone S.f) M,
      ∃ e : DgmTriangleIsomorphism
        (dgmSignedConeTriangle S.f) (dgmAssociatedTriangle S),
        e.e₁ = (𝟙 K : DifferentialGradedModuleHom K K) ∧
          e.e₂ = (𝟙 L : DifferentialGradedModuleHom L L) ∧ e.e₃ = u := by
  sorry

/-- Every cone triangle is isomorphic to a triangle associated to an
admissible short exact sequence. -/
theorem dgm_same_up_to_isomorphisms_of_map
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) :
    ∃ (M N : DifferentialGradedModule A)
      (S : DgmAdmissibleShortExact K M N),
    ∃ e : DgmTriangleIsomorphism
        (dgmAssociatedTriangle S) (dgmSignedConeTriangle f),
        e.e₁ = (𝟙 K : DifferentialGradedModuleHom K K) := by
  sorry

theorem dgm_signedConeTriangle_distinguished
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) :
    DgmDistinguishedTriangle (dgmSignedConeTriangle f) := by
  obtain ⟨M, N, S, e, _⟩ := dgm_same_up_to_isomorphisms_of_map f
  exact ⟨K, M, N, S, ⟨e⟩⟩

end Formalization.Books.Dga.Unit09
