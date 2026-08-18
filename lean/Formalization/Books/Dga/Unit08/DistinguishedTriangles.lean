import Formalization.Books.Dga.Unit07.AdmissibleShortExactSequences

/-!
# Differential Graded Algebra, Chapter 8: Distinguished triangles

This file records the triangle attached to an admissible short exact
sequence.  The connecting map is represented by the splitting-dependent
data from Chapter 7, while the independence theorem records that changing
those choices only changes the triangle up to isomorphism in the homotopy
category.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit04
open Formalization.Books.Dga.Unit05
open Formalization.Books.Dga.Unit07

universe u

namespace Formalization.Books.Dga.Unit08

/-! ## Triangles in the homotopy category

Mathlib's `Pretriangulated.Triangle` requires a `HasShift` instance on the
ambient category.  The preceding DGA chapters provide the shift functor on
differential graded modules, but not the induced coherent shift structure on
the quotient category, so this source-facing structure records the same data
without introducing a second shift infrastructure.
-/

/-- The quotient category `K(Mod_(A,d))` used by the source. -/
abbrev DgmHomotopyCategory {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :=
  DifferentialGradedModuleHomotopyCategory A

/-- The quotient functor from differential graded modules to the homotopy
category. -/
abbrev DgmHomotopyQuotient {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    DifferentialGradedModuleCategory A ⥤ DgmHomotopyCategory A :=
  differentialGradedModuleHomotopyQuotient A

/-- A triangle `K ⟶ L ⟶ M ⟶ K[1]` in the DGA homotopy category. -/
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

/-- A triangle isomorphism, expressed using differential graded
  representatives of its three component homotopy equivalences in the
  homotopy category.  The commutativity equations live in the quotient
  category, as they do in the source. -/
structure DgmTriangleIsomorphism {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (T U : DgmTriangle (A := A)) where
  e₁ : DifferentialGradedModuleHom T.obj₁ U.obj₁
  e₂ : DifferentialGradedModuleHom T.obj₂ U.obj₂
  e₃ : DifferentialGradedModuleHom T.obj₃ U.obj₃
  e₁_iso : Formalization.Books.Dga.Unit07.DgmHomotopyEquivalence e₁
  e₂_iso : Formalization.Books.Dga.Unit07.DgmHomotopyEquivalence e₂
  e₃_iso : Formalization.Books.Dga.Unit07.DgmHomotopyEquivalence e₃
  comm₁ : T.mor₁ ≫ (DgmHomotopyQuotient A).map e₂ =
    (DgmHomotopyQuotient A).map e₁ ≫ U.mor₁
  comm₂ : T.mor₂ ≫ (DgmHomotopyQuotient A).map e₃ =
    (DgmHomotopyQuotient A).map e₂ ≫ U.mor₂
  comm₃ : T.mor₃ ≫
      (DgmHomotopyQuotient A).map (dgmShiftMap e₁ (1 : ℤ)) =
    (DgmHomotopyQuotient A).map e₃ ≫ U.mor₃

/-- Two source-facing triangles are isomorphic when their displayed
component maps give an isomorphism after passage to the homotopy category.
The quotient-level isomorphism is represented by differential graded module
maps, using the homotopy-equivalence interface from Chapter 7. -/
def DgmTriangleIsomorphic
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (T U : DgmTriangle (A := A)) : Prop :=
  Nonempty (DgmTriangleIsomorphism T U)

/-! ## The connecting map and associated triangle -/

/-- All data needed to choose the connecting morphism supplied by the
admissible-short-exact-sequence lemma.  The two graded maps are splittings;
the kernel-image equality is the exactness condition used by the Chapter 7
connecting-map interface. -/
structure DgmAdmissibleConnectingData {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S) where
  splitting : DgmGradedSplitting S
  kernel_eq_image : DgmGradedKernelEqImage
    splitting.sectionMap splitting.retraction
  connecting : DgmConnectingMapData hS
    splitting.sectionMap splitting.retraction

/-- The connecting-map data exists for every admissible short exact
sequence. -/
theorem dgmAdmissibleConnectingData_exists
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S) :
    Nonempty (DgmAdmissibleConnectingData hS) := by
  sorry

/-- A chosen connecting-map datum for an admissible short exact sequence. -/
noncomputable def dgmAdmissibleConnectingData
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S) :
    DgmAdmissibleConnectingData hS :=
  Classical.choice (dgmAdmissibleConnectingData_exists hS)

/-- The triangle associated to a chosen splitting and its connecting map. -/
noncomputable def dgmAssociatedTriangleWithData
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S)
    (c : DgmAdmissibleConnectingData hS) : DgmTriangle (A := A) where
  obj₁ := S.X₁
  obj₂ := S.X₂
  obj₃ := S.X₃
  mor₁ := (DgmHomotopyQuotient A).map S.f
  mor₂ := (DgmHomotopyQuotient A).map S.g
  mor₃ := (DgmHomotopyQuotient A).map c.connecting.map

/-- The triangle associated to an admissible short exact sequence, using a
chosen connecting-map datum. -/
noncomputable def dgmAssociatedTriangle
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S) : DgmTriangle (A := A) :=
  dgmAssociatedTriangleWithData hS (dgmAdmissibleConnectingData hS)

/-- The connecting maps obtained from two choices in the admissible
short-exact-sequence construction are homotopic.  This is the map-level
assertion used to identify the two associated triangles in the homotopy
category. -/
theorem dgmConnectingMap_homotopic_of_choices
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S)
    (c c' : DgmAdmissibleConnectingData hS) :
    DifferentialGradedModuleHomotopic c.connecting.map c'.connecting.map := by
  sorry

/-- Changing the splittings in the connecting-map construction changes the
associated triangle by the canonical isomorphism whose three component maps
are identities on `S.X₁`, `S.X₂`, and `S.X₃`. -/
theorem dgmAssociatedTriangle_independent_of_splittings
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S)
    (c c' : DgmAdmissibleConnectingData hS) :
    ∃ e : DgmTriangleIsomorphism
        (dgmAssociatedTriangleWithData hS c)
        (dgmAssociatedTriangleWithData hS c'),
      e.e₁ = (𝟙 S.X₁ : DifferentialGradedModuleHom S.X₁ S.X₁) ∧
      e.e₂ = (𝟙 S.X₂ : DifferentialGradedModuleHom S.X₂ S.X₂) ∧
      e.e₃ = (𝟙 S.X₃ : DifferentialGradedModuleHom S.X₃ S.X₃) := by
  sorry

/-! ## Distinguished triangles -/

/-- A triangle is distinguished when it is isomorphic in the homotopy
category to one associated to an admissible short exact sequence. -/
def DgmDistinguishedTriangle
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (T : DgmTriangle (A := A)) : Prop :=
  ∃ (S : ShortComplex (DifferentialGradedModuleCategory A))
    (hS : DgmAdmissibleShortExactSequence S),
    DgmTriangleIsomorphic (dgmAssociatedTriangle hS) T

end Formalization.Books.Dga.Unit08
