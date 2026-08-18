import Formalization.Books.Dga.Unit05.HomotopyCategory
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Differential Graded Algebra, Chapter 6: Cones

The underlying cone is Mathlib's canonical mapping cone.  The additional
module action is packaged through an existence interface: its construction is
the diagonal action on `L ⊕ K[1]`, while the proposition proofs that it obeys
the module-object laws are deferred to the proving stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit04
open Formalization.Books.Dga.Unit05

universe u

namespace Formalization.Books.Dga.Unit06

/-! ## The cone -/

/-- The underlying cochain complex of the cone.  Mathlib's mapping-cone
construction has components `Lⁿ ⊞ Kⁿ⁺¹` and differential matrix
`[[dL, f], [0, -dK]]`; this definition supplies the source's grading and
differential by reuse of that canonical construction. -/
noncomputable abbrev dgmConeComplex
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) : CochainComplexOver R :=
  CochainComplex.mappingCone f.underlying

theorem dgmConeComplex_component_iso_exists
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) (n : ℤ) :
    Nonempty ((dgmConeComplex f).X n ≅
      (L.complex.X n ⊞ K.complex.X (n + 1))) := by
  sorry

/-- The source's degree-`n` identification `C(f)ⁿ = Lⁿ ⊕ Kⁿ⁺¹`. -/
noncomputable def dgmConeComplexComponentIso
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) (n : ℤ) :
    (dgmConeComplex f).X n ≅ (L.complex.X n ⊞ K.complex.X (n + 1)) :=
  Classical.choice (dgmConeComplex_component_iso_exists f n)

/-- The action and module-object laws for a cone. -/
structure DgmConeActionData
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) where
  action : tensorProductComplex R (dgmConeComplex f) A.complex ⟶
    dgmConeComplex f
  one_action :
    tensorHomComplex (𝟙 dgmConeComplex f) A.unit ≫ action =
      (HomologicalComplex.rightUnitor (dgmConeComplex f)).hom
  assoc_action :
    tensorHomComplex action (𝟙 A.complex) ≫ action =
      (HomologicalComplex.associator (dgmConeComplex f) A.complex A.complex).hom ≫
        tensorHomComplex (𝟙 dgmConeComplex f) A.multiplication ≫ action

/-- The diagonal action on the mapping cone exists and satisfies the module
object laws. -/
theorem dgmConeActionData_exists
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) :
    Nonempty (DgmConeActionData f) := by
  sorry

/-- A chosen action datum for the cone. -/
noncomputable def dgmConeActionData
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) : DgmConeActionData f :=
  Classical.choice (dgmConeActionData_exists f)

/-- The action on the mapping cone. -/
noncomputable abbrev dgmConeAction
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) :
    tensorProductComplex R (dgmConeComplex f) A.complex ⟶ dgmConeComplex f :=
  (dgmConeActionData f).action

/-- The differential graded module cone of a morphism. -/
noncomputable def dgmCone
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) : DifferentialGradedModule A where
  complex := dgmConeComplex f
  action := (dgmConeActionData f).action
  one_action := (dgmConeActionData f).one_action
  assoc_action := (dgmConeActionData f).assoc_action

/-! The component and differential formulas are the defining equations of
`CochainComplex.mappingCone`; no parallel local cone complex is introduced. -/

/-- The canonical inclusion of the target into the cone, on underlying
cochain complexes. -/
noncomputable def dgmConeInclusion
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) :
    L.complex ⟶ (dgmCone f).complex :=
  CochainComplex.mappingCone.inr f.underlying

/-- The canonical projection from the cone to the shifted source, on
underlying cochain complexes. -/
noncomputable def dgmConeProjection
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) :
    (dgmCone f).complex ⟶ (dgmShift K (1 : ℤ)).complex :=
  (CochainComplex.mappingCone.triangle f.underlying).mor₃

/-- The canonical inclusion as a differential graded module morphism. -/
noncomputable def dgmConeInclusionHom
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) :
    DifferentialGradedModuleHom L (dgmCone f) :=
  ⟨dgmConeInclusion f, by sorry⟩

/-- The canonical projection as a differential graded module morphism. -/
noncomputable def dgmConeProjectionHom
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) :
    DifferentialGradedModuleHom (dgmCone f) (dgmShift K (1 : ℤ)) :=
  ⟨dgmConeProjection f, by sorry⟩

/-- The source's cone triangle data. -/
structure DgmConeTriangleData
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) where
  inclusion : DifferentialGradedModuleHom L (dgmCone f)
  projection : DifferentialGradedModuleHom (dgmCone f) (dgmShift K (1 : ℤ))
  inclusion_eq : inclusion.underlying = dgmConeInclusion f
  projection_eq : projection.underlying = dgmConeProjection f

/-- The canonical cone triangle data. -/
noncomputable def dgmConeTriangleData
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L) : DgmConeTriangleData f where
  inclusion := dgmConeInclusionHom f
  projection := dgmConeProjectionHom f
  inclusion_eq := rfl
  projection_eq := rfl

/-! ## Functoriality -/

/-- The cone map associated to a chosen compatible homotopy. -/
noncomputable def dgmConeMapOfHomotopy
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule A}
    {f₁ : DifferentialGradedModuleHom K₁ L₁}
    {f₂ : DifferentialGradedModuleHom K₂ L₂}
    {a : DifferentialGradedModuleHom K₁ K₂}
    {b : DifferentialGradedModuleHom L₁ L₂}
    (H : Homotopy (f₁.underlying ≫ b.underlying)
      (a.underlying ≫ f₂.underlying)) :
    DifferentialGradedModuleHom (dgmCone f₁) (dgmCone f₂) :=
  ⟨CochainComplex.mappingCone.mapOfHomotopy H, by sorry⟩

/-- A morphism of cone triangles in the differential graded module homotopy
category. -/
structure DgmConeTriangleMorphism
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule A}
    {f₁ : DifferentialGradedModuleHom K₁ L₁}
    {f₂ : DifferentialGradedModuleHom K₂ L₂}
    {a : DifferentialGradedModuleHom K₁ K₂}
    {b : DifferentialGradedModuleHom L₁ L₂}
    (c : DifferentialGradedModuleHom (dgmCone f₁) (dgmCone f₂)) where
  comm_inclusion :
    (differentialGradedModuleHomotopyQuotient A).map
          (dgmConeInclusionHom f₁) ≫
        (differentialGradedModuleHomotopyQuotient A).map c =
      (differentialGradedModuleHomotopyQuotient A).map b ≫
        (differentialGradedModuleHomotopyQuotient A).map
          (dgmConeInclusionHom f₂)
  comm_projection :
    (differentialGradedModuleHomotopyQuotient A).map c ≫
        (differentialGradedModuleHomotopyQuotient A).map
          (dgmConeProjectionHom f₂) =
      (differentialGradedModuleHomotopyQuotient A).map
          (dgmConeProjectionHom f₁) ≫
        (differentialGradedModuleHomotopyQuotient A).map
          (dgmShiftMap a (1 : ℤ))

/-- Functoriality of the cone triangle for a square commuting up to homotopy.
The source's displayed target has a typographical repetition of `K₁,L₁`; this
declaration uses the mathematically required `K₂,L₂`. -/
theorem dgmCone_functorial
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule A}
    {f₁ : DifferentialGradedModuleHom K₁ L₁}
    {f₂ : DifferentialGradedModuleHom K₂ L₂}
    {a : DifferentialGradedModuleHom K₁ K₂}
    {b : DifferentialGradedModuleHom L₁ L₂}
    (hcomm : DifferentialGradedModuleHomotopic
      (differentialGradedModuleHomComp a f₂)
      (differentialGradedModuleHomComp f₁ b)) :
    ∃ c : DifferentialGradedModuleHom (dgmCone f₁) (dgmCone f₂),
      DgmConeTriangleMorphism (a := a) (b := b) c := by
  sorry

end Formalization.Books.Dga.Unit06
