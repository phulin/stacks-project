import Formalization.Books.EtaleCohomology.Unit09.Presheaves
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.Sheaves.Sheaf

/-!
# Étale Cohomology, Chapter 11: Sheaves

This file formalizes the source section `Sheaves` in
`books/etale-cohomology.tex`, lines 577--634.  The source's equalizer
condition is represented by Mathlib's canonical sheaf condition and its
equivalent limit and multifork formulations.  This keeps the indexed-family
notation of the book connected to the sieve-based site API used by Mathlib.
-/

namespace Formalization.Books.EtaleCohomology.Unit11

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w z

/-! ## Presheaves, separated presheaves, and sheaves -/

/-- A set-valued presheaf on `C`, reusing Chapter 9's canonical interface. -/
abbrev SetPresheaf (C : Type u) [Category.{v} C] :=
  Formalization.Books.EtaleCohomology.Unit09.Presheaf C

/-- An abelian presheaf on `C`, namely a presheaf valued in abelian groups. -/
abbrev AbelianPresheaf (C : Type u) [Category.{v} C] :=
  Formalization.Books.EtaleCohomology.Unit09.AbelianPresheaf C

/-- The category `PSh(C)` of set-valued presheaves. -/
abbrev PSh (C : Type u) [Category.{v} C] :=
  Formalization.Books.EtaleCohomology.Unit09.PSh C

/-- The category `PAb(C)` of abelian presheaves. -/
abbrev PAb (C : Type u) [Category.{v} C] :=
  Formalization.Books.EtaleCohomology.Unit09.PAb C

/-- A separated set-valued presheaf, in the terminology of the source. -/
abbrev SeparatedPresheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (F : SetPresheaf C) : Prop :=
  CategoryTheory.Presieve.IsSeparated J F

/-- A separated abelian presheaf, in the terminology of the source. -/
abbrev SeparatedAbelianPresheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (F : AbelianPresheaf C) : Prop :=
  CategoryTheory.Presheaf.IsSeparated J F

/-- The canonical sheaf condition for a presheaf valued in a category. -/
abbrev IsSheaf {C : Type u} [Category.{v} C]
    {A : Type w} [Category.{z} A] (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ A) : Prop :=
  CategoryTheory.Presheaf.IsSheaf J F

/-- A sheaf of sets on the site `(C, J)`. -/
abbrev SetSheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (F : SetPresheaf C) : Prop :=
  IsSheaf J F

/-- An abelian sheaf on the site `(C, J)`. -/
abbrev AbelianSheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (F : AbelianPresheaf C) : Prop :=
  IsSheaf J F

/-! ## The equalizer diagram and its canonical limit forms -/

/-- The sheaf condition for one covering sieve.

The cone over `S.arrows` is Mathlib's canonical sieve form of the displayed
equalizer condition: its cone point is the sections over the target, its legs
are restrictions along arrows in the sieve, and its morphisms encode the
compatibility relations among those restrictions. -/
def CoveringSieveSheafCondition {C : Type u} [Category.{v} C]
    {A : Type w} [Category.{z} A] (F : Cᵒᵖ ⥤ A)
    {X : C} (S : Sieve X) : Prop :=
  Nonempty (IsLimit (F.mapCone S.arrows.cocone.op))

/-- The source's sheaf axiom is equivalent to the limit condition for every
covering sieve. -/
theorem isSheaf_iff_coveringSieveSheafCondition
    {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A]
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ A) :
    IsSheaf J F ↔
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
        CoveringSieveSheafCondition F S := by
  simpa only [IsSheaf, CoveringSieveSheafCondition] using
    (CategoryTheory.Presheaf.isSheaf_iff_isLimit (J := J) (P := F))

/-- The source's indexed covering-family form is represented here by
Mathlib's multifork condition for a covering sieve. -/
def CoveringSieveMultiforkSheafCondition {C : Type u} [Category.{v} C]
    {A : Type w} [Category.{z} A] (F : Cᵒᵖ ⥤ A)
    {J : GrothendieckTopology C} {X : C} (S : J.Cover X) : Prop :=
  Nonempty (IsLimit (S.multifork F))

/-- A presheaf is a sheaf exactly when every covering-sieve multifork is a
limit.  This is Mathlib's sieve-indexed form of the source's equalizer
condition. -/
theorem isSheaf_iff_coveringSieveMultiforkSheafCondition
    {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A]
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ A) :
    IsSheaf J F ↔
      ∀ (X : C) (S : J.Cover X), CoveringSieveMultiforkSheafCondition F S := by
  simpa only [IsSheaf, CoveringSieveMultiforkSheafCondition] using
    (CategoryTheory.Presheaf.isSheaf_iff_multifork (J := J) (P := F))

/-! ## Empty coverings -/

/-- If the empty sieve covers `X`, sections of a sheaf over `X` are terminal.
This is the categorical form of the source's empty-product remark. -/
noncomputable def emptyCover_sections_isTerminal
    {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A]
    {J : GrothendieckTopology C} (F : Sheaf J A) (X : C)
    (hX : (⊥ : Sieve X) ∈ J X) : IsTerminal (F.1.obj (op X)) :=
  F.isTerminalOfBotCover X hX

/-- For set-valued sheaves, the terminal sections over an empty-covered object
form a singleton type, as asserted in the source. -/
theorem emptyCover_set_sections_unique
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : Sheaf J (Type v)) (X : C)
    (hX : (⊥ : Sieve X) ∈ J X) :
    Nonempty (F.1.obj (op X)) ∧ Subsingleton (F.1.obj (op X)) := by
  let : Unique (F.1.obj (op X)) :=
    (CategoryTheory.Limits.Types.isTerminalEquivUnique _).toFun
      (emptyCover_sections_isTerminal F X hX)
  exact ⟨⟨default⟩, inferInstance⟩

/-! ## Categories of sheaves -/

/-- The category `Sh(C)` of sheaves of sets on `(C, J)`. -/
abbrev Sh {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) := Sheaf J (Type v)

/-- The category `Ab(C)` of abelian sheaves on `(C, J)`. -/
abbrev Ab {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) := Sheaf J AddCommGrpCat.{v}

/-! ## The topological-space example -/

/-- The site of open subsets of a topological space, with its canonical
Grothendieck topology. -/
abbrev TopologicalSite (X : Type u) [TopologicalSpace X] :=
  Opens.grothendieckTopology (TopCat.of X)

/-- The usual category of sheaves of sets on a topological space. -/
abbrev TopologicalSh (X : Type u) [TopologicalSpace X] :=
  Sheaf (TopologicalSite X) (Type u)

/-- The usual category of abelian sheaves on a topological space. -/
abbrev TopologicalAb (X : Type u) [TopologicalSpace X] :=
  Sheaf (TopologicalSite X) AddCommGrpCat.{u}

end Formalization.Books.EtaleCohomology.Unit11
