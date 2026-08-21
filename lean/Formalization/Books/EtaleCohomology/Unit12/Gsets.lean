import Formalization.Books.EtaleCohomology.Unit11.Sheaves
import Formalization.Books.Sites.Unit06.Sites
import Formalization.Books.Sites.Unit09.GSets
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Étale Cohomology, Chapter 12: The example of G-sets

This file formalizes the section `The example of G-sets` in
`books/etale-cohomology.tex`.  Mathlib's `Action (Type u) G` and the
jointly-surjective pretopology are the canonical implementations of the
category and site in the source.  The declarations below keep the source's
indexed-family, orbit, and fixed-point formulations visible at the chapter
boundary.
-/

namespace Formalization.Books.EtaleCohomology.Unit12

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presieve Opposite
open Formalization.Books.EtaleCohomology.Unit09
open Formalization.Books.EtaleCohomology.Unit11

universe u v w

variable {G : Type u} [Group G]

/-! ## The site of G-sets -/

/- The underlying category is Mathlib's canonical category of actions. -/
abbrev GSet (G : Type u) [Monoid G] := Action (Type u) G

/- The jointly-surjective pretopology is already the canonical site API. -/
abbrev GSetPretopology (G : Type u) [Group G] :
    Formalization.Books.Sites.Unit06.Site (GSet G) :=
  Formalization.Books.Sites.Unit06.groupActionSite G

/-- The Grothendieck topology of jointly-surjective coverings of `G`-sets. -/
abbrev GSetSite (G : Type u) [Group G] :
    GrothendieckTopology (GSet G) :=
  (GSetPretopology G).toGrothendieck

/-- An indexed family of equivariant maps with fixed target. -/
structure GSetFamily (U : GSet G) where
  index : Type u
  source : index → GSet G
  hom : ∀ i, source i ⟶ U

/-- The underlying function of an equivariant map of `G`-sets. -/
def gSetMapFunction {U V : GSet G} (f : U ⟶ V) : U.V → V.V :=
  ConcreteCategory.hom ((Action.forget (Type u) G).map f)

/-- Fiber products of `G`-sets have the underlying set-theoretic fiber product. -/
theorem gSet_pullback_underlying_equiv {X Y Z : GSet G}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    Nonempty ((pullback f g).V ≃
      {p : X.V × Y.V // gSetMapFunction f p.1 = gSetMapFunction g p.2}) := by
  sorry

/-- The source's covering condition for an indexed family of `G`-sets. -/
def GSetCoveringFamily {U : GSet G} (𝒰 : GSetFamily U) : Prop :=
  ∀ x : U.V, ∃ i y, gSetMapFunction (𝒰.hom i) y = x

/-- The indexed-family covering condition agrees with Mathlib's presieve site. -/
theorem gSetCoveringFamily_iff {U : GSet G}
    (𝒰 : GSetFamily U) :
    GSetCoveringFamily 𝒰 ↔
      Presieve.ofArrows 𝒰.source 𝒰.hom ∈ (GSetPretopology G) U := by
  sorry

/-- The source's site of `G`-sets, with coverings given by jointly-surjective families. -/
theorem gSet_site_covering_iff {U : GSet G} (R : Presieve U) :
    R ∈ (GSetPretopology G) U ↔
      ∀ x : U.V, ∃ (V : GSet G) (f : V ⟶ U),
        R f ∧ x ∈ Set.range (gSetMapFunction f) := by
  change R ∈ (Formalization.Books.Sites.Unit06.groupActionSite G) U ↔ _
  change R ∈ (Formalization.Books.Sites.Unit06.groupActionSite G) U ↔
    ∀ x : U.V, ∃ (V : GSet G) (f : V ⟶ U),
      R f ∧ x ∈ Set.range (ConcreteCategory.hom f.hom)
  exact Formalization.Books.Sites.Unit06.groupActionSite_mem_iff G R

/-- The empty `G`-set. -/
def emptyGSet : GSet G := by
  letI : MulAction G (ULift.{u} Empty) := {
    smul g x := nomatch x
    one_smul x := nomatch x
    mul_smul g h x := nomatch x
  }
  exact Action.ofMulAction G (ULift.{u} Empty)

/-- The empty family covers the empty `G`-set. -/
theorem emptyGSet_covering :
    (⊥ : Presieve (emptyGSet (G := G))) ∈
      (GSetPretopology G) (emptyGSet (G := G)) := by
  sorry

/-! ## The regular G-set and its automorphisms -/

/-- The special object `{}_G G`, with its left-translation action. -/
abbrev regularGSet : GSet G :=
  Formalization.Books.Sites.Unit06.leftRegularGSet G

/-- Right translation on the regular left `G`-set. -/
abbrev rightTranslation (G : Type u) [Group G] (g : G) :
    regularGSet (G := G) ⟶ regularGSet (G := G) :=
  Formalization.Books.Sites.Unit09.rightMultiplication g

@[simp]
theorem rightTranslation_one : rightTranslation (G := G) 1 = 𝟙 regularGSet := by
  sorry

@[simp]
theorem rightTranslation_comp (g h : G) :
    rightTranslation (G := G) g ≫ rightTranslation (G := G) h =
      rightTranslation (G := G) (g * h) := by
  sorry

theorem rightTranslation_apply_one (g : G) :
    (show G from ConcreteCategory.hom (rightTranslation (G := G) g).hom (1 : G)) = g := by
  sorry

theorem regular_automorphism_is_rightTranslation (φ : Aut regularGSet) :
    φ.hom = rightTranslation (G := G)
      (ConcreteCategory.hom φ.hom (1 : G)) := by
  sorry

/-- The right-translation automorphism attached to `g`. -/
def rightTranslationIso (G : Type u) [Group G] (g : G) :
    Aut (regularGSet (G := G)) where
  hom := rightTranslation (G := G) g
  inv := rightTranslation (G := G) g⁻¹
  hom_inv_id := by
    rw [rightTranslation_comp]
    simpa using (rightTranslation_one (G := G))
  inv_hom_id := by
    rw [rightTranslation_comp]
    simpa using (rightTranslation_one (G := G))

theorem rightTranslationIso_mul (g h : G) :
    rightTranslationIso (G := G) g * rightTranslationIso (G := G) h =
      rightTranslationIso (G := G) (h * g) := by
  sorry

/-- The source's group isomorphism `Gᵒᵖ ≃ Aut_G-Sets({}_G G)`. -/
theorem exists_rho :
    Nonempty {e : Gᵐᵒᵖ ≃* Aut (regularGSet (G := G)) //
      ∀ g, e g = rightTranslationIso (G := G) g.unop} := by
  sorry

noncomputable def rho : Gᵐᵒᵖ ≃* Aut (regularGSet (G := G)) :=
  (Classical.choice (exists_rho (G := G))).1

theorem rho_apply (g : Gᵐᵒᵖ) :
    rho (G := G) g = rightTranslationIso (G := G) g.unop :=
  (Classical.choice (exists_rho (G := G))).2 g

/-! ## Evaluation of presheaves at the regular object -/

/-- The sections of a presheaf over the regular `G`-set. -/
abbrev regularSections (F : Presheaf (GSet G)) := F.obj (op regularGSet)

/-- The action on regular sections induced by contravariance and right translation. -/
theorem presheafRegularGSet_mul_smul_formula (F : Presheaf (GSet G))
    (g h : G) (s : regularSections F) :
    F.map (rightTranslation (G := G) (g * h)).op s =
      F.map (rightTranslation (G := G) g).op
        (F.map (rightTranslation (G := G) h).op s) := by
  sorry

/-- The action on regular sections induced by contravariance and right translation. -/
def presheafRegularGSet (F : Presheaf (GSet G)) : GSet G := by
  letI : MulAction G (regularSections F) := {
    smul g s := F.map (rightTranslation (G := G) g).op s
    one_smul s := by
      change F.map (rightTranslation (G := G) 1).op s = s
      rw [rightTranslation_one]
      simp
    mul_smul g h s := by
      exact presheafRegularGSet_mul_smul_formula F g h s
  }
  exact Action.ofMulAction G (regularSections F)

theorem presheafRegularGSet_action (F : Presheaf (GSet G)) (g : G)
    (s : regularSections F) :
    (presheafRegularGSet F).ρ g s =
      F.map (rightTranslation (G := G) g).op s := by
  rfl

theorem presheafEvaluation_map_comm {F H : Presheaf (GSet G)}
    (η : F ⟶ H) (g : G) :
    (presheafRegularGSet F).ρ g ≫ η.app (op regularGSet) =
      η.app (op regularGSet) ≫ (presheafRegularGSet H).ρ g := by
  sorry

/-- Evaluation at the regular object is a functor from presheaves to `G`-sets. -/
def presheafEvaluationFunctor :
    Formalization.Books.EtaleCohomology.Unit09.PSh (GSet G) ⥤ GSet G where
  obj F := presheafRegularGSet F
  map η :=
    { hom := η.app (op regularGSet)
      comm := presheafEvaluation_map_comm η }
  map_id F := by
    apply Action.hom_ext
    rfl
  map_comp η θ := by
    apply Action.hom_ext
    rfl

/-! ## Orbits and the equalizer diagram -/

/-- The orbit of a point in a `G`-set. -/
def gSetOrbit (S : GSet G) (s : S.V) : Set S.V :=
  {x | ∃ g : G, S.ρ g s = x}

/-- A map whose image is one orbit and which is an inclusion of that orbit. -/
def IsOrbitInclusion {V S : GSet G} (f : V ⟶ S) : Prop :=
  Function.Injective (gSetMapFunction f) ∧
    ∃ s : S.V, Set.range (gSetMapFunction f) = gSetOrbit S s

/-- Data expressing the decomposition of a `G`-set into disjoint orbits. -/
structure GSetOrbitDecomposition (S : GSet G) where
  index : Type u
  domain : index → GSet G
  map : ∀ i, domain i ⟶ S
  isOrbit : ∀ i, IsOrbitInclusion (map i)
  unique : ∀ x : S.V, ∃! i, x ∈ Set.range (gSetMapFunction (map i))

/-- Every `G`-set admits a decomposition into its orbits. -/
theorem exists_gSetOrbitDecomposition (S : GSet G) :
    Nonempty (GSetOrbitDecomposition S) := by
  sorry

/-- The indexed family of orbit inclusions associated to a decomposition. -/
def orbitFamily {S : GSet G} (𝒪 : GSetOrbitDecomposition S) : GSetFamily S where
  index := 𝒪.index
  source := 𝒪.domain
  hom := 𝒪.map

theorem orbitFamily_isCovering {S : GSet G} (𝒪 : GSetOrbitDecomposition S) :
    GSetCoveringFamily (orbitFamily 𝒪) := by
  sorry

/-- The fiber product of two members of an orbit decomposition. -/
noncomputable def orbitFiberProduct {S : GSet G} (𝒪 : GSetOrbitDecomposition S)
    (i j : 𝒪.index) : GSet G :=
  pullback (𝒪.map i) (𝒪.map j)

/-- The product of sections over all orbit members. -/
def orbitSectionsProduct {S : GSet G} (𝒪 : GSetOrbitDecomposition S)
    (F : Presheaf (GSet G)) : Type u :=
  ∀ i, F.obj (op (𝒪.domain i))

/-- The product of sections over all pairwise orbit fiber products. -/
noncomputable def orbitOverlapSectionsProduct {S : GSet G} (𝒪 : GSetOrbitDecomposition S)
    (F : Presheaf (GSet G)) : Type u :=
  ∀ ij : 𝒪.index × 𝒪.index,
    F.obj (op (orbitFiberProduct 𝒪 ij.1 ij.2))

/-- Restriction of orbit sections to pairwise overlaps through the first projection. -/
noncomputable def orbitFirstRestriction {S : GSet G} (𝒪 : GSetOrbitDecomposition S)
    (F : Presheaf (GSet G)) :
    orbitSectionsProduct 𝒪 F → orbitOverlapSectionsProduct 𝒪 F :=
  fun s ij => F.map (pullback.fst (𝒪.map ij.1) (𝒪.map ij.2)).op (s ij.1)

/-- Restriction of orbit sections to pairwise overlaps through the second projection. -/
noncomputable def orbitSecondRestriction {S : GSet G} (𝒪 : GSetOrbitDecomposition S)
    (F : Presheaf (GSet G)) :
    orbitSectionsProduct 𝒪 F → orbitOverlapSectionsProduct 𝒪 F :=
  fun s ij => F.map (pullback.snd (𝒪.map ij.1) (𝒪.map ij.2)).op (s ij.2)

/-- The equalizer fork attached to the orbit covering. -/
noncomputable def orbitEqualizerFork {S : GSet G} (𝒪 : GSetOrbitDecomposition S)
    (F : Presheaf (GSet G)) :=
  Fork.ofι (Equalizer.Presieve.Arrows.forkMap F 𝒪.domain 𝒪.map)
    (Equalizer.Presieve.Arrows.w F 𝒪.domain 𝒪.map)

/-- A sheaf satisfies the source's orbit equalizer diagram. -/
theorem orbit_sheaf_equalizer {S : GSet G} (𝒪 : GSetOrbitDecomposition S)
    (F : Presheaf (GSet G)) (hF : SetSheaf (GSetSite G) F) :
    Nonempty (IsLimit (orbitEqualizerFork 𝒪 F)) := by
  sorry

/-- Pairwise orbit overlaps contribute only the diagonal copies of an orbit. -/
theorem orbit_overlap_sections_equiv {S : GSet G}
    (𝒪 : GSetOrbitDecomposition S) (F : Presheaf (GSet G)) :
    Nonempty (orbitOverlapSectionsProduct 𝒪 F ≃ orbitSectionsProduct 𝒪 F) := by
  sorry

/-- Under the orbit decomposition, the two restriction maps agree. -/
theorem orbit_restrictions_agree {S : GSet G}
    (𝒪 : GSetOrbitDecomposition S) (F : Presheaf (GSet G)) :
    orbitFirstRestriction 𝒪 F = orbitSecondRestriction 𝒪 F := by
  sorry

/-- Consequently, sections over `S` are equivalent to products of orbit sections. -/
theorem sheaf_sections_orbit_product {S : GSet G}
    (𝒪 : GSetOrbitDecomposition S) (F : Presheaf (GSet G))
    (hF : SetSheaf (GSetSite G) F) :
    Nonempty (F.obj (op S) ≃ orbitSectionsProduct 𝒪 F) := by
  sorry

/-! ## Quotients by subgroups and fixed sections -/

/-- The `G`-set of left cosets `G/H`. -/
def quotientGSet (H : Subgroup G) : GSet G :=
  Action.ofMulAction G (G ⧸ H)

/-- The quotient map `{}_G G → G/H`. -/
def quotientMap (H : Subgroup G) : regularGSet ⟶ quotientGSet H where
  hom := TypeCat.ofHom (fun g : G => (g : G ⧸ H))
  comm := by
    intro g
    apply ConcreteCategory.ext_apply
    intro x
    change (↑(g * (show G from x)) : G ⧸ H) =
      g • (↑(show G from x) : G ⧸ H)
    have hx : g • (show G from x) = g * (show G from x) := by rfl
    simpa [hx] using
      (MulAction.Quotient.smul_coe H g (show G from x)).symm

/-- `G × H` with `G` acting by left translation on the first factor. -/
def productGHGSet (H : Subgroup G) : GSet G := by
  letI : MulAction G (G × H) := {
    smul g x := (g * x.1, x.2)
    one_smul x := by
      rcases x with ⟨x, hx⟩
      change (1 * x, hx) = (x, hx)
      simp
    mul_smul g h x := by
      rcases x with ⟨x, hx⟩
      change ((g * h) * x, hx) = (g * (h * x), hx)
      rw [mul_assoc]
  }
  exact Action.ofMulAction G (G × H)

/-- The fiber product of the quotient cover with itself. -/
noncomputable def quotientFiberProduct (H : Subgroup G) : GSet G :=
  pullback (quotientMap H) (quotientMap H)

/-- The source's explicit identification of the quotient fiber product. -/
theorem quotient_fiber_product_iso (H : Subgroup G) :
    Nonempty (quotientFiberProduct H ≅ productGHGSet H) := by
  sorry

/-- Sections fixed by a subgroup of `G`. -/
def subgroupFixedSections (F : Presheaf (GSet G)) (H : Subgroup G) : Type u :=
  {s : (presheafRegularGSet F).V //
    ∀ h : H, (presheafRegularGSet F).ρ (h : G) s = s}

/-- The quotient calculation identifies sections on `G/H` with `H`-fixed sections. -/
theorem sheaf_sections_quotient_fixedPoints (H : Subgroup G)
    (F : Presheaf (GSet G)) (hF : SetSheaf (GSetSite G) F) :
    Nonempty (F.obj (op (quotientGSet H)) ≃ subgroupFixedSections F H) := by
  sorry

/-- The two maps in the quotient equalizer diagram. -/
def quotientEqualizerConstant (H : Subgroup G) (F : Presheaf (GSet G)) :
    regularSections F → (H → regularSections F) :=
  fun s _ => s

def quotientEqualizerAction (H : Subgroup G) (F : Presheaf (GSet G)) :
    regularSections F → (H → regularSections F) :=
  fun s h => (presheafRegularGSet F).ρ (h : G) s

/-- The equalizer of those maps is the subgroup-fixed section type. -/
def quotientEqualizerFixedSectionsEquiv (H : Subgroup G)
    (F : Presheaf (GSet G)) :
    {s : regularSections F //
        quotientEqualizerConstant H F s = quotientEqualizerAction H F s} ≃
      subgroupFixedSections F H where
  toFun s := ⟨s.1, fun h => congrFun s.2 h |>.symm⟩
  invFun s := ⟨s.1, funext fun h => (s.2 h).symm⟩
  left_inv := by intro s; cases s; rfl
  right_inv := by intro s; cases s; rfl

/-- The one-point `G`-set and the special case of `H = G`. -/
abbrev singletonGSet : GSet G := Action.trivial G PUnit

theorem sheaf_sections_singleton_fixedPoints (F : Presheaf (GSet G))
    (hF : SetSheaf (GSetSite G) F) :
    Nonempty (F.obj (op singletonGSet) ≃ subgroupFixedSections F ⊤) := by
  sorry

/-- A sheaf has singleton sections over the empty `G`-set. -/
theorem sheaf_empty_sections_singleton (F : Presheaf (GSet G))
    (hF : SetSheaf (GSetSite G) F) :
    Nonempty (F.obj (op (emptyGSet (G := G)))) ∧
      Subsingleton (F.obj (op (emptyGSet (G := G)))) := by
  sorry

/-! ## The sheaf/G-set equivalence -/

/-- The value of a sheaf at the regular object, as a `G`-set. -/
def sheafEvaluationFunctor :
    Sh (GSetSite G) ⥤ GSet G :=
  { obj F := (presheafEvaluationFunctor (G := G)).obj F.obj
    map η := (presheafEvaluationFunctor (G := G)).map η.hom }

/-- The representable presheaf `h_X` associated to a `G`-set. -/
def gSetRepresentable (X : GSet G) : Presheaf (GSet G) :=
  yoneda.obj X

/-- Representables are sheaves for the jointly-surjective `G`-set topology. -/
theorem gSetRepresentable_isSheaf (X : GSet G) :
    SetSheaf (GSetSite G) (gSetRepresentable X) := by
  sorry

/-- The quasi-inverse candidate `X ↦ h_X`. -/
def gSetToSheaves : GSet G ⥤ Sh (GSetSite G) where
  obj X := ⟨gSetRepresentable X, gSetRepresentable_isSheaf X⟩
  map f := ⟨yoneda.map f⟩
  map_id X := by rfl
  map_comp f g := by rfl

/-- The value of `h_X` at the regular object recovers `X`. -/
theorem gSetRepresentable_evaluation (X : GSet G) :
    Nonempty ((sheafEvaluationFunctor (G := G)).obj (gSetToSheaves.obj X) ≅ X) := by
  sorry

/-- The two displayed functors are quasi-inverse. -/
theorem sheaf_gSet_quasi_inverse :
    Nonempty ((sheafEvaluationFunctor (G := G) ⋙ gSetToSheaves) ≅ 𝟭 (Sh (GSetSite G))) ∧
      Nonempty ((gSetToSheaves ⋙ sheafEvaluationFunctor (G := G)) ≅ 𝟭 (GSet G)) := by
  sorry

/-- Consequently, sheaves on `𝒯_G` are equivalent to `G`-sets. -/
theorem sheaf_gSet_equivalence :
    Nonempty (Sh (GSetSite G) ≌ GSet G) := by
  sorry

end Formalization.Books.EtaleCohomology.Unit12
