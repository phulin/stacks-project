import Formalization.Books.Schemes.Unit02
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Schemes, Chapter 6: The category of affine schemes

This file records the definitions and theorem interfaces in the source section.  The
substantive proofs are intentionally left for the proof stage; the definitions use the
canonical scheme, locally ringed space, and tensor-product constructions already present in
Mathlib.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

namespace Formalization.Books.Schemes.Unit06

universe u

/-! ## Points of an affine scheme -/

/-- The canonical identification of the points of an affine scheme with prime ideals in its
global sections. -/
noncomputable def affineSchemePointEquiv (Y : Scheme.{u}) [IsAffine Y] :
    Y ≃ PrimeSpectrum (Γ(Y, ⊤)) :=
  Y.isoSpec.hom.homeomorph.toEquiv

/-! ## A morphism into an affine scheme -/

/-- Global sections of a locally ringed space, using Mathlib's contravariant global-sections
functor. -/
abbrev locallyRingedSpaceGlobalSections (X : LocallyRingedSpace.{u}) : CommRingCat.{u} :=
  AlgebraicGeometry.LocallyRingedSpace.Γ.obj (op X)

/-- The global-sections map induced by a morphism of locally ringed spaces. -/
def locallyRingedSpaceGlobalMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    locallyRingedSpaceGlobalSections Y ⟶ locallyRingedSpaceGlobalSections X :=
  AlgebraicGeometry.LocallyRingedSpace.Γ.map f.op

/-- The prime ideal obtained by pulling the maximal ideal at a point back along a morphism into
an affine scheme. -/
def affineMorphismPointPrimeIdeal
    {X : LocallyRingedSpace.{u}} {Y : Scheme.{u}}
    (f : X ⟶ Y.toLocallyRingedSpace) (x : X) : Ideal (Γ(Y, ⊤)) :=
  Ideal.comap
    ((locallyRingedSpaceGlobalMap f ≫ X.presheaf.germ ⊤ x trivial).hom)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))

/-- The prime of the affine coordinate ring corresponding to the image of a point under a
morphism of locally ringed spaces. -/
def affineMorphismPointPrime
    {X : LocallyRingedSpace.{u}} {Y : Scheme.{u}}
    (f : X ⟶ Y.toLocallyRingedSpace) (x : X) : PrimeSpectrum (Γ(Y, ⊤)) :=
  { asIdeal := affineMorphismPointPrimeIdeal f x
    isPrime := Ideal.comap_isPrime _ _ }

/-- The point associated to the pulled-back maximal ideal is the image of the original point. -/
theorem affineMorphism_point_goes_to_corresponding_prime
    {X : LocallyRingedSpace.{u}} {Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y.toLocallyRingedSpace) (x : X) :
    f.base x = (affineSchemePointEquiv Y).symm (affineMorphismPointPrime f x) := by
  apply (affineSchemePointEquiv Y).injective
  simp only [Equiv.apply_symm_apply]
  unfold affineSchemePointEquiv
  change (Y.isoSpec.hom (f.base x) : PrimeSpectrum _) = _
  apply PrimeSpectrum.ext
  ext a
  change (Y.presheaf.Γgerm (f.base x)).hom a ∈ IsLocalRing.maximalIdeal _ ↔
    ((locallyRingedSpaceGlobalMap f ≫ X.presheaf.germ ⊤ x trivial).hom) a ∈
      IsLocalRing.maximalIdeal _
  rw [← not_iff_not, IsLocalRing.notMem_maximalIdeal,
    IsLocalRing.notMem_maximalIdeal]
  change IsUnit ((ConcreteCategory.hom (Y.presheaf.Γgerm (f.base x))) a) ↔
    IsUnit ((ConcreteCategory.hom (X.presheaf.germ ⊤ x trivial))
      ((ConcreteCategory.hom (f.c.app (op ⊤))) a))
  have h := AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ_apply
    f (⊤ : TopologicalSpace.Opens Y) x (by trivial) a
  exact (isUnit_map_iff (f.stalkMap x).hom _).symm.trans
    (eq_iff_iff.mp (by
      convert congrArg (fun z => IsUnit z) h using 1
      · simp [TopCat.Presheaf.Γgerm]
      · exact Iff.rfl))

/-! ## The basic open D(f) -/

/-- The locally ringed space version of the basic open associated to a global section. -/
def locallyRingedSpaceBasicOpen (X : LocallyRingedSpace.{u})
    (f : locallyRingedSpaceGlobalSections X) : TopologicalSpace.Opens X :=
  X.toRingedSpace.basicOpen f

/-- Membership in the basic open is the condition that the germ is outside the maximal ideal of
the stalk. -/
theorem mem_locallyRingedSpaceBasicOpen_iff
    (X : LocallyRingedSpace.{u}) (f : locallyRingedSpaceGlobalSections X) (x : X) :
    x ∈ locallyRingedSpaceBasicOpen X f ↔
      X.presheaf.germ ⊤ x trivial f ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  change (∃ _ : x ∈ (⊤ : TopologicalSpace.Opens X),
    IsUnit (X.presheaf.germ ⊤ x trivial f)) ↔ _
  simp

/-- The basic open is open. -/
theorem locallyRingedSpaceBasicOpen_isOpen
    (X : LocallyRingedSpace.{u}) (f : locallyRingedSpaceGlobalSections X) :
    IsOpen (locallyRingedSpaceBasicOpen X f : Set X) := by
  exact (locallyRingedSpaceBasicOpen X f).isOpen

/-- Restriction of a global section to its basic open. -/
def locallyRingedSpaceBasicOpen_restrictSection
    (X : LocallyRingedSpace.{u}) (f : locallyRingedSpaceGlobalSections X) :
    X.presheaf.obj (op (locallyRingedSpaceBasicOpen X f)) :=
  X.presheaf.map
    (homOfLE (show locallyRingedSpaceBasicOpen X f ≤ ⊤ from le_top)).op f

/-- The restriction of a section to its basic open is a unit, hence has an inverse. -/
theorem locallyRingedSpaceBasicOpen_restrictSection_isUnit
    (X : LocallyRingedSpace.{u}) (f : locallyRingedSpaceGlobalSections X) :
    IsUnit (locallyRingedSpaceBasicOpen_restrictSection X f) := by
  change IsUnit ((X.toRingedSpace.presheaf.map
    (homOfLE (show X.toRingedSpace.basicOpen f ≤ ⊤ from le_top)).op) f)
  exact X.toRingedSpace.isUnit_res_basicOpen f

/-! ## Comparison with the standard open of an affine scheme -/

/-- On an affine scheme, the locally ringed space basic open agrees with the standard open in the
prime spectrum of the global-sections ring. -/
theorem affineScheme_basicOpen_eq_standardOpen
    (Y : Scheme.{u}) [IsAffine Y] (f : Γ(Y, ⊤)) :
    Y.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f = Y.basicOpen f := by
  exact Scheme.map_PrimeSpectrum_basicOpen_of_affine Y f

/-! ## The affine target mapping property -/

/-- The global-sections map attached to a morphism from a locally ringed space to an affine
scheme. -/
def morphismIntoAffine_globalSectionsMap
    (X : LocallyRingedSpace.{u}) (Y : Scheme.{u}) :
    (X ⟶ Y.toLocallyRingedSpace) →
      (Γ(Y, ⊤) ⟶ locallyRingedSpaceGlobalSections X) :=
  fun f => locallyRingedSpaceGlobalMap f

/-- Morphisms from a locally ringed space to an affine scheme are classified by maps on global
sections. -/
theorem morphismIntoAffine_globalSectionsMap_bijective
    (X : LocallyRingedSpace.{u}) (Y : Scheme.{u}) [IsAffine Y] :
    Function.Bijective (morphismIntoAffine_globalSectionsMap X Y) := by
  let e := Scheme.forgetToLocallyRingedSpace.mapIso Y.isoSpec
  let E : (Γ(Y, ⊤) ⟶ locallyRingedSpaceGlobalSections X) ≃
      (X ⟶ Scheme.forgetToLocallyRingedSpace.obj (Spec (Γ(Y, ⊤)))) :=
    (opEquiv (op (locallyRingedSpaceGlobalSections X))
        (op (locallyRingedSpaceGlobalSections (Scheme.forgetToLocallyRingedSpace.obj Y)))).symm.trans
      (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op (Γ(Y, ⊤))))
  let P : (X ⟶ Scheme.forgetToLocallyRingedSpace.obj (Spec (Γ(Y, ⊤)))) ≃
      (X ⟶ Scheme.forgetToLocallyRingedSpace.obj Y) :=
    { toFun := fun f => f ≫ e.inv
      invFun := fun f => f ≫ e.hom
      left_inv := by intro f; dsimp; rw [Category.assoc, e.inv_hom_id, Category.comp_id]
      right_inv := by intro f; dsimp; rw [Category.assoc, e.hom_inv_id, Category.comp_id] }
  have h : (morphismIntoAffine_globalSectionsMap X Y) =
      E.symm ∘ P.symm := by
    funext f
    dsimp [morphismIntoAffine_globalSectionsMap, P, E]
    change locallyRingedSpaceGlobalMap f =
      (opEquiv _ _)
        ((ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op (Γ(Y, ⊤)))).symm
          (f ≫ e.hom))
    have hu :
        (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op (Γ(Y, ⊤))))
            ((opEquiv _ _).symm (locallyRingedSpaceGlobalMap f)) = f ≫ e.hom := by
      rw [ΓSpec.locallyRingedSpaceAdjunction_homEquiv_apply]
      change
        ΓSpec.locallyRingedSpaceAdjunction.unit.app X ≫
            Spec.locallyRingedSpaceMap (locallyRingedSpaceGlobalMap f) =
          f ≫ ΓSpec.locallyRingedSpaceAdjunction.unit.app Y.toLocallyRingedSpace
      exact (ΓSpec.locallyRingedSpaceAdjunction.unit.naturality f).symm
    have hs :
        (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op (Γ(Y, ⊤)))).symm
            (f ≫ e.hom) =
          (opEquiv (LocallyRingedSpace.Γ.rightOp.obj X) (op (Γ(Y, ⊤)))).symm
            (locallyRingedSpaceGlobalMap f) := by
      rw [Equiv.symm_apply_eq]
      exact hu.symm
    rw [hs]
    rfl
  rw [h]
  exact E.symm.bijective.comp P.symm.bijective

/-! ## The category of affine schemes -/

/-- The canonical equivalence between affine schemes and opposite commutative rings.  Its
forward functor is Mathlib's global-sections equivalence. -/
noncomputable def affineSchemeCategoryEquivalence :
    AffineScheme.{u} ≌ CommRingCat.{u}ᵒᵖ :=
  AffineScheme.equivCommRingCat

/-! ## Standard opens and affine limits -/

/-- A basic open in an affine scheme is affine. -/
theorem standardOpen_isAffine
    (Y : Scheme.{u}) [IsAffine Y] (f : Γ(Y, ⊤)) :
    IsAffine (Y.basicOpen f) := by
  infer_instance

/-- The affine category has finite limits. -/
theorem affineScheme_has_finite_limits : HasFiniteLimits AffineScheme.{u} := by
  infer_instance

/-- The affine morphism induced by an algebra map. -/
def affineSchemeMapOfAlgebra
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Spec (.of A) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

/-- The canonical affine-scheme fibre-product identification by a tensor product. -/
noncomputable def affineSchemeFibreProductIso
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    pullback (affineSchemeMapOfAlgebra R A) (affineSchemeMapOfAlgebra R B) ≅
      Spec (.of (A ⊗[R] B)) :=
  AlgebraicGeometry.pullbackSpecIso R A B

/-- The product formula is the fibre-product formula over `Spec ℤ`. -/
noncomputable def affineSchemeProductIso
    (A B : Type) [CommRing A] [CommRing B] :
    pullback (affineSchemeMapOfAlgebra ℤ A) (affineSchemeMapOfAlgebra ℤ B) ≅
      Spec (.of (A ⊗[ℤ] B)) :=
  affineSchemeFibreProductIso ℤ A B

/-- The locally ringed space cone underlying the affine-scheme fibre product. -/
def locallyRingedSpaceAffineFibreProductCone
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    PullbackCone
      (affineSchemeMapOfAlgebra R A).toLRSHom
      (affineSchemeMapOfAlgebra R B).toLRSHom := by
  refine PullbackCone.mk
    (pullback.fst (affineSchemeMapOfAlgebra R A) (affineSchemeMapOfAlgebra R B)).toLRSHom
    (pullback.snd (affineSchemeMapOfAlgebra R A) (affineSchemeMapOfAlgebra R B)).toLRSHom ?_
  simpa only [Scheme.Hom.comp_toLRSHom] using
    congrArg Scheme.Hom.toLRSHom
      (pullback.condition :
        pullback.fst (affineSchemeMapOfAlgebra R A) (affineSchemeMapOfAlgebra R B) ≫
            affineSchemeMapOfAlgebra R A =
          pullback.snd (affineSchemeMapOfAlgebra R A) (affineSchemeMapOfAlgebra R B) ≫
            affineSchemeMapOfAlgebra R B)

/-- The affine-scheme fibre product has the same universal property in locally ringed spaces. -/
theorem affineSchemeFibreProduct_is_pullback_in_locallyRingedSpace
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    Nonempty (IsLimit (locallyRingedSpaceAffineFibreProductCone R A B)) := by
  let c := (CommRingCat.pushoutCocone R A B).op
  have hc : IsLimit c :=
    PushoutCocone.isColimitEquivIsLimitOp
      (CommRingCat.pushoutCocone R A B) (CommRingCat.pushoutCoconeIsColimit R A B)
  let cL := PullbackCone.map c Spec.toLocallyRingedSpace
  have hcL : IsLimit cL :=
    isLimitPullbackConeMapOfIsLimit Spec.toLocallyRingedSpace c.condition
      (hc.ofIsoLimit (PullbackCone.eta c))
  let e : (locallyRingedSpaceAffineFibreProductCone R A B).pt ≅ cL.pt :=
    Scheme.forgetToLocallyRingedSpace.mapIso (affineSchemeFibreProductIso R A B)
  have hfst : (locallyRingedSpaceAffineFibreProductCone R A B).fst = e.hom ≫ cL.fst := by
    change
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).toLRSHom =
        (AlgebraicGeometry.pullbackSpecIso R A B).hom.toLRSHom ≫
          (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom))).toLRSHom
    simpa only [Scheme.Hom.comp_toLRSHom] using congrArg Scheme.Hom.toLRSHom
      (AlgebraicGeometry.pullbackSpecIso_hom_fst R A B).symm
  have hsnd : (locallyRingedSpaceAffineFibreProductCone R A B).snd = e.hom ≫ cL.snd := by
    change
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).toLRSHom =
        (AlgebraicGeometry.pullbackSpecIso R A B).hom.toLRSHom ≫
          (Spec.map (CommRingCat.ofHom (R := B) (S := A ⊗[R] B)
            (RingHomClass.toRingHom Algebra.TensorProduct.includeRight))).toLRSHom
    simpa only [Scheme.Hom.comp_toLRSHom] using congrArg Scheme.Hom.toLRSHom
      (AlgebraicGeometry.pullbackSpecIso_hom_snd R A B).symm
  refine ⟨IsLimit.ofIsoLimit hcL (PullbackCone.ext e.symm ?_ ?_)⟩
  · rw [← cancel_epi e.hom]
    simpa [Iso.symm_hom, Category.assoc, Spec_toLocallyRingedSpace,
      Spec.toLocallyRingedSpace] using hfst.symm
  · rw [← cancel_epi e.hom]
    simpa [Iso.symm_hom, Category.assoc, Spec_toLocallyRingedSpace,
      Spec.toLocallyRingedSpace] using hsnd.symm

/-- The product case is the preceding locally ringed space pullback over `Spec ℤ`. -/
theorem affineSchemeProduct_is_pullback_in_locallyRingedSpace
    (A B : Type) [CommRing A] [CommRing B] :
    Nonempty (IsLimit (locallyRingedSpaceAffineFibreProductCone ℤ A B)) := by
  exact affineSchemeFibreProduct_is_pullback_in_locallyRingedSpace ℤ A B

/-! ## Disjoint unions of affine opens -/

/-- Affineness for a locally ringed space, expressed by an isomorphism with the underlying
locally ringed space of a spectrum.  Mathlib's `IsAffine` is defined only for schemes, so this is
the minimal bridge needed for the source's statement, whose input is an arbitrary locally ringed
space. -/
def IsAffineLocallyRingedSpace (X : LocallyRingedSpace.{u}) : Prop :=
  ∃ R : CommRingCat.{u}, Nonempty (X ≅ (Spec R).toLocallyRingedSpace)

/-- An open of a locally ringed space is affine when its restricted locally ringed space is a
spectrum. -/
def IsAffineLocallyRingedSpaceOpen
    (X : LocallyRingedSpace.{u}) (U : TopologicalSpace.Opens X) : Prop :=
  IsAffineLocallyRingedSpace (X.restrict (Opens.isOpenEmbedding U))

/-- A locally ringed space which is the disjoint union of two affine opens is affine. -/
theorem disjointUnion_of_affine_opens_is_affine
    (X : LocallyRingedSpace.{u}) (U V : TopologicalSpace.Opens X)
    (hcover : (U : Set X) ∪ (V : Set X) = Set.univ)
    (hdisjoint : Disjoint (U : Set X) (V : Set X))
    (hU : IsAffineLocallyRingedSpaceOpen X U)
    (hV : IsAffineLocallyRingedSpaceOpen X V) :
    IsAffineLocallyRingedSpace X := by
  change ∃ RU : CommRingCat.{u},
    Nonempty (X.restrict (Opens.isOpenEmbedding U) ≅ (Spec RU).toLocallyRingedSpace) at hU
  change ∃ RV : CommRingCat.{u},
    Nonempty (X.restrict (Opens.isOpenEmbedding V) ≅ (Spec RV).toLocallyRingedSpace) at hV
  obtain ⟨RU, hRU⟩ := hU
  obtain ⟨RV, hRV⟩ := hV
  let S : Scheme.{u} :=
    { toLocallyRingedSpace := X
      local_affine := by
        intro x
        have hx : x ∈ (U : Set X) ∨ x ∈ (V : Set X) := by
          have : x ∈ (U : Set X) ∪ (V : Set X) := by rw [hcover]; trivial
          rcases this with hx | hx
          · exact Or.inl hx
          · exact Or.inr hx
        rcases hx with hx | hx
        · exact ⟨⟨U, hx⟩, RU, hRU⟩
        · exact ⟨⟨V, hx⟩, RV, hRV⟩ }
  let US : S.Opens := U
  let VS : S.Opens := V
  let f : S.restrict (Opens.isOpenEmbedding US) ⟶ S := US.ι
  let g : S.restrict (Opens.isOpenEmbedding VS) ⟶ S := VS.ι
  have hIf : IsOpenImmersion f := by
    change LocallyRingedSpace.IsOpenImmersion
      (S.toLocallyRingedSpace.ofRestrict (Opens.isOpenEmbedding US))
    infer_instance
  have hIg : IsOpenImmersion g := by
    change LocallyRingedSpace.IsOpenImmersion
      (S.toLocallyRingedSpace.ofRestrict (Opens.isOpenEmbedding VS))
    infer_instance
  have hcomplUV : IsCompl US VS := by
    refine ⟨?_, ?_⟩
    · simpa [disjoint_iff, ← TopologicalSpace.Opens.coe_inj] using hdisjoint
    · simpa [codisjoint_iff, ← TopologicalSpace.Opens.coe_inj] using hcover
  have hcompl : IsCompl f.opensRange g.opensRange := by
    change IsCompl (US.ι.opensRange) (VS.ι.opensRange)
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    exact hcomplUV
  have hcolim : Nonempty (IsColimit (BinaryCofan.mk f g)) :=
    @nonempty_isColimit_binaryCofanMk_of_isCompl _ _ _ f g hIf hIg hcompl
  let eU : S.restrict (Opens.isOpenEmbedding US) ≅ Spec RU :=
    Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso hRU.some
  let eV : S.restrict (Opens.isOpenEmbedding VS) ≅ Spec RV :=
    Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso hRV.some
  let q : BinaryCofan (S.restrict (Opens.isOpenEmbedding US))
      (S.restrict (Opens.isOpenEmbedding VS)) :=
    BinaryCofan.mk coprod.inl coprod.inr
  have hq : IsColimit q := by
    dsimp [q]
    exact coprodIsCoprod _ _
  have i0 : (BinaryCofan.mk f g).pt ≅ q.pt :=
    IsColimit.coconePointUniqueUpToIso hcolim.some hq
  let i : S ≅ S.restrict (Opens.isOpenEmbedding US) ⨿
      S.restrict (Opens.isOpenEmbedding VS) :=
    by simpa [q] using i0
  have hcoprod : IsAffine (S.restrict (Opens.isOpenEmbedding US) ⨿
      S.restrict (Opens.isOpenEmbedding VS)) :=
    IsAffine.of_isIso ((coprod.mapIso eU eV).hom ≫ coprodSpec _ _)
  have hS : IsAffine S :=
    @IsAffine.of_isIso S
      (S.restrict (Opens.isOpenEmbedding US) ⨿ S.restrict (Opens.isOpenEmbedding VS))
      i.hom i.isIso_hom hcoprod
  exact ⟨Γ(S, ⊤), ⟨Scheme.forgetToLocallyRingedSpace.mapIso (@Scheme.isoSpec S hS)⟩⟩

end Formalization.Books.Schemes.Unit06
