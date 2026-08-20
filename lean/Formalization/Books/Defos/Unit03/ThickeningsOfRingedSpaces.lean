import Formalization.Books.Modules.Unit13.ClosedImmersions
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Homeomorph.Defs

/-!
# Deformation Theory, Chapter 3: Thickenings of ringed spaces

This file formalizes the source section `books/defos.tex:479-574`.  The
ringed-space and sheaf-module constructions are the canonical interfaces from
the Sheaves and Modules chapters.  In particular, the ideal of a morphism is
the kernel module already used for closed immersions, and epimorphisms are the
categorical form of surjective maps of sheaves.
-/

namespace Formalization.Books.Defos.Unit03

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Modules.Unit13

universe v

noncomputable section

/-! ## Locally nilpotent ideals and thickenings -/

/- A sheaf of ideals is represented by its underlying module together with its
   monomorphism into the unit module.  This is the source-facing wrapper around
   the canonical submodule/kernel interfaces. -/

/-- A sheaf of ideals in the structure sheaf of a ringed space. -/
structure IdealSheaf (X : RingedSpace.{v}) where
  carrier : Mod X.structureSheaf
  inclusion : carrier ⟶ SheafOfModules.unit X.structureSheaf
  inclusion_mono : Mono inclusion

/-- A section of an ideal sheaf is locally nilpotent. -/
def IsLocallyNilpotentIdeal {X : RingedSpace.{v}} (I : IdealSheaf X) : Prop :=
  ∀ (U : Opens X.carrier) (s : I.carrier.val.obj (op U)) (x : X),
    x ∈ U →
      ∃ (V : Opens X.carrier) (hVU : V ≤ U), x ∈ V ∧
        ∃ n : ℕ,
          (let a : X.structureSheaf.obj.obj (op V) :=
            (I.inclusion.val.app (op V)).hom
              ((I.carrier.val.map (homOfLE hVU).op) s)
           a ^ n = 0)

/-- The square of an ideal sheaf is zero. -/
def IsSquareZeroIdeal {X : RingedSpace.{v}} (I : IdealSheaf X) : Prop :=
  ∀ (U : Opens X.carrier) (a b : I.carrier.val.obj (op U)),
    (let a' : X.structureSheaf.obj.obj (op U) :=
      (I.inclusion.val.app (op U)).hom a
     let b' : X.structureSheaf.obj.obj (op U) :=
      (I.inclusion.val.app (op U)).hom b
     a' * b' = 0)

/-- The ideal sheaf cutting out a morphism of ringed spaces. -/
noncomputable def thickeningIdeal {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') : IdealSheaf X' where
  carrier := closedImmersionIdeal i
  inclusion := closedImmersionIdealInclusion i
  inclusion_mono := by
    change Mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.sharp))
    infer_instance

/-- A morphism of ringed spaces is a thickening when its space map is a
homeomorphism, its structure-sheaf map and its associated module map are
epimorphisms, and its kernel ideal is locally nilpotent. -/
structure IsThickening {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') : Prop where
  underlying_homeomorph : IsHomeomorph i.continuous.hom
  structureSheaf_surjective : StructureSheafMapSurjective i
  structureSheaf_module_epi :
    Epi (SheafOfModules.unitToPushforwardObjUnit i.sharp)
  kernel_locallyNilpotent : IsLocallyNilpotentIdeal (thickeningIdeal i)

/-- A first-order thickening is a thickening whose kernel ideal has square zero. -/
structure IsFirstOrderThickening {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') extends IsThickening i where
  kernel_square_zero : IsSquareZeroIdeal (thickeningIdeal i)

/-! The kernel sequence and the module-category observation -/

/-- The short complex
`0 → Ker(i♯) → 𝒪_{X'} → i_*𝒪_X → 0` attached to a ringed-space morphism. -/
noncomputable def thickeningKernelShortComplex {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') : ShortComplex (Mod X'.structureSheaf) :=
  ShortComplex.mk
    (closedImmersionIdealInclusion i)
    (SheafOfModules.unitToPushforwardObjUnit i.sharp)
    (kernel.condition (SheafOfModules.unitToPushforwardObjUnit i.sharp))

/-- The kernel sequence of a thickening is short exact. -/
/- Proof roadmap for the `prove` stage:
   Put `q := SheafOfModules.unitToPushforwardObjUnit i.sharp`.  After
   unfolding `thickeningKernelShortComplex`, its first arrow is definitionally
   `kernel.ι q`, so
   `ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel q)` supplies exactness
   (`Mathlib/Algebra/Homology/ShortComplex/Exact.lean`).  Install
   `hi.structureSheaf_module_epi` as the local `Epi q` instance; the first
   arrow is already mono by the kernel instance.  Finish with
   `ShortComplex.ShortExact.mk'`, passing the exactness proof, the inferred
   `Mono (kernel.ι q)`, and the installed `Epi q`.  Do not try to derive this
   from `hi.structureSheaf_surjective`: that field is stalk-surjectivity for
   the ring sheaf, whereas this declaration needs the explicitly stored epi
   in the sheaf-of-modules category. -/
theorem thickeningKernelShortComplex_shortExact
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsThickening i) :
    (thickeningKernelShortComplex i).ShortExact := by
  let q := SheafOfModules.unitToPushforwardObjUnit i.sharp
  have hq : Epi q := hi.structureSheaf_module_epi
  change (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel q)
  · infer_instance
  · exact hq

/-- A module on the thickened space is annihilated by the kernel ideal. -/
abbrev AnnihilatedByThickeningIdeal {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') (G : Mod X'.structureSheaf) : Prop :=
  sheafModuleAnnihilatedBy (G := G) (closedImmersionIdealInclusion i)

/-- The full subcategory of modules annihilated by a thickening ideal. -/
abbrev AnnihilatedByThickeningIdealCategory {X X' : RingedSpace.{v}}
    (i : RingedSpaceHom X X') :=
  ObjectProperty.FullSubcategory
    (AnnihilatedByThickeningIdeal i)

/-- The module category on the reduced space is equivalent to the full
subcategory of modules on the thickening annihilated by its ideal. -/
theorem thickening_module_category_equivalence
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsThickening i) :
    Nonempty
      (Mod X.structureSheaf ≌
        AnnihilatedByThickeningIdealCategory i) := by
  have hclosed := hi.underlying_homeomorph.isClosedEmbedding
  let F : Mod X.structureSheaf ⥤ AnnihilatedByThickeningIdealCategory i :=
    { obj := fun G => ⟨(ringedSpaceModulePushforward i).obj G, by
        exact (closedImmersion_pushforward_essentialImage i hclosed hi.structureSheaf_surjective
          ((ringedSpaceModulePushforward i).obj G)).mp ⟨G, ⟨Iso.refl _⟩⟩⟩
      map := fun f => ObjectProperty.homMk ((ringedSpaceModulePushforward i).map f)
      map_id := by intros; apply ObjectProperty.hom_ext; simp
      map_comp := by intros; apply ObjectProperty.hom_ext; simp }
  have hcomp : (F ⋙ ObjectProperty.ι (AnnihilatedByThickeningIdeal i)).FullyFaithful := by
    dsimp [F]
    exact (closedImmersion_pushforward_fullyFaithful i hclosed hi.structureSheaf_surjective).some
  have hF : F.FullyFaithful := Functor.FullyFaithful.ofCompFaithful hcomp
  have hEss : Functor.EssSurj F := by
    refine { mem_essImage := ?_ }
    intro G
    rcases (closedImmersion_pushforward_essentialImage i hclosed
      hi.structureSheaf_surjective G.obj).mpr G.property with ⟨H, ⟨e⟩⟩
    refine ⟨H, ?_⟩
    let e' : F.obj H ≅ G := ObjectProperty.isoMk (P := AnnihilatedByThickeningIdeal i) (X := F.obj H) (Y := G) e
    exact ⟨e'⟩
  let hEq : F.IsEquivalence := { full := hF.full, faithful := hF.faithful, essSurj := hEss }
  exact ⟨@Functor.asEquivalence _ _ _ _ F hEq⟩

/-- Objectwise essential-image form of the module-category equivalence. -/
theorem thickening_module_essential_image
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsThickening i) (G : Mod X'.structureSheaf) :
    (∃ F : Mod X.structureSheaf,
      Nonempty ((ringedSpaceModulePushforward i).obj F ≅ G)) ↔
      AnnihilatedByThickeningIdeal i G := by
  have hclosed := hi.underlying_homeomorph.isClosedEmbedding
  exact closedImmersion_pushforward_essentialImage i hclosed
    hi.structureSheaf_surjective G

/-- For a first-order thickening, the kernel ideal is an
`𝒪_X`-module, expressed through the module-category equivalence. -/
theorem firstOrderThickening_kernel_is_module
    {X X' : RingedSpace.{v}} (i : RingedSpaceHom X X')
    (hi : IsFirstOrderThickening i) :
    ∃ I : Mod X.structureSheaf,
      Nonempty
        ((ringedSpaceModulePushforward i).obj I ≅
          (thickeningIdeal i).carrier) := by
  have hclosed := hi.toIsThickening.underlying_homeomorph.isClosedEmbedding
  apply (closedImmersion_pushforward_essentialImage i hclosed
    hi.toIsThickening.structureSheaf_surjective (thickeningIdeal i).carrier).mpr
  intro U a b
  let a' : X'.structureSheaf.obj.obj (op U) := by
    have t := ((closedImmersionIdealInclusion i).val.app (op U)).hom a
    change X'.structureSheaf.obj.obj (op U) at t
    exact t
  let b' : X'.structureSheaf.obj.obj (op U) := by
    have t := ((thickeningIdeal i).inclusion.val.app (op U)).hom b
    change X'.structureSheaf.obj.obj (op U) at t
    exact t
  have ha' : a' =
      (show X'.structureSheaf.obj.obj (op U) from
        ((closedImmersionIdealInclusion i).val.app (op U)).hom a) := by
    rfl
  have hb' : b' =
      (show X'.structureSheaf.obj.obj (op U) from
        ((thickeningIdeal i).inclusion.val.app (op U)).hom b) := by
    rfl
  change a' • b = 0
  have hmono : Mono ((thickeningIdeal i).inclusion.val.app (op U)) := by
    exact @Functor.map_mono _ _ _ _
      (SheafOfModules.evaluation X'.structureSheaf (op U)) _ _ _
      (thickeningIdeal i).inclusion (thickeningIdeal i).inclusion_mono
  apply (ModuleCat.mono_iff_injective _).1 hmono
  have hmap := ((thickeningIdeal i).inclusion.val.app (op U)).hom.map_smul a' b
  have hunit :
      a' • ((thickeningIdeal i).inclusion.val.app (op U)).hom b = a' * b' := by
    change a' • b' = a' * b'
    exact smul_eq_mul a' b'
  have hsq := hi.kernel_square_zero
  dsimp [IsSquareZeroIdeal] at hsq
  let ha : (thickeningIdeal i).carrier.val.obj (op U) := by
    simpa only [thickeningIdeal] using a
  let hb : (thickeningIdeal i).carrier.val.obj (op U) := by
    simpa only [thickeningIdeal] using b
  have hz : a' * b' = 0 := by
    rw [ha', hb']
    convert hsq U ha hb using 1; rfl
  rw [hmap, hunit]
  simp only [map_zero]
  assumption

/-! ## Morphisms of thickenings -/

/-- The commutative square of ringed spaces whose horizontal maps are
thickenings. -/
structure MorphismOfThickenings where
  X : RingedSpace.{v}
  X' : RingedSpace.{v}
  S : RingedSpace.{v}
  S' : RingedSpace.{v}
  i : RingedSpaceHom X X'
  f : RingedSpaceHom X S
  f' : RingedSpaceHom X' S'
  t : RingedSpaceHom S S'
  commutes : RingedSpaceHom.comp f t = RingedSpaceHom.comp i f'
  i_isThickening : IsThickening i
  t_isThickening : IsThickening t

namespace MorphismOfThickenings

/-- The source kernel ideal `𝓘 = Ker(i♯)`. -/
abbrev sourceIdeal (M : MorphismOfThickenings) : IdealSheaf M.X' :=
  thickeningIdeal M.i

/-- The base kernel ideal `𝓙 = Ker(t♯)`. -/
abbrev baseIdeal (M : MorphismOfThickenings) : IdealSheaf M.S' :=
  thickeningIdeal M.t

/- The sheaf-module pullback below is the canonical `f^*` construction.  The
   right-adjoint instance is an explicit Mathlib hypothesis in the existing
   API.  First expose the map on the pushed-forward ideal (the module form of
   `f'^{-1}𝓙 → 𝓘`), then transpose it along the existing pullback/pushforward
   Hom equivalence. -/

/- The source's map `f'⁻¹𝓙 → 𝓘` is represented as the unique kernel
   factorization of the canonical `f'`-map
   `𝓙 → f'_*𝒪_{X'}`.  Recording the factorization equation is essential:
   mere inhabitation of this Hom type would also admit the zero map and would
   make `IsStrict` unrelated to the square of thickenings. -/
/- Proof roadmap for the `prove` stage:
   Let `R := ringedSpaceModulePushforward M.f'`,
   `L := ringedSpaceModulePullback M.f'`, and
   `adj := ringedSpaceModuleAdjunction M.f'` (all from
   `Formalization/Books/Sheaves/Unit26/Infrastructure.lean`).  Form
   `u := M.baseIdeal.inclusion ≫
     SheafOfModules.unitToPushforwardObjUnit M.f'.sharp` and transpose it to
   `u' : L.obj M.baseIdeal.carrier ⟶ SheafOfModules.unit _` with
   `(adj.homEquiv _ _).symm`.

   The key intermediate claim is
   `u' ≫ SheafOfModules.unitToPushforwardObjUnit M.i.sharp = 0`.
   Apply the injectivity of `adj.homEquiv` and rewrite the transpose of this
   composite with `Adjunction.homEquiv_naturality_right`.  The resulting
   `f'`-map is the base inclusion followed around the structure-sheaf square.
   Expand the two composites with `RingedSpaceHom.comp_sharp` and compare
   their pushforwards using `ringedSpaceModulePushforwardCompIso M.f M.t`
   and `ringedSpaceModulePushforwardCompIso M.i M.f'`; rewrite the middle
   morphism with `M.commutes`.  It is zero because the other route begins
   with `M.baseIdeal.inclusion = kernel.ι _` and
   `kernel.condition (SheafOfModules.unitToPushforwardObjUnit M.t.sharp)`.
   If simplification does not expose the equality, ext on an open `U` and a
   section and use
   `SheafOfModules.unitToPushforwardObjUnit_val_app_apply`; both sides then
   reduce to `congrArg RingedSpaceHom.sharp M.commutes`.

   Define `l := kernel.lift
     (SheafOfModules.unitToPushforwardObjUnit M.i.sharp) u'` using that
   vanishing claim (the kernel is definitionally `M.sourceIdeal.carrier`).
   Set `φ := adj.homEquiv _ _ l`.  For the displayed factorization, again
   use `Adjunction.homEquiv_naturality_right`, `kernel.lift_ι`, and
   `Equiv.apply_symm_apply`.  This constructs the canonical map; the old
   approach `⟨0⟩` proves only the discarded `Nonempty` interface and must not
   be reused. -/
theorem exists_inducedIdealFMap
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    ∃ φ : M.baseIdeal.carrier ⟶
        (ringedSpaceModulePushforward M.f').obj M.sourceIdeal.carrier,
      φ ≫ (ringedSpaceModulePushforward M.f').map M.sourceIdeal.inclusion =
        M.baseIdeal.inclusion ≫
          SheafOfModules.unitToPushforwardObjUnit M.f'.sharp := by
  have : (PresheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward
      (F := Opens.map M.f'.continuous) (φ := M.f'.sharp.hom)
  have : (SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint :=
    SheafOfModules.instIsRightAdjointPushforward
      (F := Opens.map M.f'.continuous) (φ := M.f'.sharp)
  let uf : SheafOfModules.unit M.S'.structureSheaf ⟶
      (ringedSpaceModulePushforward M.f').obj
        (SheafOfModules.unit M.X'.structureSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit M.f'.sharp
  let ut : SheafOfModules.unit M.S'.structureSheaf ⟶
      (ringedSpaceModulePushforward M.t).obj
        (SheafOfModules.unit M.S.structureSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit M.t.sharp
  let uf0 : SheafOfModules.unit M.S.structureSheaf ⟶
      (ringedSpaceModulePushforward M.f).obj
        (SheafOfModules.unit M.X.structureSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit M.f.sharp
  let qi : SheafOfModules.unit M.X'.structureSheaf ⟶
      (ringedSpaceModulePushforward M.i).obj
        (SheafOfModules.unit M.X.structureSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit M.i.sharp
  let K :=
    (ringedSpaceModulePushforwardCompIso M.f M.t).app
        (SheafOfModules.unit M.X.structureSheaf) ≪≫
      (eqToIso (congrArg (fun g => ringedSpaceModulePushforward g)
        M.commutes)).app (SheafOfModules.unit M.X.structureSheaf) ≪≫
      ((ringedSpaceModulePushforwardCompIso M.i M.f').app
        (SheafOfModules.unit M.X.structureSheaf)).symm
  have hft : SheafOfModules.unitToPushforwardObjUnit
      (RingedSpaceHom.comp M.f M.t).sharp =
      ut ≫ (ringedSpaceModulePushforward M.t).map uf0 ≫
        (ringedSpaceModulePushforwardCompIso M.f M.t).hom.app
          (SheafOfModules.unit M.X.structureSheaf) := by
    ext U
    have h := SheafOfModules.unitToPushforwardObjUnit_val_app_apply
      ((RingedSpaceHom.comp M.f M.t).sharp) (X := U)
      (1 : M.S'.structureSheaf.obj.obj U)
    change (ConcreteCategory.hom
      ((SheafOfModules.unitToPushforwardObjUnit
        (RingedSpaceHom.comp M.f M.t).sharp).val.app U))
      (1 : M.S'.structureSheaf.obj.obj U) = _
    rw [h]
    simp [ut, uf0, RingedSpaceHom.comp_sharp,
      Formalization.Books.Sheaves.Unit22.algebraicFMapComp] ; rfl
  have hif : SheafOfModules.unitToPushforwardObjUnit
      (RingedSpaceHom.comp M.i M.f').sharp =
      uf ≫ (ringedSpaceModulePushforward M.f').map qi ≫
        (ringedSpaceModulePushforwardCompIso M.i M.f').hom.app
          (SheafOfModules.unit M.X.structureSheaf) := by
    ext U
    have h := SheafOfModules.unitToPushforwardObjUnit_val_app_apply
      ((RingedSpaceHom.comp M.i M.f').sharp) (X := U)
      (1 : M.S'.structureSheaf.obj.obj U)
    change (ConcreteCategory.hom
      ((SheafOfModules.unitToPushforwardObjUnit
        (RingedSpaceHom.comp M.i M.f').sharp).val.app U))
      (1 : M.S'.structureSheaf.obj.obj U) = _
    rw [h]
    simp [uf, qi, RingedSpaceHom.comp_sharp,
      Formalization.Books.Sheaves.Unit22.algebraicFMapComp] ; rfl
  have hft' :
      (ut ≫ (ringedSpaceModulePushforward M.t).map uf0) ≫
          (ringedSpaceModulePushforwardCompIso M.f M.t).hom.app
            (SheafOfModules.unit M.X.structureSheaf) =
        SheafOfModules.unitToPushforwardObjUnit
          (RingedSpaceHom.comp M.f M.t).sharp := by
    rw [Category.assoc]
    simpa only [ringedSpaceModulePushforward, moduleSheafPushforwardAlong]
      using hft.symm
  have hif' :
      (uf ≫ (ringedSpaceModulePushforward M.f').map qi) ≫
          (ringedSpaceModulePushforwardCompIso M.i M.f').hom.app
            (SheafOfModules.unit M.X.structureSheaf) =
        SheafOfModules.unitToPushforwardObjUnit
          (RingedSpaceHom.comp M.i M.f').sharp := by
    rw [Category.assoc]
    simpa only [ringedSpaceModulePushforward, moduleSheafPushforwardAlong]
      using hif.symm
  have hcompat : uf ≫ (ringedSpaceModulePushforward M.f').map qi =
      ut ≫ (ringedSpaceModulePushforward M.t).map uf0 ≫ K.hom := by
    apply (cancel_mono
      ((ringedSpaceModulePushforwardCompIso M.i M.f').hom.app
        (SheafOfModules.unit M.X.structureSheaf))).1
    simp [K, Category.assoc]
    simp only [← Category.assoc]
    rw [hif', hft']
    have hunit (p q : RingedSpaceHom M.X M.S') (h : p = q) :
        SheafOfModules.unitToPushforwardObjUnit q.sharp =
          SheafOfModules.unitToPushforwardObjUnit p.sharp ≫
            eqToHom (congrArg (fun g : RingedSpaceHom M.X M.S' =>
              (SheafOfModules.pushforward (F := Opens.map g.continuous) g.sharp).obj
                (SheafOfModules.unit M.X.structureSheaf)) h) := by
      subst q
      simp
    simpa [ringedSpaceModulePushforward, moduleSheafPushforwardAlong] using
      hunit (RingedSpaceHom.comp M.f M.t)
      (RingedSpaceHom.comp M.i M.f') M.commutes
  let u : M.baseIdeal.carrier ⟶
      (ringedSpaceModulePushforward M.f').obj (SheafOfModules.unit M.X'.structureSheaf) :=
    M.baseIdeal.inclusion ≫ uf
  have hkernel : kernel qi = M.sourceIdeal.carrier := by
    rfl
  have hbase : M.baseIdeal.inclusion ≫ ut = 0 := by
    change kernel.ι ut ≫ ut = 0
    exact kernel.condition ut
  let u' :=
    (ringedSpaceModuleFMapPullbackHomEquiv M.f'
      M.baseIdeal.carrier (SheafOfModules.unit M.X'.structureSheaf)).symm
      u
  have hzero : u' ≫ qi = 0 := by
    apply (ringedSpaceModuleFMapPullbackHomEquiv M.f'
      M.baseIdeal.carrier ((ringedSpaceModulePushforward M.i).obj
        (SheafOfModules.unit M.X.structureSheaf))).injective
    rw [Adjunction.homEquiv_naturality_right]
    dsimp [u']
    simp only [Equiv.apply_symm_apply]
    change u ≫ (ringedSpaceModulePushforward M.f').map qi = 0
    change (M.baseIdeal.inclusion ≫ uf) ≫
      (ringedSpaceModulePushforward M.f').map qi = 0
    rw [Category.assoc, hcompat]
    rw [← Category.assoc, ← Category.assoc, hbase]
    simp
  let l := kernel.lift qi u' hzero
  let eI := ringedSpaceModuleFMapPullbackHomEquiv M.f'
    M.baseIdeal.carrier (kernel qi)
  refine ⟨eI l, ?_⟩
  change eI l ≫ (ringedSpaceModulePushforward M.f').map
      (kernel.ι qi) = u
  rw [← Adjunction.homEquiv_naturality_right]
  rw [kernel.lift_ι]
  exact (ringedSpaceModuleFMapPullbackHomEquiv M.f'
    M.baseIdeal.carrier (SheafOfModules.unit M.X'.structureSheaf)).apply_symm_apply u

/- A chosen source-facing representative of the induced map before extension
   of scalars. -/
noncomputable def inducedIdealFMap
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    M.baseIdeal.carrier ⟶
      (ringedSpaceModulePushforward M.f').obj M.sourceIdeal.carrier :=
  Classical.choose (exists_inducedIdealFMap M)

/-- The chosen induced `f'`-map is the canonical factorization through the
source kernel ideal. -/
theorem inducedIdealFMap_fac
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    inducedIdealFMap M ≫
        (ringedSpaceModulePushforward M.f').map M.sourceIdeal.inclusion =
      M.baseIdeal.inclusion ≫
        SheafOfModules.unitToPushforwardObjUnit M.f'.sharp :=
  Classical.choose_spec (exists_inducedIdealFMap M)

/- The adjoint-transposed map is the source's map
   `(f')^*𝓙 → 𝓘`. -/
noncomputable def inducedIdealMap
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    (ringedSpaceModulePullback M.f').obj M.baseIdeal.carrier ⟶
      M.sourceIdeal.carrier :=
  (ringedSpaceModuleFMapPullbackHomEquiv M.f' M.baseIdeal.carrier
    M.sourceIdeal.carrier).symm (inducedIdealFMap M)

/-- The induced ideal map exists as a morphism of `𝒪_{X'}`-modules. -/
theorem exists_inducedIdealMap
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    Nonempty
      ((ringedSpaceModulePullback M.f').obj M.baseIdeal.carrier ⟶
        M.sourceIdeal.carrier) :=
  ⟨inducedIdealMap M⟩

/-- A morphism of thickenings is strict when its induced ideal map is an
epimorphism. -/
def IsStrict
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] : Prop :=
  Epi (inducedIdealMap M)

/-- The first-order base ideal is an `𝒪_S`-module. -/
/- Proof roadmap for the `prove` stage:
   This is exactly `firstOrderThickening_kernel_is_module M.t ht` above.
   `M.baseIdeal` is an abbreviation for `thickeningIdeal M.t`, so
   `simpa only [baseIdeal]` (or simply `simpa`) turns that theorem into the
   displayed existential.  No choice of module or isomorphism needs to be
   reconstructed. -/
theorem firstOrder_baseIdeal_is_module
    (M : MorphismOfThickenings)
    (ht : IsFirstOrderThickening M.t) :
    ∃ J : Mod M.S.structureSheaf,
      Nonempty
        ((ringedSpaceModulePushforward M.t).obj J ≅ M.baseIdeal.carrier) := by
  simpa only [baseIdeal] using (firstOrderThickening_kernel_is_module M.t ht)

/-- After identifying the two square-zero ideals with modules on the reduced
spaces, maps `(f')^*𝓙 ⟶ 𝓘` are identified with maps `i_*f^*𝓙 ⟶ 𝓘`.

This is a Hom-set equivalence, not an isomorphism
`(f')^*𝓙 ≅ i_*f^*𝓙`: the latter is false in general (the first object can
retain a nontrivial action by the source thickening ideal). -/
/- Proof roadmap for the `prove` stage:
   1. Obtain `⟨I, ⟨eI⟩⟩` from
      `firstOrderThickening_kernel_is_module M.i hi`; thus
      `eI : (ringedSpaceModulePushforward M.i).obj I ≅
        M.sourceIdeal.carrier`.  Choose `eJ` from `hJ`.
   2. Obtain fully-faithful structures `ffi` and `fft` from
      `closedImmersion_pushforward_fullyFaithful` in
      `Formalization/Books/Modules/Unit13/ClosedImmersions.lean`, using
      `hi.toIsThickening.underlying_homeomorph.isClosedEmbedding` and
      `.structureSheaf_surjective` for `M.i`, and the corresponding fields of
      `M.t_isThickening` for `M.t`.  Use the explicit
      `Functor.FullyFaithful.homEquiv` from
      `Mathlib/CategoryTheory/Functor/FullyFaithful.lean`; no global Full or
      Faithful instances are required.
   3. Build an object isomorphism
      `K : t_* (f_* I) ≅ f'_* (i_* I)`.  Compose the app at `I` of
      `ringedSpaceModulePushforwardCompIso M.f M.t`, the `eqToIso` obtained
      by applying `(fun g => (ringedSpaceModulePushforward g).obj I)` to
      `M.commutes`, and the inverse app of
      `ringedSpaceModulePushforwardCompIso M.i M.f'`.  This fixes the
      otherwise easy-to-miss orientation of the commutative square.
   4. Compose the following equivalences in order:
      * `Iso.homCongr eJ.symm
          ((ringedSpaceModulePushforward M.f').mapIso eI.symm)`;
      * `Iso.homCongr (Iso.refl _) K.symm`;
      * `fft.homEquiv.symm`;
      * `(ringedSpaceModuleHomEquiv M.f J I).symm` from
        `Formalization/Books/Sheaves/Unit26/Infrastructure.lean`;
      * `ffi.homEquiv`;
      * `Iso.homCongr (Iso.refl _) eI`.
      The source and target of the composite are exactly the two Hom types in
      the statement.  The square-zero hypothesis on `M.i` is used to obtain
      `I`; `ht` is represented by the supplied `hJ` (normally obtained from
      `firstOrder_baseIdeal_is_module`).

   Known dead end: do not try to prove the previous object-level isomorphism.
   For rings `A' = k[ε]/(ε²) → A = k` and
   `B' = k[x]/(x²) → B = k`, with `ε ↦ 0`, one has
   `B' ⊗_{A'} (ε) ≅ B'` but `B ⊗_A (ε) ≅ k`; only maps from these objects
   into the square-zero source ideal are canonically identified. -/
theorem firstOrder_pullback_baseIdeal_iso
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    (J : Mod M.S.structureSheaf)
    (hJ : Nonempty
      ((ringedSpaceModulePushforward M.t).obj J ≅ M.baseIdeal.carrier))
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
      Nonempty
      ((M.baseIdeal.carrier ⟶
          (ringedSpaceModulePushforward M.f').obj M.sourceIdeal.carrier) ≃
        ((ringedSpaceModulePushforward M.i).obj
            ((ringedSpaceModulePullback M.f).obj J) ⟶
          M.sourceIdeal.carrier)) := by
  let hI := firstOrderThickening_kernel_is_module M.i hi
  let I := Classical.choose hI
  let eI : (ringedSpaceModulePushforward M.i).obj I ≅
      M.sourceIdeal.carrier :=
    Classical.choice (Classical.choose_spec hI)
  let eJ : (ringedSpaceModulePushforward M.t).obj J ≅
      M.baseIdeal.carrier :=
    Classical.choice hJ
  let ffi : (ringedSpaceModulePushforward M.i).FullyFaithful :=
    Classical.choice (closedImmersion_pushforward_fullyFaithful M.i
      hi.toIsThickening.underlying_homeomorph.isClosedEmbedding
      hi.toIsThickening.structureSheaf_surjective)
  let fft : (ringedSpaceModulePushforward M.t).FullyFaithful :=
    Classical.choice (closedImmersion_pushforward_fullyFaithful M.t
      ht.toIsThickening.underlying_homeomorph.isClosedEmbedding
      ht.toIsThickening.structureSheaf_surjective)
  let K :=
    (ringedSpaceModulePushforwardCompIso M.f M.t).app I ≪≫
      (eqToIso (congrArg (fun g => ringedSpaceModulePushforward g)
        M.commutes)).app I ≪≫
      ((ringedSpaceModulePushforwardCompIso M.i M.f').app I).symm
  let E :=
    (Iso.homCongr eJ.symm
      ((ringedSpaceModulePushforward M.f').mapIso eI.symm)).trans
      (Iso.homCongr (Iso.refl _) K.symm) |>.trans fft.homEquiv.symm |>.trans
      (ringedSpaceModuleHomEquiv M.f J I).symm |>.trans ffi.homEquiv |>.trans
      (Iso.homCongr (Iso.refl _) eI)
  exact ⟨E⟩

/-- The chosen first-order identification of the two presentations of an
ideal map. -/
noncomputable def firstOrderIdealMapHomEquiv
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    (J : Mod M.S.structureSheaf)
    (hJ : Nonempty
      ((ringedSpaceModulePushforward M.t).obj J ≅ M.baseIdeal.carrier))
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    (M.baseIdeal.carrier ⟶
        (ringedSpaceModulePushforward M.f').obj M.sourceIdeal.carrier) ≃
      ((ringedSpaceModulePushforward M.i).obj
          ((ringedSpaceModulePullback M.f).obj J) ⟶
        M.sourceIdeal.carrier) :=
  Classical.choice (firstOrder_pullback_baseIdeal_iso M hi ht J hJ)

/-- In the first-order case the induced ideal map can be expressed as a map
`f^*𝓙 → 𝓘`, after the canonical first-order identification. -/
/- Proof roadmap for the `prove` stage:
   Set `e := firstOrderIdealMapHomEquiv M hi ht J hJ` and
   `α := inducedIdealFMap M`.  Take `φ := e α`.  The required compatibility
   is exactly `Equiv.symm_apply_apply e α`.  Keeping this equation in the
   interface is what says that `φ` is the first-order presentation of the
   canonical kernel map; the former `Nonempty` Hom statement was vacuous
   because `0` inhabits every such Hom type. -/
theorem exists_firstOrder_idealMap
    (M : MorphismOfThickenings)
    (hi : IsFirstOrderThickening M.i)
    (ht : IsFirstOrderThickening M.t)
    (J : Mod M.S.structureSheaf)
    (hJ : Nonempty
      ((ringedSpaceModulePushforward M.t).obj J ≅ M.baseIdeal.carrier))
    [((SheafOfModules.pushforward (F := Opens.map M.f.continuous)
      M.f.sharp).IsRightAdjoint)]
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    ∃ φ : (ringedSpaceModulePushforward M.i).obj
          ((ringedSpaceModulePullback M.f).obj J) ⟶
        M.sourceIdeal.carrier,
      (firstOrderIdealMapHomEquiv M hi ht J hJ).symm φ =
        inducedIdealFMap M := by
  let e := firstOrderIdealMapHomEquiv M hi ht J hJ
  refine ⟨e (inducedIdealFMap M), ?_⟩
  exact e.symm_apply_apply (inducedIdealFMap M)

end MorphismOfThickenings

/-! ## Strictness and cartesian squares -/

/-- The strictness criterion: the square of ringed spaces is cartesian exactly
when the induced map of ideals is an epimorphism. -/
theorem strict_iff_cartesian
    (M : MorphismOfThickenings)
    [((SheafOfModules.pushforward (F := Opens.map M.f'.continuous)
      M.f'.sharp).IsRightAdjoint)] :
    MorphismOfThickenings.IsStrict M ↔
      @IsPullback (RingedSpace.{v}) _ M.X M.X' M.S M.S'
        M.i M.f M.f' M.t := by
  sorry

end

end Formalization.Books.Defos.Unit03
