import Formalization.Books.Descent.Unit33.PropertiesOfMorphismsOfGerms
import Formalization.Books.Algebra.Unit39.FlatModules

/-!
# Descent, Chapter 33

This chapter formalizes “Properties of morphisms of germs local on
source-and-target”. The imported section file contains the chosen-germ
interfaces and real constructions; the theorem statements below follow the
source order.
-/

universe u

open CategoryTheory
open AlgebraicGeometry

namespace SchemeGerm

private theorem flat_iff_of_etale_square
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (k : T →+* U)
    (comm : h.comp f = k.comp g)
    (hgFlat : RingHom.Flat g) (hgUnramified : RingHom.FormallyUnramified g)
    (hgEssFiniteType : RingHom.EssFiniteType g)
    (hhFlat : RingHom.Flat h)
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T] [IsLocalRing U]
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h] [IsLocalHom k] :
    f.Flat ↔ k.Flat := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R T := g.toAlgebra
  let _ : Algebra T U := k.toAlgebra
  let _ : Algebra R U := (k.comp g).toAlgebra
  let _ : Algebra S U := h.toAlgebra
  let _ : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq fun x => rfl
  let _ : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq fun x => by
    simpa only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] using
      (congrArg (fun q => q x) comm).symm
  have hflat : Module.Flat S U := by
    simpa [RingHom.Flat] using hhFlat
  let _ : Module.Flat S U := hflat
  have hfaithful : Module.FaithfullyFlat S U :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have gflat : Module.Flat R T := by
    simpa [RingHom.Flat] using hgFlat
  let _ : Module.Flat R T := gflat
  have gformallyUnramified : Algebra.FormallyUnramified R T := by
    simpa [RingHom.FormallyUnramified] using hgUnramified
  let _ : Algebra.FormallyUnramified R T := gformallyUnramified
  have gEssFiniteType : Algebra.EssFiniteType R T := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact hgEssFiniteType
  let _ : Algebra.EssFiniteType R T := gEssFiniteType
  constructor
  · intro hf
    have hfmod : Module.Flat R S := by
      simpa [RingHom.Flat] using hf
    let _ : Module.Flat R S := hfmod
    let _ : Algebra S (TensorProduct R S T) := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra T (TensorProduct R S T) := Algebra.TensorProduct.rightAlgebra
    have hP : Algebra.FormallyUnramified S (TensorProduct R S T) := by
      infer_instance
    let sAlg : S →ₐ[R] U :=
      { toRingHom := h
        commutes' := fun x => by
          change h (f x) = k (g x)
          exact congrArg (fun q => q x) comm }
    let tAlg : T →ₐ[R] U :=
      { toRingHom := k
        commutes' := fun _ => rfl }
    let pAlg : (TensorProduct R S T) →ₐ[R] U :=
      Algebra.pushoutDesc _ sAlg tAlg (fun x y => mul_comm _ _)
    let pAlgS : (TensorProduct R S T) →ₐ[S] U :=
      { toRingHom := pAlg.toRingHom
        commutes' := by
          intro x
          change pAlg (algebraMap S (TensorProduct R S T) x) = sAlg x
          exact Algebra.pushoutDesc_left (TensorProduct R S T) sAlg tAlg
            (fun x y => mul_comm _ _) x }
    let _ : Algebra (TensorProduct R S T) U := pAlgS.toAlgebra
    let _ : IsScalarTower S (TensorProduct R S T) U :=
      IsScalarTower.of_algebraMap_eq fun x => (pAlgS.commutes x).symm
    let _ : Algebra.FormallyUnramified S (TensorProduct R S T) := hP
    have hpflat : RingHom.Flat pAlgS.toRingHom := by
      simpa [RingHom.Flat] using
        (Algebra.FormallyUnramified.flat_of_restrictScalars
          (R := S) (S := TensorProduct R S T) (M := U))
    have htensor : RingHom.Flat
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)).toRingHom := by
      change Module.Flat T (TensorProduct R S T)
      have hbase : IsBaseChange T
          (((Algebra.TensorProduct.commRight R T S).toLinearMap.restrictScalars R).comp
            (TensorProduct.mk R T S 1)) :=
        IsBaseChange.of_equiv (Algebra.TensorProduct.commRight R T S).toLinearEquiv
          (fun x => by simp)
      exact Module.Flat.isBaseChange (R := R) (S := T) (M := S)
        (N := TensorProduct R S T) hbase
    have hcomp : pAlgS.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)).toRingHom = k := by
      apply RingHom.ext
      intro x
      simpa [pAlgS, pAlg, tAlg, RingHom.algebraMap_toAlgebra] using
        (Algebra.pushoutDesc_right (TensorProduct R S T) sAlg tAlg
          (fun x y => mul_comm _ _) x)
    rw [← hcomp]
    exact RingHom.Flat.comp htensor hpflat
  · intro hk
    have hkflat : Module.Flat T U := by
      simpa [RingHom.Flat] using hk
    let _ : Module.Flat T U := hkflat
    have hcomp : Module.Flat R U := Module.Flat.trans R T U
    have hresult : Module.Flat R S :=
      Formalization.Books.Algebra.Unit39.flat_permanence hcomp hfaithful
    simpa [RingHom.Flat] using hresult

private theorem stalkMap_comp_eqToHom
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) (y : Y) (z : Z)
    (hf : f.base x = y) (hg : g.base y = z) :
    eqToHom (congrArg (fun w => Z.presheaf.stalk w) hg.symm) ≫
        g.stalkMap y ≫
        eqToHom (congrArg (fun w => Y.presheaf.stalk w) hf.symm) ≫
        f.stalkMap x =
      eqToHom (congrArg (fun w => Z.presheaf.stalk w)
        (hg.symm.trans (congrArg g.base hf.symm))) ≫
        (f ≫ g).stalkMap x := by
  subst y
  subst z
  simp [Scheme.Hom.stalkMap_comp]

/-- Source Lemma `lemma-local-source-target-global-implies-local`. -/
lemma globalProperty_implies_localGermProperty
    (P : SchemeMorphismProperty)
    (hP : IsEtaleLocalOnSourceAndTargetScheme P) :
    IsEtaleLocalOnSourceAndTarget (germPropertyOfSchemeProperty P) := by
  sorry

/-- Source Lemma `lemma-local-source-target-local-implies-global`. -/
lemma localGermProperty_implies_globalProperty
    (P : SchemeMorphismProperty)
    (hP : IsEtaleLocalOnSourceAndTargetScheme P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P f ↔ ∀ x : X, germPropertyOfSchemeProperty P (Hom.ofSchemeHom f x) := by
  sorry

/-! ### Flatness at a point -/

/-- Source Lemma `lemma-flat-at-point`. -/
lemma flatAtPoint_isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget (fun {_X _Y} f => Hom.IsFlatAtPoint f) := by
  unfold IsEtaleLocalOnSourceAndTarget Hom.IsEtale CommSquare
  intro U' U V' V a b h' h comm ha hb
  simp only [Hom.IsFlatAtPoint]
  let _ : Etale a.map := ha
  let _ : Etale b.map := hb
  have haFlat : RingHom.Flat (a.map.stalkMap U'.point).hom :=
    AlgebraicGeometry.Flat.stalkMap a.map U'.point
  have hbFlat : RingHom.Flat (b.map.stalkMap V'.point).hom :=
    AlgebraicGeometry.Flat.stalkMap b.map V'.point
  have hbEssFiniteType : RingHom.EssFiniteType (b.map.stalkMap V'.point).hom :=
    AlgebraicGeometry.LocallyOfFiniteType.stalkMap b.map V'.point
  have hbUnramified : RingHom.FormallyUnramified (b.map.stalkMap V'.point).hom :=
    AlgebraicGeometry.FormallyUnramified.stalkMap b.map V'.point
  let e_h : V.carrier.presheaf.stalk V.point =
      V.carrier.presheaf.stalk (h.map U.point) :=
    congrArg (fun x => V.carrier.presheaf.stalk x) h.map_point.symm
  let e_b : V.carrier.presheaf.stalk V.point =
      V.carrier.presheaf.stalk (b.map V'.point) :=
    congrArg (fun x => V.carrier.presheaf.stalk x) b.map_point.symm
  let e_a : U.carrier.presheaf.stalk U.point =
      U.carrier.presheaf.stalk (a.map U'.point) :=
    congrArg (fun x => U.carrier.presheaf.stalk x) a.map_point.symm
  let e_h' : V'.carrier.presheaf.stalk V'.point =
      V'.carrier.presheaf.stalk (h'.map U'.point) :=
    congrArg (fun x => V'.carrier.presheaf.stalk x) h'.map_point.symm
  let f₀ : (V.carrier.presheaf.stalk V.point) →+*
      (U.carrier.presheaf.stalk U.point) :=
    (eqToHom e_h ≫ h.map.stalkMap U.point).hom
  let g₀ : (V.carrier.presheaf.stalk V.point) →+*
      (V'.carrier.presheaf.stalk V'.point) :=
    (eqToHom e_b ≫ b.map.stalkMap V'.point).hom
  let h₀ : (U.carrier.presheaf.stalk U.point) →+*
      (U'.carrier.presheaf.stalk U'.point) :=
    (eqToHom e_a ≫ a.map.stalkMap U'.point).hom
  let k₀ : (V'.carrier.presheaf.stalk V'.point) →+*
      (U'.carrier.presheaf.stalk U'.point) :=
    (eqToHom e_h' ≫ h'.map.stalkMap U'.point).hom
  have e_b_bij : Function.Bijective (eqToHom e_b).hom :=
    ConcreteCategory.bijective_of_isIso (eqToHom e_b)
  have e_a_bij : Function.Bijective (eqToHom e_a).hom :=
    ConcreteCategory.bijective_of_isIso (eqToHom e_a)
  have e_h_bij : Function.Bijective (eqToHom e_h).hom :=
    ConcreteCategory.bijective_of_isIso (eqToHom e_h)
  have e_h'_bij : Function.Bijective (eqToHom e_h').hom :=
    ConcreteCategory.bijective_of_isIso (eqToHom e_h')
  let qStalk : ∀ (q : {q : U'.carrier ⟶ V.carrier // q U'.point = V.point}),
      V.carrier.presheaf.stalk V.point ⟶ U'.carrier.presheaf.stalk U'.point :=
    fun q =>
      eqToHom (congrArg (fun z => V.carrier.presheaf.stalk z) q.property.symm) ≫
        q.1.stalkMap U'.point
  let qleft : {q : U'.carrier ⟶ V.carrier // q U'.point = V.point} :=
    ⟨a.map ≫ h.map, by simp [a.map_point, h.map_point]⟩
  let qright : {q : U'.carrier ⟶ V.carrier // q U'.point = V.point} :=
    ⟨h'.map ≫ b.map, by simp [h'.map_point, b.map_point]⟩
  have comm_fixed : qStalk qleft = qStalk qright := by
    apply congrArg qStalk
    exact Subtype.ext comm
  have comm₀ : h₀.comp f₀ = k₀.comp g₀ := by
    have hleft : h₀.comp f₀ = (qStalk qleft).hom := by
      apply congrArg CommRingCat.Hom.hom
      change
        (eqToHom e_h ≫ h.map.stalkMap U.point) ≫
            (eqToHom e_a ≫ a.map.stalkMap U'.point) =
          qStalk qleft
      have hqprop :
          qleft.property.symm =
            h.map_point.symm.trans (congrArg h.map a.map_point.symm) := by
        apply Subsingleton.elim
      have hcomp := stalkMap_comp_eqToHom a.map h.map
        U'.point U.point V.point a.map_point h.map_point
      simpa [qStalk, qleft, e_h, e_a, hqprop, Scheme.Hom.stalkMap_comp,
        Category.assoc] using hcomp
    have hright : k₀.comp g₀ = (qStalk qright).hom := by
      apply congrArg CommRingCat.Hom.hom
      change
        (eqToHom e_b ≫ b.map.stalkMap V'.point) ≫
            (eqToHom e_h' ≫ h'.map.stalkMap U'.point) =
          qStalk qright
      have hqprop :
          qright.property.symm =
            b.map_point.symm.trans (congrArg b.map h'.map_point.symm) := by
        apply Subsingleton.elim
      have hcomp := stalkMap_comp_eqToHom h'.map b.map
        U'.point V'.point V.point h'.map_point b.map_point
      simpa [qStalk, qright, e_b, e_h', hqprop,
        Scheme.Hom.stalkMap_comp, Category.assoc] using hcomp
    exact hleft.trans ((congrArg CommRingCat.Hom.hom comm_fixed).trans hright.symm)
  have result := flat_iff_of_etale_square
    (f := f₀) (g := g₀) (h := h₀) (k := k₀) comm₀
    (RingHom.Flat.comp (RingHom.Flat.of_bijective e_b_bij) hbFlat)
    (RingHom.FormallyUnramified.comp
      (RingHom.FormallyUnramified.of_surjective e_b_bij.2) hbUnramified)
    (RingHom.EssFiniteType.comp
      (RingHom.FiniteType.of_surjective (eqToHom e_b).hom e_b_bij.2).essFiniteType
      hbEssFiniteType)
    (RingHom.Flat.comp (RingHom.Flat.of_bijective e_a_bij) haFlat)
  have hf_equiv : f₀.Flat ↔ (h.map.stalkMap U.point).hom.Flat := by
    change ((h.map.stalkMap U.point).hom.comp (eqToHom e_h).hom).Flat ↔ _
    exact RingHom.Flat.comp_iff_of_bijective_right e_h_bij
  have hk_equiv : k₀.Flat ↔ (h'.map.stalkMap U'.point).hom.Flat := by
    change ((h'.map.stalkMap U'.point).hom.comp (eqToHom e_h').hom).Flat ↔ _
    exact RingHom.Flat.comp_iff_of_bijective_right e_h'_bij
  exact hf_equiv.symm.trans (result.trans hk_equiv)

/-! ### Étale morphisms on fibres -/

/-- Source Lemma `lemma-etale-on-fiber`. -/
lemma etaleOnFibre
    {U' U V' V : Scheme.{u}}
    (a : U' ⟶ U) (b : V' ⟶ V) (h' : U' ⟶ V') (h : U ⟶ V)
    (comm : a ≫ h = h' ≫ b) (ha : Etale a) (hb : Etale b) (v' : V') :
    Etale (fibreMap a b h' h comm v') := by
  sorry

/-! ### Dimension of the local ring of a fibre -/

/-- Source Lemma `lemma-dimension-local-ring-fibre`. -/
lemma fibreLocalRingDimension_isEtaleLocalOnSourceAndTarget (d : ℕ∞) :
    IsEtaleLocalOnSourceAndTarget
      (fun {X Y} f => Hom.fibreLocalRingDimension f = d) := by
  sorry

/-! ### Transcendence degree at a point -/

/-- Source Lemma `lemma-transcendence-degree-at-point`.

The parameter is a `Cardinal`, which is the canonical Mathlib codomain of
transcendence degree and also covers extensions of uncountable transcendence
degree.
-/
lemma residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget (r : Cardinal) :
    IsEtaleLocalOnSourceAndTarget
      (fun {X Y} f => Hom.residueFieldTranscendenceDegree f = r) := by
  sorry

/-! ### Dimension at a point -/

/-- Source Lemma `lemma-dimension-at-point`. -/
lemma fibrePointDimension_isEtaleLocalOnSourceAndTarget (d : ℕ∞) :
    IsEtaleLocalOnSourceAndTarget
      (fun {X Y} f => Hom.fibrePointDimension f = d) := by
  sorry

end SchemeGerm
