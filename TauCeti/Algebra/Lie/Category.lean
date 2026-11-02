/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# The category of Lie algebras finite as modules

`TauCeti.FGLieAlgCat R` bundles Lie algebras whose underlying `R`-module is finitely
generated. Its morphisms are Lie-algebra homomorphisms. Over a field, its objects are precisely
the finite-dimensional Lie algebras.

The concrete-category setup follows Mathlib's `AlgCat`, using a wrapper around the underlying
Lie homomorphism and the canonical `ConcreteCategory.hom` projection.

## Main definitions and results

* `TauCeti.FGLieAlgCat`: the bundled category, with object constructor `of`.
* `TauCeti.FGLieAlgCat.Hom.hom` and `TauCeti.FGLieAlgCat.ofHom`: conversions between
  categorical morphisms and Lie homomorphisms.
* `TauCeti.FGLieAlgCat.hom_id`, `TauCeti.FGLieAlgCat.hom_comp`: identity and composition
  of the underlying Lie homomorphisms.
* `TauCeti.FGLieAlgCat.hom_ofHom`, `TauCeti.FGLieAlgCat.ofHom_hom`: the conversion laws.
* `TauCeti.FGLieAlgCat.ofHom_id`, `TauCeti.FGLieAlgCat.ofHom_comp`: conversion preserves
  identities and composition.
* `TauCeti.FGLieAlgCat.hom_ext`: equality of morphisms from their Lie homomorphisms.
* `LieEquiv.toFGLieAlgCatIso` and `CategoryTheory.Iso.toLieEquiv`: conversion between Lie
  equivalences and categorical isomorphisms, with inverse-application and round-trip laws.

## References

* Mathlib's `Mathlib.Algebra.Category.AlgCat.Basic`, for the concrete-category construction.
* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Corollary 3.44, for the real finite-dimensional category.
-/

public section

open CategoryTheory

universe u r

namespace TauCeti

/-- Lie algebras over `R` whose underlying module is finitely generated. -/
structure FGLieAlgCat (R : Type r) [CommRing R] where
  /-- The underlying type. -/
  carrier : Type u
  /-- The additive group and Lie bracket. -/
  [lieRing : LieRing carrier]
  /-- The Lie algebra structure over `R`. -/
  [lieAlgebra : LieAlgebra R carrier]
  /-- Finite generation of the underlying module. -/
  [finite : Module.Finite R carrier]

attribute [instance] FGLieAlgCat.lieRing FGLieAlgCat.lieAlgebra FGLieAlgCat.finite

instance {R : Type r} [CommRing R] : CoeSort (FGLieAlgCat.{u} R) (Type u) :=
  ⟨FGLieAlgCat.carrier⟩

namespace FGLieAlgCat

variable {R : Type r} [CommRing R]

/-- Bundle a Lie algebra whose underlying module is finitely generated. -/
abbrev of (R : Type r) [CommRing R] (L : Type u) [LieRing L] [LieAlgebra R L]
    [Module.Finite R L] : FGLieAlgCat R := ⟨L⟩

/-- A Lie homomorphism between Lie algebras finite as modules. -/
@[ext]
structure Hom (L K : FGLieAlgCat.{u} R) where
  /-- The underlying Lie homomorphism. Use `Hom.hom` to access it. -/
  hom' : L →ₗ⁅R⁆ K

instance : Category (FGLieAlgCat.{u} R) where
  Hom L K := Hom L K
  id _ := ⟨1⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (FGLieAlgCat.{u} R) (fun L K ↦ L →ₗ⁅R⁆ K) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {L K M : FGLieAlgCat.{u} R}

/-- The Lie homomorphism underlying a categorical morphism. -/
abbrev Hom.hom (f : L ⟶ K) : L →ₗ⁅R⁆ K := ConcreteCategory.hom f

/-- Regard a Lie homomorphism as a categorical morphism. -/
abbrev ofHom (f : L →ₗ⁅R⁆ K) : L ⟶ K := ConcreteCategory.ofHom f

/-- The underlying homomorphism of the identity is the identity Lie homomorphism. -/
@[simp]
theorem hom_id : (𝟙 L : L ⟶ L).hom = 1 := rfl

/-- The underlying homomorphism of a composite is the composite of the underlying maps. -/
@[simp]
theorem hom_comp (f : L ⟶ K) (g : K ⟶ M) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- Constructing a categorical morphism preserves its underlying Lie homomorphism. -/
@[simp]
theorem hom_ofHom (f : L →ₗ⁅R⁆ K) : (ofHom f).hom = f := rfl

/-- A categorical morphism is recovered from its underlying Lie homomorphism. -/
@[simp]
theorem ofHom_hom (f : L ⟶ K) : ofHom f.hom = f := rfl

/-- Converting the identity Lie homomorphism gives the identity categorical morphism. -/
@[simp]
theorem ofHom_id : ofHom (1 : L →ₗ⁅R⁆ L) = 𝟙 L := rfl

/-- Converting a composite Lie homomorphism gives the composite categorical morphism. -/
@[simp]
theorem ofHom_comp (f : L →ₗ⁅R⁆ K) (g : K →ₗ⁅R⁆ M) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

/-- Categorical morphisms are equal if their underlying Lie homomorphisms agree. -/
@[ext]
theorem hom_ext {f g : L ⟶ K} (h : f.hom = g.hom) : f = g := ConcreteCategory.ext h

/-- The inverse of a categorical isomorphism cancels its forward map. -/
theorem inv_hom_apply (e : L ≅ K) (x : L) : e.inv.hom (e.hom.hom x) = x := by
  exact ConcreteCategory.congr_hom e.hom_inv_id x

/-- The forward map of a categorical isomorphism cancels its inverse. -/
theorem hom_inv_apply (e : L ≅ K) (x : K) : e.hom.hom (e.inv.hom x) = x := by
  exact ConcreteCategory.congr_hom e.inv_hom_id x

end FGLieAlgCat

end TauCeti

variable {R : Type r} [CommRing R]

/-- A Lie equivalence gives an isomorphism of the associated Lie algebra objects. -/
def LieEquiv.toFGLieAlgCatIso {L K : Type u} [LieRing L] [LieAlgebra R L] [Module.Finite R L]
    [LieRing K] [LieAlgebra R K] [Module.Finite R K] (e : L ≃ₗ⁅R⁆ K) :
    TauCeti.FGLieAlgCat.of R L ≅ TauCeti.FGLieAlgCat.of R K where
  hom := TauCeti.FGLieAlgCat.ofHom e.toLieHom
  inv := TauCeti.FGLieAlgCat.ofHom e.symm.toLieHom
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

/-- The forward Lie homomorphism of the categorical isomorphism is the original map. -/
@[simp]
theorem LieEquiv.toFGLieAlgCatIso_hom_hom {L K : Type u} [LieRing L] [LieAlgebra R L]
    [Module.Finite R L] [LieRing K] [LieAlgebra R K] [Module.Finite R K]
    (e : L ≃ₗ⁅R⁆ K) : e.toFGLieAlgCatIso.hom.hom = e.toLieHom := by
  simp only [LieEquiv.toFGLieAlgCatIso, TauCeti.FGLieAlgCat.hom_ofHom]

/-- The inverse Lie homomorphism of the categorical isomorphism is the inverse map. -/
@[simp]
theorem LieEquiv.toFGLieAlgCatIso_inv_hom {L K : Type u} [LieRing L] [LieAlgebra R L]
    [Module.Finite R L] [LieRing K] [LieAlgebra R K] [Module.Finite R K]
    (e : L ≃ₗ⁅R⁆ K) : e.toFGLieAlgCatIso.inv.hom = e.symm.toLieHom := by
  simp only [LieEquiv.toFGLieAlgCatIso, TauCeti.FGLieAlgCat.hom_ofHom]

/-- An isomorphism of Lie algebra objects gives a Lie equivalence of their carriers. -/
def CategoryTheory.Iso.toLieEquiv {L K : TauCeti.FGLieAlgCat.{u} R} (e : L ≅ K) :
    L ≃ₗ⁅R⁆ K :=
  { e.hom.hom with
    invFun := e.inv.hom
    left_inv := TauCeti.FGLieAlgCat.inv_hom_apply e
    right_inv := TauCeti.FGLieAlgCat.hom_inv_apply e }

/-- The Lie homomorphism of an isomorphism's Lie equivalence is its forward map. -/
@[simp]
theorem CategoryTheory.Iso.toLieEquiv_toLieHom {L K : TauCeti.FGLieAlgCat.{u} R}
    (e : L ≅ K) : e.toLieEquiv.toLieHom = e.hom.hom := by
  simp only [CategoryTheory.Iso.toLieEquiv]

/-- The Lie equivalence associated to a categorical isomorphism applies its forward map. -/
@[simp]
theorem CategoryTheory.Iso.toLieEquiv_apply {L K : TauCeti.FGLieAlgCat.{u} R}
    (e : L ≅ K) (x : L) : e.toLieEquiv x = e.hom.hom x := by
  simp only [← LieEquiv.coe_toLieHom, toLieEquiv_toLieHom]

/-- The inverse Lie equivalence associated to an isomorphism applies its inverse map. -/
@[simp]
theorem CategoryTheory.Iso.toLieEquiv_symm_apply {L K : TauCeti.FGLieAlgCat.{u} R}
    (e : L ≅ K) (x : K) : e.toLieEquiv.symm x = e.inv.hom x := by
  simp only [LieEquiv.symm_apply_eq, toLieEquiv_apply, TauCeti.FGLieAlgCat.hom_inv_apply]

/-- Converting a Lie equivalence to a categorical isomorphism and back recovers it. -/
@[simp]
theorem LieEquiv.toFGLieAlgCatIso_toLieEquiv {L K : Type u} [LieRing L] [LieAlgebra R L]
    [Module.Finite R L] [LieRing K] [LieAlgebra R K] [Module.Finite R K]
    (e : L ≃ₗ⁅R⁆ K) : e.toFGLieAlgCatIso.toLieEquiv = e := by
  ext x
  rw [CategoryTheory.Iso.toLieEquiv_apply, LieEquiv.toFGLieAlgCatIso_hom_hom]
  exact congrFun (LieEquiv.coe_toLieHom e) x

/-- Converting a categorical isomorphism to a Lie equivalence and back recovers it. -/
@[simp]
theorem CategoryTheory.Iso.toLieEquiv_toFGLieAlgCatIso {L K : TauCeti.FGLieAlgCat.{u} R}
    (e : L ≅ K) : e.toLieEquiv.toFGLieAlgCatIso = e := by
  apply CategoryTheory.Iso.ext
  apply TauCeti.FGLieAlgCat.hom_ext
  simp only [LieEquiv.toFGLieAlgCatIso_hom_hom, CategoryTheory.Iso.toLieEquiv_toLieHom]
