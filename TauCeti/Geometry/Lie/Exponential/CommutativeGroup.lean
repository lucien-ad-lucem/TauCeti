/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Generation
public import TauCeti.Geometry.Lie.Exponential.Trotter
public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Topology.Algebra.Module.Submodule
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Topology.Algebra.Module.CompactQuotient
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Algebra.Group.Neighborhood
import TauCeti.Topology.Algebra.ContinuousMonoidHom.QuotientKerEquiv

/-!
# The exponential map of a commutative Lie group

For a commutative finite-dimensional real Lie group `G` the exponential map `lieExp : 𝔤 → G` is a
homomorphism from the additive group of the Lie algebra. Its image is the identity component of
`G`; when `G` is preconnected, `lieExp` is surjective. Its kernel is a discrete subgroup of `𝔤`.

The exponential of a commutative `G` is moreover an open map, so for a preconnected `G` it
identifies `G` with the quotient of `𝔤` by the kernel as topological groups. When `G` is compact
the quotient of `𝔤` by the kernel is the identity component, hence compact, so the kernel spans
`𝔤` and is a lattice of full rank: a compact connected commutative Lie group is the quotient of
its Lie algebra by a lattice. Choosing a `ℤ`-basis of the lattice identifies that quotient with
the standard torus `(ℝ ⧸ ℤ)^r`, so a compact connected commutative Lie group of dimension `r` is
a product of `r` circles, as topological groups.

## Main results

* `TauCeti.lieExp_add`: the exponential of a commutative Lie group is a homomorphism.
* `TauCeti.lieExpAddMonoidHom`: that homomorphism, bundled.
* `TauCeti.range_lieExp`: the exponential image is the identity component.
* `TauCeti.lieExp_surjective_of_preconnectedSpace`: the exponential of a preconnected
  commutative Lie group is surjective.
* `TauCeti.discreteTopology_ker_lieExpAddMonoidHom`: the kernel of the exponential is discrete.
* `TauCeti.isOpenMap_lieExpAddMonoidHom` and `TauCeti.isOpenMap_lieExp`: the exponential of a
  commutative Lie group is an open map.
* `TauCeti.lieExpAddMonoidHom_surjective_of_preconnectedSpace`: the exponential homomorphism of
  a preconnected commutative Lie group is surjective.
* `TauCeti.lieExpQuotientKerContinuousAddEquiv`: a preconnected commutative Lie group is the
  quotient of its Lie algebra by the kernel of the exponential, as topological groups.
* `TauCeti.compactSpace_quotient_ker_lieExpAddMonoidHom`: for a compact commutative Lie group
  the quotient of the Lie algebra by the kernel of the exponential is compact.
* `TauCeti.span_ker_lieExpAddMonoidHom_eq_top`, `TauCeti.isZLattice_ker_lieExpAddMonoidHom` and
  `TauCeti.finrank_ker_lieExpAddMonoidHom`: for a compact commutative Lie group the kernel of the
  exponential is a lattice of full rank in the Lie algebra.
* `TauCeti.lieExpLatticeBasis`: a `ℤ`-basis of the kernel of the exponential, which is an
  `ℝ`-basis of the Lie algebra.
* `TauCeti.torusContinuousMulEquiv`: a compact connected commutative Lie group of dimension `r` is
  isomorphic to the product of `r` circles, as topological groups.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 20
  (The Exponential Map), § One-Parameter Subgroups and the Exponential Map.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map), Theorem (3.6) and Lemma (3.8).
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 15 (Tori), Proposition 15.3.
-/

public section

noncomputable section

namespace TauCeti

open Filter Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothnessThree

variable [IsMulCommutative G]

/-- **The exponential of a commutative Lie group is a homomorphism** from the additive group of
the Lie algebra. -/
@[simp]
theorem lieExp_add (X Y : LeftInvariantDerivation I G) :
    lieExp (X + Y) = lieExp X * lieExp Y :=
  lieExp_add_of_commute (I := I) (G := G) fun _ => mul_comm' _ _

/-- The exponential of a commutative Lie group, as a homomorphism from the additive group of the
Lie algebra to the group written additively. -/
def lieExpAddMonoidHom : LeftInvariantDerivation I G →+ Additive G where
  toFun X := Additive.ofMul (lieExp X)
  map_zero' := by rw [lieExp_zero, ofMul_one]
  map_add' X Y := by rw [lieExp_add, ofMul_mul]

@[simp]
theorem lieExpAddMonoidHom_apply (X : LeftInvariantDerivation I G) :
    lieExpAddMonoidHom (I := I) (G := G) X = Additive.ofMul (lieExp X) := by
  rw [lieExpAddMonoidHom]
  rfl

/-- The exponential homomorphism is the exponential, viewed as a map into `Additive G`. -/
theorem coe_lieExpAddMonoidHom :
    ⇑(lieExpAddMonoidHom (I := I) (G := G)) = Additive.ofMul ∘ lieExp (I := I) :=
  funext fun X => lieExpAddMonoidHom_apply X

/-- Membership in the kernel of the exponential. -/
theorem mem_ker_lieExpAddMonoidHom {X : LeftInvariantDerivation I G} :
    X ∈ (lieExpAddMonoidHom (I := I) (G := G)).ker ↔ lieExp X = 1 := by
  -- Not a `simp` lemma: `simp` already proves it from `AddMonoidHom.mem_ker`,
  -- `lieExpAddMonoidHom_apply` and `ofMul_eq_zero`, so the simpNF linter rejects the attribute.
  rw [AddMonoidHom.mem_ker, lieExpAddMonoidHom_apply, ofMul_eq_zero]

/-- **The kernel of the exponential of a commutative Lie group is a discrete subgroup** of the
Lie algebra. -/
instance discreteTopology_ker_lieExpAddMonoidHom :
    DiscreteTopology (lieExpAddMonoidHom (I := I) (G := G)).ker := by
  -- The exponential is injective near `0`, so `0` is isolated in the kernel.
  apply discreteTopology_of_isOpen_singleton_zero
  obtain ⟨U, hU, hUopen, h0⟩ :=
    eventually_nhds_iff.mp (eventually_lieLog_lieExp (I := I) (G := G))
  have hsingleton : ({0} : Set (lieExpAddMonoidHom (I := I) (G := G)).ker) =
      Subtype.val ⁻¹' U := by
    ext ⟨X, hX⟩
    rw [mem_ker_lieExpAddMonoidHom] at hX
    simp only [mem_singleton_iff, mem_preimage, Subtype.ext_iff, ZeroMemClass.coe_zero]
    exact ⟨fun h => by rw [h]; exact h0, fun h => by rw [← hU X h, hX, lieLog_one]⟩
  rw [hsingleton]
  exact hUopen.preimage continuous_subtype_val

/-- The exponential homomorphism is continuous. -/
@[fun_prop]
theorem continuous_lieExpAddMonoidHom : Continuous (lieExpAddMonoidHom (I := I) (G := G)) :=
  continuous_ofMul.comp (contMDiff_lieExp (I := I) (G := G)).continuous

variable [IsTopologicalGroup G]

/-- **The exponential homomorphism of a commutative Lie group is an open map.** -/
theorem isOpenMap_lieExpAddMonoidHom : IsOpenMap (lieExpAddMonoidHom (I := I) (G := G)) := by
  -- A homomorphism of topological groups is open as soon as it is open at the identity, and near
  -- the identity the logarithm is a continuous right inverse of the exponential.
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero]
  intro s hs
  rw [Filter.mem_map] at hs
  have hlog : ContinuousAt (lieLog (I := I) (G := G) ∘ Additive.toMul) (0 : Additive G) :=
    (contMDiffAt_lieLog_one (I := I) (G := G)).continuousAt.comp_of_eq
      continuous_toMul.continuousAt toMul_zero
  filter_upwards [hlog.preimage_mem_nhds
      (by simpa only [Function.comp_apply, toMul_zero, lieLog_one] using hs),
    continuous_toMul.continuousAt.eventually (eventually_lieExp_lieLog (I := I) (G := G))]
    with g hg hexp
  simp only [Set.mem_preimage, Function.comp_apply, lieExpAddMonoidHom_apply, hexp, ofMul_toMul]
    at hg
  exact hg

/-- **The exponential of a commutative Lie group is an open map.** -/
theorem isOpenMap_lieExp : IsOpenMap (lieExp (I := I) (G := G)) := by
  have hopen := isOpenMap_lieExpAddMonoidHom (I := I) (G := G)
  rw [coe_lieExpAddMonoidHom] at hopen
  exact isOpenMap_toMul.comp hopen

/-- **The exponential image of a commutative Lie group is the identity component.** -/
theorem range_lieExp :
    range (lieExp (I := I) (G := G)) = (Subgroup.connectedComponentOfOne G : Set G) := by
  -- The image is the range of the homomorphism `lieExp`, hence a subgroup; it contains a
  -- neighbourhood of the identity, so it is the identity component, which is the subgroup
  -- generated by the exponential image.
  let M : Multiplicative (LeftInvariantDerivation I G) →* G :=
    AddMonoidHom.toMultiplicativeLeft (lieExpAddMonoidHom (I := I) (G := G))
  have hrange : (M.range : Set G) = range (lieExp (I := I) (G := G)) := by
    ext g
    simp only [M, MonoidHom.coe_range, AddMonoidHom.coe_toMultiplicativeLeft, mem_range,
      Function.comp_apply, lieExpAddMonoidHom_apply (I := I) (G := G), toMul_ofMul]
    exact ⟨fun ⟨X, hX⟩ => ⟨Multiplicative.toAdd X, hX⟩,
      fun ⟨X, hX⟩ => ⟨Multiplicative.ofAdd X, hX⟩⟩
  rw [← closure_range_lieExp_eq_connectedComponentOfOne (I := I) (G := G), ← hrange,
    Subgroup.closure_eq]

/-- **The exponential of a preconnected commutative Lie group is surjective.** -/
theorem lieExp_surjective_of_preconnectedSpace [PreconnectedSpace G] :
    Function.Surjective (lieExp (I := I) (G := G)) := by
  rw [← range_eq_univ, range_lieExp, Subgroup.connectedComponentOfOne_eq_top, Subgroup.coe_top]


/-! ### The exponential as a quotient map, and the lattice of a compact group -/

/-- The Lie algebra is finite-dimensional; a local instance for the rest of this file. -/
noncomputable local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))

section Preconnected

variable [PreconnectedSpace G]

/-- **The exponential homomorphism of a preconnected commutative Lie group is surjective.** -/
theorem lieExpAddMonoidHom_surjective_of_preconnectedSpace :
    Function.Surjective (lieExpAddMonoidHom (I := I) (G := G)) := fun g =>
  (lieExp_surjective_of_preconnectedSpace (I := I) (G := G) (Additive.toMul g)).imp
    fun X hX => by rw [lieExpAddMonoidHom_apply, hX, ofMul_toMul]

/-- **A preconnected commutative Lie group is the quotient of its Lie algebra by the kernel of the
exponential**, as topological groups: the first isomorphism theorem for the open surjective
homomorphism `lieExpAddMonoidHom`. -/
def lieExpQuotientKerContinuousAddEquiv :
    (LeftInvariantDerivation I G ⧸ (lieExpAddMonoidHom (I := I) (G := G)).ker) ≃ₜ+ Additive G :=
  ContinuousAddEquiv.quotientKerEquivOfSurjective _
    ((isOpenMap_lieExpAddMonoidHom (I := I) (G := G)).isStrictMap
      (continuous_lieExpAddMonoidHom (I := I) (G := G)))
    (lieExpAddMonoidHom_surjective_of_preconnectedSpace (I := I) (G := G))

@[simp]
theorem lieExpQuotientKerContinuousAddEquiv_apply (X : LeftInvariantDerivation I G) :
    lieExpQuotientKerContinuousAddEquiv (I := I) (G := G) (QuotientAddGroup.mk X) =
      Additive.ofMul (lieExp (I := I) X) := by
  rw [lieExpQuotientKerContinuousAddEquiv,
    ContinuousAddEquiv.quotientKerEquivOfSurjective_apply_mk, lieExpAddMonoidHom_apply]

@[simp]
theorem lieExpQuotientKerContinuousAddEquiv_symm_apply (X : LeftInvariantDerivation I G) :
    (lieExpQuotientKerContinuousAddEquiv (I := I) (G := G)).symm
      (Additive.ofMul (lieExp (I := I) X)) = QuotientAddGroup.mk X := by
  rw [← lieExpQuotientKerContinuousAddEquiv_apply, ContinuousAddEquiv.symm_apply_apply]

end Preconnected

section Compact

variable [CompactSpace G]

/-- **The Lie algebra modulo the kernel of the exponential is compact** when the group is: it is
the identity component, which is closed. -/
instance compactSpace_quotient_ker_lieExpAddMonoidHom :
    CompactSpace (LeftInvariantDerivation I G ⧸ (lieExpAddMonoidHom (I := I) (G := G)).ker) := by
  -- The quotient is the range of the exponential homomorphism, as the exponential is strict.
  have hcompact : IsCompact (Set.range (lieExpAddMonoidHom (I := I) (G := G))) := by
    rw [coe_lieExpAddMonoidHom, Set.range_comp, range_lieExp, Equiv.image_eq_preimage_symm,
      Additive.ofMul_symm_eq]
    exact (isClosed_connectedComponent.preimage continuous_toMul).isCompact
  rw [← AddMonoidHom.coe_range, isCompact_iff_compactSpace] at hcompact
  exact (ContinuousAddEquiv.quotientKerEquivRange
    ((isOpenMap_lieExpAddMonoidHom (I := I) (G := G)).isStrictMap
      continuous_lieExpAddMonoidHom)).symm.toHomeomorph.compactSpace

/-- **The kernel of the exponential of a compact commutative Lie group spans the Lie
algebra.** -/
theorem span_ker_lieExpAddMonoidHom_eq_top :
    Submodule.span ℝ
      ((lieExpAddMonoidHom (I := I) (G := G)).ker : Set (LeftInvariantDerivation I G)) = ⊤ :=
  AddSubgroup.span_eq_top_of_compactSpace_quotient _

/-- **The kernel of the exponential of a compact commutative Lie group is a lattice**
in the Lie algebra. -/
instance isZLattice_ker_lieExpAddMonoidHom :
    IsZLattice ℝ (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule where
  span_top := by
    rw [AddSubgroup.coe_toIntSubmodule]
    exact span_ker_lieExpAddMonoidHom_eq_top (I := I) (G := G)

/-- The rank of the kernel of the exponential is the dimension of the group. -/
theorem finrank_ker_lieExpAddMonoidHom :
    Module.finrank ℤ (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule =
      Module.finrank ℝ (LeftInvariantDerivation I G) :=
  ZLattice.rank ℝ _

section Torus

open scoped IsMulCommutative

/-- **A lattice basis of the Lie algebra**: a `ℤ`-basis of the kernel of the exponential,
indexed by the dimension of the group, which is also an `ℝ`-basis of the Lie algebra. -/
def lieExpLatticeBasis :
    Module.Basis (Fin (Module.finrank ℝ (LeftInvariantDerivation I G))) ℝ
      (LeftInvariantDerivation I G) :=
  (Module.finBasisOfFinrankEq ℤ (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule
    finrank_ker_lieExpAddMonoidHom).ofZLatticeBasis ℝ
    (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule

/-- The vectors of a lattice basis lie in the kernel of the exponential. -/
@[simp]
theorem lieExp_lieExpLatticeBasis (i : Fin (Module.finrank ℝ (LeftInvariantDerivation I G))) :
    lieExp (lieExpLatticeBasis (I := I) (G := G) i) = 1 := by
  rw [lieExpLatticeBasis, Module.Basis.ofZLatticeBasis_apply, ← mem_ker_lieExpAddMonoidHom]
  exact (Module.finBasisOfFinrankEq ℤ (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule
    finrank_ker_lieExpAddMonoidHom i).2

/-- The integral span of a lattice basis is the kernel of the exponential. -/
theorem span_range_lieExpLatticeBasis :
    Submodule.span ℤ (Set.range (lieExpLatticeBasis (I := I) (G := G))) =
      (lieExpAddMonoidHom (I := I) (G := G)).ker.toIntSubmodule :=
  Module.Basis.ofZLatticeBasis_span ℝ _ _

/-- The one-parameter subgroup of a lattice vector has period one, so it descends to the unit
circle `ℝ ⧸ ℤ`. -/
private def unitAddCircleLift (i : Fin (Module.finrank ℝ (LeftInvariantDerivation I G))) :
    UnitAddCircle →+ Additive G :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℝ))
    (AddMonoidHom.mk' (fun t : ℝ => lieExpAddMonoidHom (t • lieExpLatticeBasis (I := I) (G := G) i))
      fun s t => by rw [add_smul, map_add])
    fun t ht => by
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, zsmul_eq_mul, mul_one,
        Int.cast_smul_eq_zsmul, map_zsmul, lieExpAddMonoidHom_apply, lieExp_lieExpLatticeBasis,
        ofMul_one, zsmul_zero]

private theorem unitAddCircleLift_coe (i : Fin (Module.finrank ℝ (LeftInvariantDerivation I G)))
    (t : ℝ) :
    unitAddCircleLift (I := I) (G := G) i (t : UnitAddCircle) =
      Additive.ofMul (lieExp (t • lieExpLatticeBasis (I := I) (G := G) i)) := by
  rw [unitAddCircleLift, QuotientAddGroup.lift_mk, AddMonoidHom.mk'_apply, lieExpAddMonoidHom_apply]

private theorem continuous_unitAddCircleLift
    (i : Fin (Module.finrank ℝ (LeftInvariantDerivation I G))) :
    Continuous (unitAddCircleLift (I := I) (G := G) i) := by
  rw [(QuotientAddGroup.isQuotientMap_mk _).continuous_iff]
  exact (continuous_ofMul.comp ((contMDiff_lieExp (I := I) (G := G)).continuous.comp
    (continuous_id.smul continuous_const))).congr fun t => (unitAddCircleLift_coe i t).symm

/-- The lattice basis vectors generate circle subgroups, and the standard torus `(ℝ ⧸ ℤ)^r` maps
to the group by multiplying them. -/
private def unitAddTorusHom :
    (Fin (Module.finrank ℝ (LeftInvariantDerivation I G)) → UnitAddCircle) →+ Additive G where
  toFun z := ∑ i, unitAddCircleLift (I := I) (G := G) i (z i)
  map_zero' := by simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero]
  map_add' z w := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]

private theorem unitAddTorusHom_apply
    (z : Fin (Module.finrank ℝ (LeftInvariantDerivation I G)) → UnitAddCircle) :
    unitAddTorusHom (I := I) (G := G) z = ∑ i, unitAddCircleLift (I := I) (G := G) i (z i) :=
  rfl

private theorem unitAddTorusHom_coe
    (t : Fin (Module.finrank ℝ (LeftInvariantDerivation I G)) → ℝ) :
    unitAddTorusHom (I := I) (G := G) (fun i => (t i : UnitAddCircle)) =
      Additive.ofMul (lieExp (∑ i, t i • lieExpLatticeBasis (I := I) (G := G) i)) := by
  simp_rw [unitAddTorusHom_apply, unitAddCircleLift_coe, ← lieExpAddMonoidHom_apply, ← map_sum]

private theorem continuous_unitAddTorusHom : Continuous (unitAddTorusHom (I := I) (G := G)) :=
  (continuous_finsetSum _ fun i _ =>
    (continuous_unitAddCircleLift i).comp (continuous_apply i)).congr fun z =>
      (unitAddTorusHom_apply z).symm

private theorem unitAddTorusHom_injective :
    Function.Injective (unitAddTorusHom (I := I) (G := G)) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  choose t ht using fun i => QuotientAddGroup.mk_surjective (z i)
  have hz' : z = fun i => (t i : UnitAddCircle) := funext fun i => (ht i).symm
  rw [hz', unitAddTorusHom_coe, ← lieExpAddMonoidHom_apply, ← AddMonoidHom.mem_ker,
    ← SetLike.mem_coe, ← AddSubgroup.coe_toIntSubmodule, SetLike.mem_coe,
    ← span_range_lieExpLatticeBasis, Module.Basis.mem_span_iff_repr_mem,
    Module.Basis.repr_sum_self] at hz
  rw [hz']
  funext i
  obtain ⟨k, hk⟩ := hz i
  exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨k, by rw [zsmul_eq_mul, mul_one, ← hk]; rfl⟩

variable [PreconnectedSpace G]

private theorem unitAddTorusHom_surjective :
    Function.Surjective (unitAddTorusHom (I := I) (G := G)) := fun g => by
  obtain ⟨X, rfl⟩ := lieExpAddMonoidHom_surjective_of_preconnectedSpace (I := I) (G := G) g
  refine ⟨fun i => ((lieExpLatticeBasis (I := I) (G := G)).repr X i : UnitAddCircle), ?_⟩
  rw [unitAddTorusHom_coe, Module.Basis.sum_repr, lieExpAddMonoidHom_apply]

/-- The standard torus `(ℝ ⧸ ℤ)^r` is isomorphic to the group, as topological groups. -/
private def unitAddTorusContinuousAddEquiv :
    (Fin (Module.finrank ℝ (LeftInvariantDerivation I G)) → UnitAddCircle) ≃ₜ+ Additive G :=
  let _ : T2Space (Additive G) := ‹T2Space G›
  ContinuousAddEquiv.mk'
    (Continuous.homeoOfEquivCompactToT2
      (f := (AddEquiv.ofBijective (unitAddTorusHom (I := I) (G := G))
        ⟨unitAddTorusHom_injective, unitAddTorusHom_surjective⟩).toEquiv)
      continuous_unitAddTorusHom)
    (map_add (unitAddTorusHom (I := I) (G := G)))

private theorem unitAddTorusContinuousAddEquiv_coe
    (t : Fin (Module.finrank ℝ (LeftInvariantDerivation I G)) → ℝ) :
    unitAddTorusContinuousAddEquiv (I := I) (G := G) (fun i => (t i : UnitAddCircle)) =
      Additive.ofMul (lieExp (∑ i, t i • lieExpLatticeBasis (I := I) (G := G) i)) :=
  unitAddTorusHom_coe t

private theorem symm_homeomorphCircle_mul (x y : Circle) :
    (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm (x * y) =
      (AddCircle.homeomorphCircle one_ne_zero).symm x +
        (AddCircle.homeomorphCircle one_ne_zero).symm y := by
  rw [Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply one_ne_zero,
    AddCircle.toCircle_add, ← AddCircle.homeomorphCircle_apply one_ne_zero,
    ← AddCircle.homeomorphCircle_apply one_ne_zero, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

/-- The underlying homeomorphism of `torusContinuousMulEquiv`: read each circle coordinate as a
real number modulo one, apply `unitAddTorusContinuousAddEquiv`, and pass from `Additive G` to
`G`. -/
private def torusHomeomorph :
    (Fin (Module.finrank ℝ (LeftInvariantDerivation I G)) → Circle) ≃ₜ G :=
  (Homeomorph.piCongrRight fun _ => (AddCircle.homeomorphCircle one_ne_zero).symm).trans
    ((unitAddTorusContinuousAddEquiv (I := I) (G := G)).toHomeomorph.trans
      { Additive.toMul with
        continuous_toFun := continuous_toMul
        continuous_invFun := continuous_ofMul })

private theorem torusHomeomorph_apply
    (z : Fin (Module.finrank ℝ (LeftInvariantDerivation I G)) → Circle) :
    torusHomeomorph (I := I) (G := G) z = Additive.toMul (unitAddTorusContinuousAddEquiv (I := I)
      (G := G) fun i => (AddCircle.homeomorphCircle one_ne_zero).symm (z i)) :=
  rfl

/-- **A compact connected commutative Lie group is a torus**: it is isomorphic, as a topological
group, to a product of circles indexed by its dimension. The isomorphism sends
`(exp (2πi t_j))_j` to `lieExp (∑ t_j • X_j)` for a lattice basis `X`,
see `torusContinuousMulEquiv_apply`. -/
def torusContinuousMulEquiv :
    (Fin (Module.finrank ℝ (LeftInvariantDerivation I G)) → Circle) ≃ₜ* G :=
  ContinuousMulEquiv.mk' (torusHomeomorph (I := I) (G := G)) fun z w => by
    have h : (fun i => (AddCircle.homeomorphCircle one_ne_zero).symm ((z * w) i)) =
        (fun i => (AddCircle.homeomorphCircle one_ne_zero).symm (z i)) +
          fun i => (AddCircle.homeomorphCircle one_ne_zero).symm (w i) :=
      funext fun i => by rw [Pi.add_apply, Pi.mul_apply, symm_homeomorphCircle_mul]
    rw [torusHomeomorph_apply, torusHomeomorph_apply, torusHomeomorph_apply, h, map_add,
      toMul_add]

theorem torusContinuousMulEquiv_apply
    (t : Fin (Module.finrank ℝ (LeftInvariantDerivation I G)) → ℝ) :
    torusContinuousMulEquiv (I := I) (G := G) (fun i => Circle.exp (2 * Real.pi * t i)) =
      lieExp (∑ i, t i • lieExpLatticeBasis (I := I) (G := G) i) := by
  have hsymm : ∀ s : ℝ, (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm
      (Circle.exp (2 * Real.pi * s)) = (s : UnitAddCircle) := fun s =>
    (Homeomorph.symm_apply_eq _).mpr
      (by rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, div_one])
  rw [torusContinuousMulEquiv, ContinuousMulEquiv.coe_mk', torusHomeomorph_apply]
  simp only [hsymm, unitAddTorusContinuousAddEquiv_coe, toMul_ofMul]

theorem torusContinuousMulEquiv_symm_apply
    (t : Fin (Module.finrank ℝ (LeftInvariantDerivation I G)) → ℝ) :
    (torusContinuousMulEquiv (I := I) (G := G)).symm
        (lieExp (∑ i, t i • lieExpLatticeBasis (I := I) (G := G) i)) =
      fun i => Circle.exp (2 * Real.pi * t i) := by
  rw [← torusContinuousMulEquiv_apply, ContinuousMulEquiv.symm_apply_apply]

end Torus

end Compact

end TauCeti
