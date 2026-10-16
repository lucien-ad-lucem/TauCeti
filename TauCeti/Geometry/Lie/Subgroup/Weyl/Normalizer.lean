/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus
public import TauCeti.Geometry.Lie.Subgroup.Weyl.Group
public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Topology.Algebra.Module.Submodule
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
import TauCeti.Geometry.Lie.Exponential.CommutativeGroup
import TauCeti.Geometry.Lie.Subgroup.Differential
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# The exponential lattice of a torus and the normalizer of a maximal torus

For a commutative subgroup `K` of a Lie group `G`, the exponential is a homomorphism on `Lie(K)`,
and its kernel `Subgroup.lieExpKer K` is an additive subgroup of `Lie(K)`. For a torus `T` this
kernel is a full lattice: it is discrete and spans `Lie(T)`, because `T` is itself a compact
connected commutative Lie group whose Lie algebra is `Lie(T)`.

The normalizer of a subgroup `K` acts on `Lie(K)` through the adjoint representation, and this
action preserves the lattice. A one-parameter subgroup of the normalizer of a torus therefore
moves every lattice vector along a continuous path in a discrete set, so it fixes the lattice,
hence all of `Lie(T)`; differentiating, its generator brackets to zero with `Lie(T)`. For a
maximal torus of a compact Lie group such a generator lies in `Lie(T)`: the normalizer of a
maximal torus has the Lie algebra of the torus.

## Main definitions

* `Subgroup.lieExpKer`: the kernel of the exponential of a commutative subgroup, as an additive
  subgroup of its Lie algebra.

## Main results

* `TauCeti.Lie.IsTorus.discreteTopology_lieExpKer`, `TauCeti.Lie.IsTorus.span_lieExpKer_eq_top`
  and `TauCeti.Lie.IsTorus.isZLattice_lieExpKer`: the kernel of the exponential of a torus is a
  full lattice in its Lie algebra.
* `Subgroup.normalizerAdjointRepresentation_mem_lieExpKer`: the normalizer of a commutative
  subgroup preserves the kernel of its exponential.
* `TauCeti.Lie.IsMaximalTorus.lieSubalgebraOfSubgroup_normalizer`: the normalizer of a maximal
  torus of a compact Lie group has the Lie algebra of the torus.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map), Theorem (3.6), and Chapter IV, § 1 (Maximal Tori), (1.2)
  and the proof of Theorem (1.5).
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 15 (Tori), Proposition 15.3.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

section Kernel

variable (K : Subgroup G) [IsMulCommutative K]

/-- **The kernel of the exponential of a commutative subgroup**: the derivations in `Lie(K)`
which the exponential sends to the identity. -/
def _root_.Subgroup.lieExpKer : AddSubgroup (lieSubalgebraOfSubgroup (I := I) K).toSubmodule where
  carrier := {X | lieExp (I := I) (X : LeftInvariantDerivation I G) = 1}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, Submodule.coe_zero, lieExp_zero]
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq] at hX hY ⊢
    rw [Submodule.coe_add, lieExp_add_of_lie_eq_zero
      (lie_eq_zero_of_mem_lieSubalgebraOfSubgroup X.2 Y.2), hX, hY, mul_one]
  neg_mem' {X} hX := by
    simp only [Set.mem_ofPred_eq] at hX ⊢
    rw [Submodule.coe_neg, lieExp_neg, hX, inv_one]

variable {K}

@[simp]
theorem _root_.Subgroup.mem_lieExpKer {X : (lieSubalgebraOfSubgroup (I := I) K).toSubmodule} :
    X ∈ K.lieExpKer (I := I) ↔ lieExp (I := I) (X : LeftInvariantDerivation I G) = 1 :=
  Iff.rfl

/-- The normalizer of a commutative subgroup preserves the kernel of its exponential. -/
theorem _root_.Subgroup.normalizerAdjointRepresentation_mem_lieExpKer
    (g : Subgroup.normalizer (K : Set G)) {X : (lieSubalgebraOfSubgroup (I := I) K).toSubmodule}
    (hX : X ∈ K.lieExpKer (I := I)) :
    K.normalizerAdjointRepresentation (I := I) g X ∈ K.lieExpKer (I := I) := by
  rw [Subgroup.mem_lieExpKer] at hX ⊢
  rw [Subgroup.coe_normalizerAdjointRepresentation_apply, ← conj_lieExp, hX, mul_one,
    mul_inv_cancel]

end Kernel

section Lattice

variable {T : Subgroup G} [IsMulCommutative T] (hT : IsTorus T)
include hT

/-- The Lie algebra is finite-dimensional; a local instance for the lattice arguments. -/
local instance finiteDimensionalLeftInvariantDerivationOfNormalizer :
    FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))

omit hT in
/-- The kernel of the exponential of a torus `T` is the pullback of the kernel of the exponential
of `T`, as a Lie group in its own right, along the identification of its Lie algebra with
`Lie(T)`. -/
private theorem toIntSubmodule_lieExpKer_eq
    (d : EmbeddedLieSubgroupData I T (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :
    let _ : ChartedSpace (lieSubalgebraOfSubgroup (I := I) T).toSubmodule T := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) ∞ T := d.lieGroup
    have : FiniteDimensional ℝ
        (LeftInvariantDerivation 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) T) :=
      finiteDimensional_leftInvariantDerivation
        (ContMDiffMul.isInteriorPoint
          (I := 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) T).toSubmodule)) (n := ∞) (by simp) (1 : T))
    (T.lieExpKer (I := I)).toIntSubmodule =
      ZLattice.comap ℝ
        (lieExpAddMonoidHom (I := 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) T).toSubmodule))
          (G := T)).ker.toIntSubmodule
        d.lieEquivLieSubalgebraOfSubgroup.symm.toLinearEquiv.toLinearMap := by
  let _ : ChartedSpace (lieSubalgebraOfSubgroup (I := I) T).toSubmodule T := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) ∞ T := d.lieGroup
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  dsimp only
  ext X
  -- Membership on both sides unfolds to a statement about exponentials.
  change lieExp (I := I) (X : LeftInvariantDerivation I G) = 1 ↔
    d.lieEquivLieSubalgebraOfSubgroup.symm X ∈
      (lieExpAddMonoidHom (I := 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) T).toSubmodule))
        (G := T)).ker
  rw [mem_ker_lieExpAddMonoidHom, ← OneMemClass.coe_eq_one (S' := T)]
  have hnat := map_lieExp d.subtypeVal (d.lieEquivLieSubalgebraOfSubgroup.symm X)
  dsimp only at hnat
  rw [EmbeddedLieSubgroupData.subtypeVal_apply, ← EmbeddedLieSubgroupData.lieMapSubtypeVal_apply,
    ← EmbeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup_apply, LieEquiv.apply_symm_apply]
    at hnat
  rw [hnat]

/-- **The kernel of the exponential of a torus is discrete.** -/
theorem IsTorus.discreteTopology_lieExpKer : DiscreteTopology (T.lieExpKer (I := I)) := by
  obtain ⟨d⟩ := nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed (I := I)
    hT.isClosed
  have h := toIntSubmodule_lieExpKer_eq (I := I) (T := T) d
  let _ : ChartedSpace (lieSubalgebraOfSubgroup (I := I) T).toSubmodule T := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) ∞ T := d.lieGroup
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  change DiscreteTopology (T.lieExpKer (I := I)).toIntSubmodule
  rw [h]
  exact ZLattice.comap_discreteTopology ℝ _
    (e := d.lieEquivLieSubalgebraOfSubgroup.symm.toLinearEquiv.toLinearMap)
    (LinearMap.continuous_of_finiteDimensional _) (LinearEquiv.injective _)

/-- **The kernel of the exponential of a torus spans its Lie algebra.** -/
theorem IsTorus.span_lieExpKer_eq_top :
    Submodule.span ℝ
      (T.lieExpKer (I := I) : Set (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) = ⊤ := by
  obtain ⟨d⟩ := nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed (I := I)
    hT.isClosed
  have h := toIntSubmodule_lieExpKer_eq (I := I) (T := T) d
  let _ : ChartedSpace (lieSubalgebraOfSubgroup (I := I) T).toSubmodule T := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) ∞ T := d.lieGroup
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have _ : CompactSpace T := isCompact_iff_compactSpace.mp hT.isCompact
  rw [← AddSubgroup.coe_toIntSubmodule, h]
  refine ZLattice.comap_span_top ℝ _ ?_
    (e := d.lieEquivLieSubalgebraOfSubgroup.symm.toLinearEquiv.toLinearMap)
    fun X _ => LinearMap.mem_range.mpr (LinearEquiv.surjective _ X)
  rw [AddSubgroup.coe_toIntSubmodule]
  exact span_ker_lieExpAddMonoidHom_eq_top

/-- **The kernel of the exponential of a torus is a full lattice in its Lie algebra.** -/
theorem IsTorus.isZLattice_lieExpKer :
    have := hT.discreteTopology_lieExpKer (I := I)
    IsZLattice ℝ (T.lieExpKer (I := I)).toIntSubmodule :=
  have := hT.discreteTopology_lieExpKer (I := I)
  ⟨by rw [AddSubgroup.coe_toIntSubmodule]; exact hT.span_lieExpKer_eq_top⟩

end Lattice

section Normalizer

variable [CompactSpace G]

/-- **The normalizer of a maximal torus has the Lie algebra of the torus.** -/
theorem IsMaximalTorus.lieSubalgebraOfSubgroup_normalizer {T : Subgroup G}
    (hT : IsMaximalTorus T) :
    lieSubalgebraOfSubgroup (I := I) (Subgroup.normalizer (T : Set G)) =
      lieSubalgebraOfSubgroup (I := I) T := by
  have _ : IsMulCommutative T := hT.isTorus.isMulCommutative
  refine le_antisymm (fun X hX => ?_) (lieSubalgebraOfSubgroup_mono Subgroup.le_normalizer)
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  rw [mem_lieSubalgebraOfSubgroup (Subgroup.isClosed_normalizer hT.isTorus.isClosed)] at hX
  apply hT.mem_lieSubalgebraOfSubgroup_of_forall_lie_eq_zero
  intro Y hY
  -- The one-parameter subgroup of `X` lies in the normalizer, so it acts on `Lie(T)` preserving
  -- the lattice; being connected, it fixes every lattice vector, hence all of `Lie(T)`.
  have hfix : ∀ (t : ℝ) (Λ : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule),
      Λ ∈ T.lieExpKer (I := I) →
        T.normalizerAdjointRepresentation (I := I) ⟨lieExp (I := I) (t • X), hX t⟩ Λ = Λ := by
    intro t Λ hΛ
    have hcont : Continuous fun s : ℝ =>
        T.normalizerAdjointRepresentation (I := I) ⟨lieExp (I := I) (s • X), hX s⟩ Λ := by
      refine continuous_induced_rng.mpr ?_
      simp only [Function.comp_def, Subgroup.coe_normalizerAdjointRepresentation_apply]
      exact (contMDiff_Ad_apply (I := I) (G := G)).continuous.comp
        (((contMDiff_lieExp (I := I) (G := G)).continuous.comp
          (continuous_id.smul continuous_const)).prodMk continuous_const)
    have hdisc : IsDiscrete
        (T.lieExpKer (I := I) : Set (lieSubalgebraOfSubgroup (I := I) T).toSubmodule) :=
      isDiscrete_iff_discreteTopology.mpr (hT.isTorus.discreteTopology_lieExpKer (I := I))
    have h := isPreconnected_univ.constant_of_mapsTo hdisc hcont.continuousOn
      (fun s _ => T.normalizerAdjointRepresentation_mem_lieExpKer _ hΛ) (Set.mem_univ t)
      (Set.mem_univ 0)
    rw [h]
    have h1 : (⟨lieExp (I := I) ((0 : ℝ) • X), hX 0⟩ : Subgroup.normalizer (T : Set G)) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mk, OneMemClass.coe_one, zero_smul, lieExp_zero])
    rw [h1, map_one, Module.End.one_apply]
  have hid : ∀ t : ℝ,
      T.normalizerAdjointRepresentation (I := I) ⟨lieExp (I := I) (t • X), hX t⟩ = LinearMap.id :=
    fun t => LinearMap.ext_on (hT.isTorus.span_lieExpKer_eq_top (I := I)) fun Λ hΛ => by
      rw [LinearMap.id_apply]
      exact hfix t Λ hΛ
  have hconst : ∀ t : ℝ, Ad (I := I) (lieExp (I := I) (t • X)) Y = Y := fun t => by
    have h := congrArg (fun f : Module.End ℝ (lieSubalgebraOfSubgroup (I := I) T).toSubmodule =>
      (f ⟨Y, hY⟩ : LeftInvariantDerivation I G)) (hid t)
    simpa only [Subgroup.coe_normalizerAdjointRepresentation_apply, LinearMap.id_apply] using h
  have hderiv := hasDerivAt_Ad_lieExp_smul_apply_zero (I := I) X Y
  simp only [hconst] at hderiv
  exact hderiv.unique (hasDerivAt_const 0 Y)

end Normalizer

end TauCeti.Lie
