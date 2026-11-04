/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Functor
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Covering.Basic
import TauCeti.Topology.Algebra.Group.Covering
import TauCeti.Topology.Covering.Clopen
import TauCeti.Topology.Homotopy.Covering
import TauCeti.Geometry.Manifold.Topology

/-!
# Lie homomorphisms with invertible differential

A smooth homomorphism with bijective Lie map is a local diffeomorphism at every point.
If its target is preconnected, it is a covering map. If its source is preconnected and its
target is simply connected, it is bijective. These are the local-isomorphism criteria used
when integrating Lie-algebra homomorphisms by graph subgroups.

## Main results

* `ContMDiffMonoidMorphism.isLocalDiffeomorph_of_lieMap_bijective`: invertible differential
  gives a local diffeomorphism everywhere.
* `ContMDiffMonoidMorphism.isCoveringMap_of_lieMap_bijective`: the covering criterion.
* `ContMDiffMonoidMorphism.bijective_of_lieMap_bijective_of_simplyConnectedSpace`: the
  bijectivity criterion over a simply connected target.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Exercise 2.3, for the covering-map assertion.
-/

public section

open Function Manifold Topology Set
open scoped ContDiff Manifold

noncomputable section

namespace ContMDiffMonoidMorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {K : Type*} [TopologicalSpace K] [ChartedSpace H' K] [Group K] [LieGroup J ∞ K]

private def mulLeftDiffeo (g : G) : G ≃ₘ⟮I, I⟯ G where
  toEquiv := Equiv.mulLeft g
  contMDiff_toFun := contMDiff_mul_left
  contMDiff_invFun := contMDiff_mul_left

private theorem mulLeftDiffeo_apply (g x : G) : mulLeftDiffeo (I := I) g x = g * x := rfl

private theorem isLocalDiffeomorph_of_isLocalDiffeomorphAt_one
    (f : ContMDiffMonoidMorphism I J ∞ G K)
    (h : IsLocalDiffeomorphAt I J ∞ f 1) : IsLocalDiffeomorph I J ∞ f := by
  intro g
  have hleft := (mulLeftDiffeo (I := I) g⁻¹).isLocalDiffeomorph g
  have hmid : IsLocalDiffeomorphAt I J ∞ (f ∘ mulLeftDiffeo (I := I) g⁻¹) g :=
    hleft.comp (K := J) (P := K) (by simpa only [mulLeftDiffeo_apply, inv_mul_cancel] using h)
  have hwhole := hmid.comp (K := J) (P := K) ((mulLeftDiffeo (I := J) (f g)).isLocalDiffeomorph _)
  simpa only [Function.comp_def, mulLeftDiffeo_apply, map_mul, map_inv,
    mul_inv_cancel_left] using hwhole

/-- A smooth homomorphism with bijective Lie map is a local diffeomorphism. -/
theorem isLocalDiffeomorph_of_lieMap_bijective [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] (f : ContMDiffMonoidMorphism I J ∞ G K)
    (hf : Bijective (lieMap f)) : IsLocalDiffeomorph I J ∞ f :=
  isLocalDiffeomorph_of_isLocalDiffeomorphAt_one f
    (f.isLocalDiffeomorphAt_of_lieMap_bijective hf)

/-- A smooth homomorphism with bijective Lie map onto a preconnected target is a covering map. -/
theorem isCoveringMap_of_lieMap_bijective [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [PreconnectedSpace K] (f : ContMDiffMonoidMorphism I J ∞ G K)
    (hf : Bijective (lieMap f)) : IsCoveringMap f := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : IsTopologicalGroup K := topologicalGroup_of_lieGroup J ∞
  have hlocal := (f.isLocalDiffeomorph_of_lieMap_bijective hf).isLocalHomeomorph
  exact f.toMonoidHom.isCoveringMap_of_surjective_isLocalHomeomorph hlocal
    (f.toMonoidHom.surjective_of_isLocalHomeomorph hlocal)

/-- A smooth homomorphism with bijective Lie map from a preconnected group to a simply
connected group is bijective. -/
theorem bijective_of_lieMap_bijective_of_simplyConnectedSpace [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] [PreconnectedSpace G] [SimplyConnectedSpace K]
    (f : ContMDiffMonoidMorphism I J ∞ G K) (hf : Bijective (lieMap f)) : Bijective f := by
  let _ : ConnectedSpace G :=
    { toPreconnectedSpace := inferInstance, toNonempty := ⟨1⟩ }
  let _ : LocallyPathConnectedSpace H := I.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace G := ChartedSpace.locallyPathConnectedSpace H G
  let _ : PathConnectedSpace G := PathConnectedSpace.of_locallyPathConnectedSpace
  have hcov := f.isCoveringMap_of_lieMap_bijective hf
  exact ⟨hcov.injective, hcov.surjective⟩

end ContMDiffMonoidMorphism
