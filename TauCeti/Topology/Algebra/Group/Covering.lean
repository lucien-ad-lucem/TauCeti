/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Covering homomorphisms of topological groups

A surjective homomorphism that is a local homeomorphism is a covering map.
For a preconnected target, a local-homeomorphism homomorphism is automatically surjective.
These criteria turn local information about a group homomorphism into a global covering.

## Main results

* `MonoidHom.isCoveringMap_of_surjective_isLocalHomeomorph`: a surjective homomorphism
  which is a local homeomorphism is a covering map.
* `MonoidHom.surjective_of_isLocalHomeomorph`: a local-homeomorphism homomorphism into a
  preconnected topological group is surjective.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Exercise 2.3, for the covering-map assertion for Lie groups.
* Mathlib's `IsQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom`.
-/

public section

open Function Topology Set

namespace MonoidHom

variable {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group K] [TopologicalSpace K] [SeparatelyContinuousMul K]

omit [SeparatelyContinuousMul K] in
/-- A surjective local-homeomorphism homomorphism is a covering map. -/
theorem isCoveringMap_of_surjective_isLocalHomeomorph (f : G →* K)
    (hlocal : IsLocalHomeomorph f) (hsurj : Surjective f) : IsCoveringMap f := by
  have hq : IsOpenQuotientMap f := ⟨hsurj, hlocal.continuous, hlocal.isOpenMap⟩
  have hdiscrete : IsDiscrete (f.ker : Set G) := by
    apply (hlocal.isLocalHomeomorphOn.mono (subset_univ _)).isDiscrete_of_image
    rw [← Subgroup.coe_map, Subgroup.map_ker_self, Subgroup.coe_bot]
    exact (subsingleton_singleton : ({1} : Set K).Subsingleton).isDiscrete
  exact (hq.isQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    hdiscrete).isCoveringMap

omit [IsTopologicalGroup G] in
/-- A local-homeomorphism homomorphism into a preconnected group is surjective. -/
theorem surjective_of_isLocalHomeomorph [PreconnectedSpace K] (f : G →* K)
    (hlocal : IsLocalHomeomorph f) : Surjective f := by
  have hopen : IsOpen (f.range : Set K) := hlocal.isOpenMap.isOpen_range
  have hclopen : IsClopen (f.range : Set K) := ⟨f.range.isClosed_of_isOpen hopen, hopen⟩
  have hfull := hclopen.eq_univ ⟨1, f.range.one_mem⟩
  exact range_eq_univ.mp hfull

end MonoidHom

