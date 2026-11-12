/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Sesquilinear forms and inner products

A positive definite Hermitian form on a real or complex vector space defines an
`InnerProductSpace.Core`, without requiring a previously chosen norm or topology.

A sesquilinear form on a finite-dimensional inner product space which gives every
endomorphism its usual adjoint is a scalar multiple of the inner product. For a positive
definite real or complex sesquilinear form, the scalar is uniquely determined and positive real.
This is the full-endomorphism-algebra form of the uniqueness of an invariant metric.

The comparison uses Mathlib's rank-one operators: their adjoints exchange the two vectors.
It does not assume that the form being compared is already represented by an operator.

## Main definitions and results

* `LinearMap.toInnerProductSpaceCore`: the core defined by a positive definite Hermitian form.
* `LinearMap.toInnerProductSpaceCore_inner`: its inner product is the original form.
* `LinearMap.eq_mul_inner_of_adjoint`: a form with the usual adjoints is a scalar multiple of
  the inner product.
* `LinearMap.existsUnique_pos_mul_inner_of_adjoint`: uniqueness and positivity of that scalar.

## References

* Mathlib's `InnerProductSpace.Core` in `Mathlib.Analysis.InnerProductSpace.Defs` gives the
  defining axioms used by `LinearMap.toInnerProductSpaceCore`.
-/

public section

namespace LinearMap

open InnerProductSpace

section Core

variable {𝕜 V : Type*} [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]

open scoped ComplexOrder

/-- The inner product space core of a positive definite Hermitian form. This constructs data;
it does not install a norm or an inner product space instance on a space with an existing norm. -/
@[instance_reducible]
noncomputable def toInnerProductSpaceCore (h : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜) (hh : h.IsSymm)
    (hpos : ∀ x, x ≠ 0 → 0 < h x x) : InnerProductSpace.Core 𝕜 V where
  inner x y := h x y
  conj_inner_symm x y := hh.eq y x
  re_inner_nonneg x := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact (RCLike.pos_iff.mp (hpos x hx)).1.le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra hne
    exact (hpos x hne).ne' hx

/-- The core constructed from a Hermitian form has that form as its inner product. -/
@[simp]
theorem toInnerProductSpaceCore_inner (h : V →ₗ⋆[𝕜] V →ₗ[𝕜] 𝕜) (hh : h.IsSymm)
    (hpos : ∀ x, x ≠ 0 → 0 < h x x) (x y : V) :
    (h.toInnerProductSpaceCore hh hpos).inner x y = h x y :=
  (rfl)

end Core

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A sesquilinear form with the usual adjoints is determined by its value on any unit vector.
No symmetry or nondegeneracy of the form is required. -/
theorem eq_mul_inner_of_adjoint (H : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜)
    (hH : ∀ (T : Module.End 𝕜 E) x y, H (T x) y = H x (T.adjoint y))
    {u : E} (hu : ‖u‖ = 1) (x y : E) :
    H x y = H u u * inner 𝕜 x y := by
  have h := hH (rankOne 𝕜 x u).toLinearMap u y
  simpa [ContinuousLinearMap.adjoint_toLinearMap, rankOne_apply,
    hu, mul_comm] using h

open scoped ComplexOrder

/-- A positive definite real or complex sesquilinear form giving all endomorphisms their usual
adjoints is a unique positive real multiple of the inner product. Nontriviality is necessary
for uniqueness of the scalar. -/
theorem existsUnique_pos_mul_inner_of_adjoint [Nontrivial E]
    (H : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (hpos : H.IsNonneg)
    (hdef : ∀ x : E, x ≠ 0 → H x x ≠ 0)
    (hH : ∀ (T : Module.End 𝕜 E) x y, H (T x) y = H x (T.adjoint y)) :
    ∃! r : ℝ, 0 < r ∧ ∀ x y, H x y = (r : 𝕜) * inner 𝕜 x y := by
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨u, hu⟩ := exists_norm_eq E zero_le_one
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  obtain ⟨hre, him⟩ := RCLike.nonneg_iff.mp (hpos.nonneg u)
  have hc : H u u = (RCLike.re (H u u) : 𝕜) := by
    apply RCLike.ext <;> simp [him.symm]
  have hr : 0 < RCLike.re (H u u) := lt_of_le_of_ne hre fun h =>
    hdef u hu0 (hc.trans (by simp [h.symm]))
  refine ⟨RCLike.re (H u u), ⟨hr, ?_⟩, ?_⟩
  · intro x y
    exact (eq_mul_inner_of_adjoint H hH hu x y).trans
      (congrArg (· * inner 𝕜 x y) hc)
  · rintro r ⟨_, hr⟩
    have h := hr u u
    rw [inner_self_eq_one_of_norm_eq_one hu, mul_one, hc] at h
    exact (RCLike.ofReal_injective h).symm

end LinearMap
