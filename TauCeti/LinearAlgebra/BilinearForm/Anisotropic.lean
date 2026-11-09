/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!+# Anisotropic quadratic maps and bilinear forms

Anisotropy is preserved by pullback along an injective linear map. A bilinear form with
anisotropic diagonal is nondegenerate, without symmetry or order assumptions.

## Main results

* `QuadraticMap.Anisotropic.comp`: an injective pullback of an anisotropic map is anisotropic.
* `LinearMap.BilinForm.nondegenerate_of_anisotropic`: an anisotropic diagonal implies
  nondegeneracy of a bilinear form.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Definition 12.1.1 and Lemma 12.1.2, for the positive-definite case of restriction of forms.
-/

public section

/-- An injective pullback of an anisotropic quadratic map is anisotropic. -/
theorem QuadraticMap.Anisotropic.comp {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P] {Q : QuadraticMap R M N} (hQ : Q.Anisotropic)
    (f : P →ₗ[R] M) (hf : Function.Injective f) : (Q.comp f).Anisotropic := by
  intro x hx
  apply hf
  rw [map_zero]
  exact hQ _ hx

/-- A bilinear form with anisotropic diagonal is nondegenerate, without symmetry. -/
theorem LinearMap.BilinForm.nondegenerate_of_anisotropic {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (B : LinearMap.BilinForm R M)
    (hB : B.toQuadraticMap.Anisotropic) : B.Nondegenerate :=
  ⟨LinearMap.BilinForm.separatingLeft_of_anisotropic hB, fun x hx ↦ hB x (hx x)⟩
