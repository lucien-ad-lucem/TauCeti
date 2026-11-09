/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# The point Lie group

The point, modelled on its zero-dimensional normed vector space, is a Lie group at every
regularity over every nontrivially normed field. Its multiplication and inversion are constant.
This provides the native point-group model for the compact Lie-algebra metric boundary case.

## References

* `Mathlib.Geometry.Manifold.Algebra.LieGroup`, for the Lie-group regularity classes.
-/

public section

open scoped ContDiff Manifold

universe u v

/-- The unique group operations on a point are smooth at every regularity. -/
instance LieGroup.punit {𝕜 : Type u} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} :
    LieGroup 𝓘(𝕜, PUnit.{v + 1}) n PUnit.{v + 1} where
  contMDiff_mul := contMDiff_const
  contMDiff_inv := contMDiff_const
