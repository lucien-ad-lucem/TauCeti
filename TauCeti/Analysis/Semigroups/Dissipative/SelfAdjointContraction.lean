/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generator.ComplexLinear
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
import TauCeti.Analysis.Semigroups.Dissipative.Hilbert

/-!
# Generators of self-adjoint contraction semigroups

A contraction semigroup on a complex Hilbert space whose operators are complex linear and
self-adjoint has a self-adjoint complex generator with nonpositive quadratic form: the generator is
symmetric because each operator is, its resolvent supplies a surjective real shift, and the basic
criterion for self-adjointness
(`LinearPMap.isSelfAdjoint_of_isFormalAdjoint_of_surjective_real_smul_sub`) closes the gap between
symmetric and self-adjoint.  Nonpositivity of the quadratic form is the
inner-product form of dissipativity of the generator.

## Main results

* `ContractionSemigroup.complexGenerator_smul_sub_surjective`: every positive real shift of the
  complex generator of a complex-linear contraction semigroup is surjective.
* `ContractionSemigroup.re_inner_complexGenerator_apply_self_nonpos`: the quadratic form of the
  complex generator has nonpositive real part.
* `ContractionSemigroup.complexGenerator_isFormalAdjoint`: if every operator of the semigroup is
  self-adjoint, the complex generator is formally self-adjoint.
* `ContractionSemigroup.isSelfAdjoint_complexGenerator` and
  `ContractionSemigroup.isSelfAdjoint_neg_complexGenerator`: it is then self-adjoint, and so is
  its negative.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Corollary II.4.4 and Section II.3.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Theorem VIII.3.
-/

public section

noncomputable section

open scoped InnerProductSpace NNReal

namespace TauCeti.Semigroups

namespace ContractionSemigroup

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- Every positive real shift of the complex generator of a complex-linear contraction semigroup
maps its domain onto the whole space: this is the resolvent of the contraction semigroup. -/
theorem complexGenerator_smul_sub_surjective (S : ContractionSemigroup X)
    (hS : S.toStronglyContinuousSemigroup.IsComplexLinear) {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Surjective fun
      x : (S.toStronglyContinuousSemigroup.complexGenerator hS).domain =>
        (lambda : ℂ) • (x : X) - S.toStronglyContinuousSemigroup.complexGenerator hS x := by
  intro y
  obtain ⟨x, hx⟩ := S.toStronglyContinuousSemigroup.smul_sub_generator_surjective
    S.hasGrowthBound hlambda y
  refine ⟨⟨(x : X), by
    rw [S.toStronglyContinuousSemigroup.complexGenerator_domain hS,
      S.toStronglyContinuousSemigroup.mem_complexDomain_iff hS,
      ← S.toStronglyContinuousSemigroup.generator_domain]
    exact x.property⟩, ?_⟩
  -- Beta-reduce the applied lambda, then evaluate the complex generator.
  dsimp only
  rw [S.toStronglyContinuousSemigroup.complexGenerator_apply hS, Complex.coe_smul]
  exact hx

/-- The quadratic form of the complex generator of a complex-linear contraction semigroup has
nonpositive real part: the inner-product form of dissipativity of the generator. -/
theorem re_inner_complexGenerator_apply_self_nonpos (S : ContractionSemigroup X)
    (hS : S.toStronglyContinuousSemigroup.IsComplexLinear)
    (x : (S.toStronglyContinuousSemigroup.complexGenerator hS).domain) :
    (inner ℂ (S.toStronglyContinuousSemigroup.complexGenerator hS x) (x : X)).re ≤ 0 := by
  rw [S.toStronglyContinuousSemigroup.complexGenerator_apply hS x]
  -- The real inner product of `rclikeToReal` sits over the ambient real normed structure, in
  -- which the dissipativity of the generator is stated.
  let _ : InnerProductSpace ℝ X := InnerProductSpace.rclikeToReal ℂ X
  have h := S.real_inner_generator_nonpos ⟨(x : X), by
    rw [S.toStronglyContinuousSemigroup.generator_domain,
      ← S.toStronglyContinuousSemigroup.mem_complexDomain_iff hS,
      ← S.toStronglyContinuousSemigroup.complexGenerator_domain hS]
    exact x.property⟩
  rwa [real_inner_eq_re_inner] at h

/-- For a semigroup of self-adjoint operators, the generator difference quotients are symmetric
under the inner product. -/
private theorem inner_genQuot_eq (S : ContractionSemigroup X)
    (hS : S.toStronglyContinuousSemigroup.IsComplexLinear)
    (hself : ∀ t, IsSelfAdjoint (S.toStronglyContinuousSemigroup.complexLinearOperator hS t))
    (t : ℝ) (x y : X) :
    inner ℂ ((1 / t) • (S.toStronglyContinuousSemigroup.realOperator t x - x)) y =
      inner ℂ x ((1 / t) • (S.toStronglyContinuousSemigroup.realOperator t y - y)) := by
  have hxy : inner ℂ (S.toStronglyContinuousSemigroup.realOperator t x) y =
      inner ℂ x (S.toStronglyContinuousSemigroup.realOperator t y) := by
    have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hself t.toNNReal)) x y
    rwa [ContinuousLinearMap.coe_coe,
      S.toStronglyContinuousSemigroup.complexLinearOperator_apply hS,
      S.toStronglyContinuousSemigroup.complexLinearOperator_apply hS,
      ← S.toStronglyContinuousSemigroup.realOperator_def] at h
  rw [← algebraMap_smul ℂ (1 / t), ← algebraMap_smul ℂ (1 / t), inner_smul_real_right,
    inner_smul_real_left, inner_sub_left, inner_sub_right, hxy]

omit [CompleteSpace X] in
/-- The generator difference quotient of `x ∈ D(A)` paired with `y` converges to `⟪A x, y⟫`. -/
private theorem tendsto_inner_genQuot_left (S : ContractionSemigroup X)
    (hS : S.toStronglyContinuousSemigroup.IsComplexLinear)
    (x : (S.toStronglyContinuousSemigroup.complexGenerator hS).domain) (y : X) :
    Filter.Tendsto (fun t : ℝ => inner ℂ ((1 / t) •
      (S.toStronglyContinuousSemigroup.realOperator t (x : X) - (x : X))) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (inner ℂ (S.toStronglyContinuousSemigroup.complexGenerator hS x) y)) := by
  have hxmem : (x : X) ∈ S.toStronglyContinuousSemigroup.domain := by
    rw [← S.toStronglyContinuousSemigroup.mem_complexDomain_iff hS,
      ← S.toStronglyContinuousSemigroup.complexGenerator_domain hS]
    exact x.property
  rw [S.toStronglyContinuousSemigroup.complexGenerator_apply hS x]
  exact (S.toStronglyContinuousSemigroup.generator_tendsto ⟨(x : X), hxmem⟩).inner
    tendsto_const_nhds

omit [CompleteSpace X] in
/-- `x` paired with the generator difference quotient of `y ∈ D(A)` converges to `⟪x, A y⟫`. -/
private theorem tendsto_inner_genQuot_right (S : ContractionSemigroup X)
    (hS : S.toStronglyContinuousSemigroup.IsComplexLinear) (x : X)
    (y : (S.toStronglyContinuousSemigroup.complexGenerator hS).domain) :
    Filter.Tendsto (fun t : ℝ => inner ℂ x ((1 / t) •
      (S.toStronglyContinuousSemigroup.realOperator t (y : X) - (y : X))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (inner ℂ x (S.toStronglyContinuousSemigroup.complexGenerator hS y))) := by
  have hymem : (y : X) ∈ S.toStronglyContinuousSemigroup.domain := by
    rw [← S.toStronglyContinuousSemigroup.mem_complexDomain_iff hS,
      ← S.toStronglyContinuousSemigroup.complexGenerator_domain hS]
    exact y.property
  rw [S.toStronglyContinuousSemigroup.complexGenerator_apply hS y]
  exact tendsto_const_nhds.inner
    (S.toStronglyContinuousSemigroup.generator_tendsto ⟨(y : X), hymem⟩)

/-- The complex generator of a complex-linear contraction semigroup of self-adjoint operators is
formally self-adjoint: the symmetry of the operators passes to the limit of the difference
quotients. -/
theorem complexGenerator_isFormalAdjoint (S : ContractionSemigroup X)
    (hS : S.toStronglyContinuousSemigroup.IsComplexLinear)
    (hself : ∀ t, IsSelfAdjoint (S.toStronglyContinuousSemigroup.complexLinearOperator hS t)) :
    (S.toStronglyContinuousSemigroup.complexGenerator hS).IsFormalAdjoint
      (S.toStronglyContinuousSemigroup.complexGenerator hS) := fun x y =>
  tendsto_nhds_unique (tendsto_inner_genQuot_left S hS x y)
    ((tendsto_inner_genQuot_right S hS (x : X) y).congr' (Filter.Eventually.of_forall fun t =>
      (inner_genQuot_eq S hS hself t x y).symm))

/-- **The generator of a self-adjoint contraction semigroup is self-adjoint**: it is symmetric,
and its resolvent makes the real shift `1 - A` surjective. -/
theorem isSelfAdjoint_complexGenerator (S : ContractionSemigroup X)
    (hS : S.toStronglyContinuousSemigroup.IsComplexLinear)
    (hself : ∀ t, IsSelfAdjoint (S.toStronglyContinuousSemigroup.complexLinearOperator hS t)) :
    IsSelfAdjoint (S.toStronglyContinuousSemigroup.complexGenerator hS) :=
  LinearPMap.isSelfAdjoint_of_isFormalAdjoint_of_surjective_real_smul_sub
    (by
      rw [S.toStronglyContinuousSemigroup.complexGenerator_domain hS]
      exact S.toStronglyContinuousSemigroup.dense_complexDomain hS)
    (S.complexGenerator_isFormalAdjoint hS hself) 1
    (S.complexGenerator_smul_sub_surjective hS one_pos)

/-- The negative of the generator of a self-adjoint contraction semigroup is self-adjoint (with
nonnegative quadratic form, by `re_inner_complexGenerator_apply_self_nonpos`). -/
theorem isSelfAdjoint_neg_complexGenerator (S : ContractionSemigroup X)
    (hS : S.toStronglyContinuousSemigroup.IsComplexLinear)
    (hself : ∀ t, IsSelfAdjoint (S.toStronglyContinuousSemigroup.complexLinearOperator hS t)) :
    IsSelfAdjoint (-(S.toStronglyContinuousSemigroup.complexGenerator hS)) := by
  refine LinearPMap.isSelfAdjoint_of_isFormalAdjoint_of_surjective_real_smul_sub ?_ ?_ (-1) ?_
  · rw [LinearPMap.neg_domain, S.toStronglyContinuousSemigroup.complexGenerator_domain hS]
    exact S.toStronglyContinuousSemigroup.dense_complexDomain hS
  · intro x y
    simpa only [LinearPMap.neg_apply, inner_neg_left, inner_neg_right] using
      congrArg Neg.neg (S.complexGenerator_isFormalAdjoint hS hself x y)
  · intro y
    obtain ⟨x, hx⟩ := S.complexGenerator_smul_sub_surjective hS one_pos (-y)
    refine ⟨x, ?_⟩
    -- Beta-reduce the applied lambdas.
    dsimp only at hx ⊢
    rw [Complex.ofReal_one, one_smul] at hx
    rw [RCLike.ofReal_neg, RCLike.ofReal_one, neg_one_smul, LinearPMap.neg_apply,
      sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, hx, neg_neg]

end ContractionSemigroup

end TauCeti.Semigroups

end
