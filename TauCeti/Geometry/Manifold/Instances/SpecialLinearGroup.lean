/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Analysis.Matrix.Normed
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.RegularValue.Level
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.Det
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Analysis.Calculus.ContDiff.Matrix

/-!
# The analytic special linear group

The special linear group over `ℝ` or `ℂ` is an analytic Lie group with its existing subspace
topology. Its matrix inclusion is an analytic embedding, and the tangent image at the identity
is exactly the trace-zero matrices. The model has dimension `card n * card n - 1`, including
the trivial group with empty matrix index.

Matrix-valued maps use the `L∞` operator norm. Enable `open scoped Matrix.Norms.Operator` and
`attribute [local instance] Matrix.linftyOpTopologicalSpace` when using these results.

## Main declarations

* `Matrix.SpecialLinearGroup.Model`: the model vector space.
* `Matrix.SpecialLinearGroup.instChartedSpace`, `Matrix.SpecialLinearGroup.instIsManifold`,
  `Matrix.SpecialLinearGroup.instLieGroup`: the native analytic structures.
* `Matrix.SpecialLinearGroup.isSmoothEmbedding_coe`: the analytic matrix embedding.
* `Matrix.SpecialLinearGroup.contMDiff_coe`, `Matrix.SpecialLinearGroup.contMDiff_toGL`:
  analytic inclusions into matrices and the general linear group.
* `Matrix.SpecialLinearGroup.range_mvfderiv_coe_one`: the trace-zero tangent image.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Chapter 5, Corollary 5.14 (Regular Level Set Theorem), and Chapter 7, Example 7.18(c),(e).
-/

public noncomputable section

open Matrix Manifold Function
open scoped ContDiff Manifold Matrix.Norms.Operator
attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace Matrix.SpecialLinearGroup

/-- The model of dimension `card n * card n - 1` for the special linear group. -/
abbrev Model (n : Type*) [Fintype n] (𝕜 : Type*) :=
  Fin (Fintype.card n * Fintype.card n - 1) → 𝕜

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

private theorem contDiff_det {k : ℕ∞ω} : ContDiff 𝕜 k (det : Matrix n n 𝕜 → 𝕜) :=
  ContDiff.matrix_det fun i j ↦ (Matrix.entryLinearMap 𝕜 𝕜 i j).toContinuousLinearMap.contDiff

private theorem contMDiffAt_det {k : ℕ∞ω} (A : Matrix n n 𝕜) :
    ContMDiffAt 𝓘(𝕜, Matrix n n 𝕜) 𝓘(𝕜, 𝕜) k det A :=
  contDiff_det.contMDiff.contMDiffAt

omit [DecidableEq n] in
private theorem detLevelDimension :
    Module.finrank 𝕜 (Matrix n n 𝕜) - Module.finrank 𝕜 𝕜 =
      Fintype.card n * Fintype.card n - 1 := by
  simp [Module.finrank_matrix]

@[instance_reducible]
private def regularChartedSpace [Nonempty n] : ChartedSpace (Model n 𝕜) (SpecialLinearGroup n 𝕜) :=
  TauCeti.regularLevelChartedSpace (I := 𝓘(𝕜, Matrix n n 𝕜)) (M := Matrix n n 𝕜)
    (f := det) (c := 1) (n := Fintype.card n * Fintype.card n - 1)
    (fun x _ ↦ contMDiffAt_det x)
    (Matrix.isRegularValue_det (n := n) (𝕜 := 𝕜) one_ne_zero) detLevelDimension

private theorem isManifold_regularChartedSpace [Nonempty n] :
    let _ := regularChartedSpace (n := n) (𝕜 := 𝕜)
    IsManifold 𝓘(𝕜, Model n 𝕜) ω (SpecialLinearGroup n 𝕜) :=
  TauCeti.isManifold_regularLevel (n := Fintype.card n * Fintype.card n - 1) (by simp)
    (fun x _ ↦ contMDiffAt_det x)
    (Matrix.isRegularValue_det (n := n) (𝕜 := 𝕜) one_ne_zero) detLevelDimension

private theorem isSmoothEmbedding_coe_regularChartedSpace [Nonempty n] :
    let _ := regularChartedSpace (n := n) (𝕜 := 𝕜)
    Manifold.IsSmoothEmbedding (M := SpecialLinearGroup n 𝕜) (N := Matrix n n 𝕜)
      𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) ω
      (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) := by
  let := regularChartedSpace (n := n) (𝕜 := 𝕜)
  -- Keep the named SL carrier when elaborating the regular-level embedding theorem.
  have h : Manifold.IsSmoothEmbedding (M := SpecialLinearGroup n 𝕜) (N := Matrix n n 𝕜)
      𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) ω
      (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) :=
    TauCeti.isSmoothEmbedding_coe_regularLevel
      (I := 𝓘(𝕜, Matrix n n 𝕜)) (M := Matrix n n 𝕜) (f := det) (c := 1)
      (n := Fintype.card n * Fintype.card n - 1) (by simp)
      (fun x _ ↦ contMDiffAt_det x)
      (Matrix.isRegularValue_det (n := n) (𝕜 := 𝕜) one_ne_zero) detLevelDimension
  exact h

private theorem existsSLCharts :
    ∃ c : ChartedSpace (Model n 𝕜) (SpecialLinearGroup n 𝕜),
      letI := c
      IsManifold 𝓘(𝕜, Model n 𝕜) ω (SpecialLinearGroup n 𝕜) ∧
        Manifold.IsSmoothEmbedding 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) ω
          (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have : IsEmpty (Fin (Fintype.card n * Fintype.card n - 1)) := by
      simp only [Fintype.card_of_isEmpty, zero_mul, Nat.zero_sub]
      infer_instance
    let : ChartedSpace (Model n 𝕜) (SpecialLinearGroup n 𝕜) :=
      ChartedSpace.ofDiscreteTopology
    let : IsManifold 𝓘(𝕜, Model n 𝕜) ω (SpecialLinearGroup n 𝕜) :=
      IsManifold.of_discreteTopology ω
    exact ⟨inferInstance, inferInstance,
      contMDiff_of_subsingleton.isImmersion_of_injective_mfderiv (by simp)
        (fun x u v _ ↦
          (tangentSpaceCastModel 𝓘(𝕜, Model n 𝕜) x).injective (Subsingleton.elim _ _)), .subtypeVal⟩
  | inr hn =>
    let := regularChartedSpace (n := n) (𝕜 := 𝕜)
    exact ⟨inferInstance, isManifold_regularChartedSpace, isSmoothEmbedding_coe_regularChartedSpace⟩

/-- The native analytic charts on the special linear group. -/
@[instance_reducible]
instance instChartedSpace : ChartedSpace (Model n 𝕜) (SpecialLinearGroup n 𝕜) :=
  Classical.choose (show ∃ c : ChartedSpace (Model n 𝕜) (SpecialLinearGroup n 𝕜),
    letI := c
    IsManifold 𝓘(𝕜, Model n 𝕜) ω (SpecialLinearGroup n 𝕜) ∧
      Manifold.IsSmoothEmbedding 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) ω
        (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) from by exact existsSLCharts)

/-- The special linear group is an analytic manifold over its scalar field. -/
instance instIsManifold : IsManifold 𝓘(𝕜, Model n 𝕜) ω (SpecialLinearGroup n 𝕜) :=
  (Classical.choose_spec existsSLCharts).1

/-- The matrix inclusion of the special linear group is an analytic embedding. -/
theorem isSmoothEmbedding_coe :
    Manifold.IsSmoothEmbedding 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) ω
      (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) :=
  (Classical.choose_spec existsSLCharts).2

/-- The matrix inclusion of the special linear group has every differentiability order. -/
theorem contMDiff_coe {k : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) k
      (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) :=
  isSmoothEmbedding_coe.contMDiff.of_le le_top

/-- The inclusion of the special linear group into the general linear group is analytic. -/
theorem contMDiff_toGL {k : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜) k
      (SpecialLinearGroup.toGL : SpecialLinearGroup n 𝕜 → GL n 𝕜) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  simpa only [Function.comp_def, SpecialLinearGroup.coe_GL_coe_matrix] using
    (isSmoothEmbedding_coe (n := n) (𝕜 := 𝕜)).contMDiff.of_le (show k ≤ ω from le_top)

/-- The special linear group is an analytic Lie group over its scalar field. -/
instance instLieGroup : LieGroup 𝓘(𝕜, Model n 𝕜) ω (SpecialLinearGroup n 𝕜) := by
  have hi := (isSmoothEmbedding_coe (n := n) (𝕜 := 𝕜)).1
  exact
    { contMDiff_mul := (ContMDiff.iff_comp_isImmersion hi).2 ⟨continuous_mul, by
        refine (Units.contMDiff_val.comp
          (((contMDiff_toGL (n := n) (𝕜 := 𝕜)).comp contMDiff_fst).mul
            ((contMDiff_toGL (n := n) (𝕜 := 𝕜)).comp contMDiff_snd))).congr ?_
        intro p
        exact (SpecialLinearGroup.coe_mul p.1 p.2).trans
          (Units.val_mul (SpecialLinearGroup.toGL p.1) (SpecialLinearGroup.toGL p.2)).symm⟩
      contMDiff_inv := (ContMDiff.iff_comp_isImmersion hi).2 ⟨continuous_inv, by
        simpa only [Function.comp_def, ← map_inv, SpecialLinearGroup.coe_GL_coe_matrix] using
          Units.contMDiff_val.comp (contMDiff_toGL (n := n) (𝕜 := 𝕜)).inv⟩ }

/-- The tangent image at the identity consists exactly of the trace-zero matrices. -/
theorem range_mvfderiv_coe_one :
    (mvfderiv 𝓘(𝕜, Model n 𝕜)
      (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) 1).range =
      (Matrix.traceLinearMap n 𝕜 𝕜).ker := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn => exact Subsingleton.elim _ _
  | inr hn =>
    have hr := (Matrix.isRegularValue_det (n := n) (𝕜 := 𝕜) one_ne_zero).isRegularPoint
      (x := (1 : Matrix n n 𝕜)) (by simp)
    have heq := hr.range_mfderiv_eq_ker_mfderiv
      (g := fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) (p := 1)
      (.of_forall fun A ↦ A.2)
      ((isSmoothEmbedding_coe (n := n) (𝕜 := 𝕜)).1.mfderiv_injective (by simp) 1)
      (by
        simp only [Module.finrank_matrix, Module.finrank_self, Module.finrank_fin_fun, Model]
        have hp := Nat.mul_pos (Fintype.card_pos (α := n)) (Fintype.card_pos (α := n))
        omega)
    simp only [SpecialLinearGroup.coe_one] at heq
    have hker (v : TangentSpace 𝓘(𝕜, Matrix n n 𝕜) (1 : Matrix n n 𝕜)) :
        mfderiv 𝓘(𝕜, Matrix n n 𝕜) 𝓘(𝕜, 𝕜) det 1 v = 0 ↔
          Matrix.trace (NormedSpace.fromTangentSpace (1 : Matrix n n 𝕜) v) = 0 := by
      rw [← mvfderiv_apply_eq_mfderiv_apply, Matrix.mvfderiv_det_one]
      rfl
    ext B
    constructor
    · rintro ⟨v, rfl⟩
      have hv : mfderiv 𝓘(𝕜, Matrix n n 𝕜) 𝓘(𝕜, 𝕜) det 1
          (mfderiv 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜)
            (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) 1 v) = 0 :=
        (LinearMap.mem_ker).mp (heq.le ⟨v, rfl⟩)
      have hmv := mvfderiv_apply_eq_mfderiv_apply (I := 𝓘(𝕜, Model n 𝕜))
        (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) (1 : SpecialLinearGroup n 𝕜) v
      have htrace : trace (mfderiv 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜)
          (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) 1 v) = 0 := by
        simpa only [NormedSpace.fromTangentSpace_apply] using (hker _).mp hv
      rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply]
      exact (congrArg Matrix.trace hmv).trans htrace
    · intro hB
      have hv : (NormedSpace.fromTangentSpace (1 : Matrix n n 𝕜)).symm B ∈
          (mfderiv 𝓘(𝕜, Model n 𝕜) 𝓘(𝕜, Matrix n n 𝕜)
            (fun A : SpecialLinearGroup n 𝕜 ↦ (A : Matrix n n 𝕜)) 1).range := by
        rw [heq, LinearMap.mem_ker]
        apply (hker _).mpr
        simpa only [ContinuousLinearEquiv.apply_symm_apply, LinearMap.mem_ker,
          Matrix.traceLinearMap_apply] using hB
      obtain ⟨v, hv⟩ := hv
      exact ⟨v, by simpa only [mvfderiv, ContinuousLinearMap.comp_apply, hv,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]⟩

end Matrix.SpecialLinearGroup
