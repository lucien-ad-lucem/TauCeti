/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Averaging
public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.RepresentationTheory.InvariantForm
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Haar averaging of real bilinear forms

A continuous representation of a compact group averages each given continuous real bilinear
form by pulling both arguments back through the inverse action and integrating against normalized
Haar measure. The average is a continuous bilinear form, and the operation is continuous and linear
in the starting form. It preserves symmetry and strict positive definiteness on arbitrary real
normed spaces, without requiring the representation space to be complete or finite-dimensional.

## Main definitions

* `ContRepresentation.averageBilinearForm`: Haar averaging as an operator on continuous forms.

## Main results

* `ContRepresentation.averageBilinearForm_apply`: the inverse-action integral formula.
* `ContRepresentation.isInvariantForm_averageBilinearForm`: the averaged form is invariant.
* `ContRepresentation.isSymm_averageBilinearForm` and
  `ContRepresentation.posDef_averageBilinearForm`: symmetry and positivity are preserved.
* `ContRepresentation.averageBilinearForm_eq_self_iff`: averaging fixes exactly invariant forms.
* `ContRepresentation.averageBilinearForm_idempotent`: averaging is a projection.
* `ContRepresentation.averageBilinearForm_bilinearComp`: pulling back the input by an action
  operator does not change its average.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), Lemma 10.4.14, for the invariant-inner-product construction.
-/

public noncomputable section

open MeasureTheory TauCeti

namespace ContRepresentation

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

-- Cache the canonical instances so nested operator spaces stay within instance-search depth.
private local instance normedBilinear : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance normedSpaceBilinear : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable (π : ContRepresentation ℝ G V) (hπ : Continuous π)

include hπ

/-- The orbit of a form under simultaneous pullback of its arguments. -/
private def bilinearOrbit (B : V →L[ℝ] V →L[ℝ] ℝ) :
    C(G, V →L[ℝ] V →L[ℝ] ℝ) where
  toFun g := B.bilinearComp (π g⁻¹) (π g⁻¹)
  continuous_toFun := by
    have hi := hπ.comp continuous_inv
    have hf := (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).continuous.comp (hi.const_clm_comp B)
    exact (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).continuous.comp
      (((ContinuousLinearMap.compL ℝ V V (V →L[ℝ] ℝ)).continuous.comp hf).clm_apply hi)

@[simp]
private theorem bilinearOrbit_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (g : G) (v w : V) :
    bilinearOrbit π hπ B g v w = B (π g⁻¹ v) (π g⁻¹ w) := by
  rfl

variable [CompactSpace G]

/-- The orbit family depends continuously and linearly on the starting form. -/
private def bilinearOrbitL :
    (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] C(G, V →L[ℝ] V →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := bilinearOrbit π hπ
      map_add' := fun B C ↦ by ext g v w; rfl
      map_smul' := fun c B ↦ by ext g v w; rfl }
    (‖(⟨π, hπ⟩ : C(G, V →L[ℝ] V))‖ ^ 2) fun B ↦ by
      let K := ‖(⟨π, hπ⟩ : C(G, V →L[ℝ] V))‖
      apply ((bilinearOrbit π hπ B).norm_le
        (mul_nonneg (sq_nonneg K) (norm_nonneg B))).mpr
      intro g
      have hK : 0 ≤ K := norm_nonneg (⟨π, hπ⟩ : C(G, V →L[ℝ] V))
      have hg : ‖π g⁻¹‖ ≤ K := (⟨π, hπ⟩ : C(G, V →L[ℝ] V)).norm_coe_le_norm g⁻¹
      calc
        ‖bilinearOrbit π hπ B g‖ = ‖((B.comp (π g⁻¹)).flip.comp (π g⁻¹))‖ := by
          simp only [bilinearOrbit, ContinuousMap.coe_mk, ContinuousLinearMap.bilinearComp,
            ContinuousLinearMap.opNorm_flip]
        _ ≤ K ^ 2 * ‖B‖ := by
          have hcomp : ‖B.comp (π g⁻¹)‖ ≤ ‖B‖ * K := by
            apply (ContinuousLinearMap.opNorm_comp_le B (π g⁻¹)).trans
            gcongr
          calc
            _ ≤ ‖B.comp (π g⁻¹)‖ * ‖π g⁻¹‖ := by
              simpa only [ContinuousLinearMap.opNorm_flip] using
                ContinuousLinearMap.opNorm_comp_le (B.comp (π g⁻¹)).flip (π g⁻¹)
            _ ≤ (‖B‖ * K) * K := by gcongr
            _ = K ^ 2 * ‖B‖ := by ring

/-- Evaluation of the continuous operator producing the orbit family. -/
private theorem bilinearOrbitL_apply (B : V →L[ℝ] V →L[ℝ] ℝ) :
    bilinearOrbitL π hπ B = bilinearOrbit π hπ B := by
  rfl

variable [MeasurableSpace G] [BorelSpace G]

/-- Average a given real continuous bilinear form against normalized Haar measure, using
inverse-action pullback. This is a continuous linear operator on the space of forms. -/
def averageBilinearForm : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ :=
  (haarAverage G).comp (bilinearOrbitL π hπ)

/-- The averaged form is the integral of the inverse-action pullbacks of the starting form.
The integral formula is an explicit rewrite; the averaged form is the default normal form. -/
theorem averageBilinearForm_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (v w : V) :
    averageBilinearForm π hπ B v w =
      ∫ g, B (π g⁻¹ v) (π g⁻¹ w) ∂haarProb G := by
  rw [averageBilinearForm, ContinuousLinearMap.comp_apply, bilinearOrbitL_apply]
  have h := ((ContinuousLinearMap.apply ℝ ℝ w).comp
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) v)).haarAverage_comp_comm
      (G := G) (bilinearOrbit π hπ B)
  simpa only [ContinuousLinearMap.comp_apply, haarAverage_apply, ContinuousMap.coe_comp,
    ContinuousMap.coe_ofClass, Function.comp_apply, ContinuousLinearMap.apply_apply,
    bilinearOrbit_apply] using h.symm

/-- The Haar-averaged form is invariant under the original representation. -/
theorem isInvariantForm_averageBilinearForm (B : V →L[ℝ] V →L[ℝ] ℝ) :
    Representation.IsInvariantForm π.toRepresentation
      (averageBilinearForm π hπ B).toBilinForm := by
  apply Representation.isInvariantForm_iff.mpr
  intro h v w
  have hρ (g : G) (x : V) : (π.toRepresentation : Representation ℝ G V) g x = π g x := rfl
  simp only [ContinuousLinearMap.toBilinForm_apply, hρ]
  rw [averageBilinearForm_apply, averageBilinearForm_apply]
  let f := fun g : G ↦ B (π g⁻¹ v) (π g⁻¹ w)
  calc
    _ = ∫ g, f (h⁻¹ * g) ∂haarProb G := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g ↦ by
        simp only [f, mul_inv_rev, inv_inv, map_mul, mul_apply_eq_comp]
    _ = _ := integral_mul_left_eq_self f h⁻¹

/-- Averaging preserves symmetry of a continuous real bilinear form. -/
theorem isSymm_averageBilinearForm (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : B.toBilinForm.IsSymm) :
    (averageBilinearForm π hπ B).toBilinForm.IsSymm := by
  constructor
  intro v w
  simp only [ContinuousLinearMap.toBilinForm_apply]
  rw [averageBilinearForm_apply, averageBilinearForm_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g ↦ hB.eq _ _)

/-- Averaging preserves positive definiteness, without requiring symmetry of the input. -/
theorem posDef_averageBilinearForm (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : B.toBilinForm.toQuadraticMap.PosDef) :
    (averageBilinearForm π hπ B).toBilinForm.toQuadraticMap.PosDef := by
  intro v hv
  rw [LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply,
    averageBilinearForm_apply]
  have hp (g : G) : 0 < B (π g⁻¹ v) (π g⁻¹ v) := by
    have hn : π g⁻¹ v ≠ 0 := by
      intro hzero
      have hc : π g (π g⁻¹ v) = v := Representation.self_inv_apply π.toRepresentation g v
      rw [hzero, map_zero] at hc
      exact hv hc.symm
    simpa only [LinearMap.BilinMap.toQuadraticMap_apply,
      ContinuousLinearMap.toBilinForm_apply] using hB (π g⁻¹ v) hn
  have hi : Integrable (fun g ↦ B (π g⁻¹ v) (π g⁻¹ v)) (haarProb G) := by
    apply TauCeti.integrable_continuousMap G
      (⟨fun g ↦ B (π g⁻¹ v) (π g⁻¹ v), ?_⟩ : C(G, ℝ))
    have hInv := hπ.comp continuous_inv
    exact (B.continuous.comp (hInv.clm_apply continuous_const)).clm_apply
      (hInv.clm_apply continuous_const)
  apply (integral_pos_iff_support_of_nonneg (fun g ↦ (hp g).le) hi).mpr
  have hs : Function.support (fun g : G ↦ B (π g⁻¹ v) (π g⁻¹ v)) = Set.univ := by
    ext g
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (hp g)
  rw [hs, measure_univ]
  exact zero_lt_one

/-- Averaging fixes every invariant continuous bilinear form. -/
@[simp]
theorem averageBilinearForm_eq_self (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : Representation.IsInvariantForm π.toRepresentation B.toBilinForm) :
    averageBilinearForm π hπ B = B := by
  ext v w
  rw [averageBilinearForm_apply]
  have hB' (g : G) : B (π g v) (π g w) = B v w := hB.apply g v w
  simp only [hB', integral_const, probReal_univ, one_smul]

/-- A continuous bilinear form is fixed by averaging exactly when it is invariant. -/
theorem averageBilinearForm_eq_self_iff (B : V →L[ℝ] V →L[ℝ] ℝ) :
    averageBilinearForm π hπ B = B ↔
      Representation.IsInvariantForm π.toRepresentation B.toBilinForm := by
  refine ⟨fun h ↦ ?_, averageBilinearForm_eq_self π hπ B⟩
  rw [← h]
  exact isInvariantForm_averageBilinearForm π hπ B

/-- Haar averaging is idempotent on continuous real bilinear forms. -/
@[simp]
theorem averageBilinearForm_idempotent (B : V →L[ℝ] V →L[ℝ] ℝ) :
    averageBilinearForm π hπ (averageBilinearForm π hπ B) = averageBilinearForm π hπ B :=
  averageBilinearForm_eq_self π hπ _ (isInvariantForm_averageBilinearForm π hπ B)

/-- Averaging is unchanged if the starting form is pulled back by an action operator. -/
@[simp]
theorem averageBilinearForm_bilinearComp (B : V →L[ℝ] V →L[ℝ] ℝ) (h : G) :
    averageBilinearForm π hπ (B.bilinearComp (π h) (π h)) = averageBilinearForm π hπ B := by
  ext v w
  rw [averageBilinearForm_apply, averageBilinearForm_apply]
  let f := fun g : G ↦ B (π g⁻¹ v) (π g⁻¹ w)
  calc
    _ = ∫ g, f (g * h⁻¹) ∂haarProb G := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g ↦ by
        simp only [ContinuousLinearMap.bilinearComp_apply, f, mul_inv_rev, inv_inv,
          map_mul, mul_apply_eq_comp]
    _ = _ := integral_mul_right_eq_self f h⁻¹

end ContRepresentation
