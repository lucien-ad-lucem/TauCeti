/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SU2.LieAlgebra
public import TauCeti.RepresentationTheory.Compact.BilinearForm
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
/-!
# The weighted compact SU(2) metric example

This example uses the native Lie algebra of the special unitary subgroup of GL₂. Its Pauli
coordinates have the actual native group adjoint, as proved in
`TauCeti.SU2.adjointRepresentation_pauliLieAlgebraEquiv`. Averaging a diagonal form gives the
mean of its weights times the standard form.

The weighted example's basis is z, x, y, so its weights (1, 2, 3) become (2, 3, 1) in native
Pauli order.
The starting and averaged adjoint-pairing values are respectively minus six/four and minus
four/four, while the actual Killing form takes the value minus eight on the first basis vector.

## Main definitions

* `TauCeti.Examples.LieGroups.su2PauliForm`: the starting diagonal form on the native Lie algebra.

## Main results

* `TauCeti.Examples.LieGroups.su2_integral_pauliForm`: the native inverse-adjoint Haar integral.
* `TauCeti.Examples.LieGroups.su2_weightedPauliForm_skew_values`: the explicit adjoint
  pairings and Killing-form value.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), Lemma 10.4.14, for Haar averaging.
-/

public noncomputable section

open Matrix TauCeti TauCeti.Lie MeasureTheory
open scoped ContDiff Manifold Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
namespace TauCeti.Examples.LieGroups

-- Cache the canonical group properties with the matrix operator norm in scope.
private local instance : IsTopologicalGroup SU2 :=
  TauCeti.Matrix.instIsTopologicalGroupSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti

private local instance : CompactSpace SU2 :=
  TauCeti.Matrix.instCompactSpaceSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti

private def action : ContRepresentation ℝ SU2 (Fin 3 → ℝ) where
  toMonoidHom := {
   toFun g := (Matrix.toLin' (SU2.toSO3 g : Matrix (Fin 3) (Fin 3) ℝ)).toContinuousLinearMap
   map_one' := by
    ext x i
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
    simp
   map_mul' g h := by
    ext x i
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
    simp [Matrix.mulVec_mulVec] }

private theorem action_apply (g : SU2) (x : Fin 3 → ℝ) :
    action g x = (SU2.toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x := rfl

private theorem continuous_action : Continuous action := by
  let L : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] ((Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toLin'.toLinearMap
  exact L.continuous_of_finiteDimensional.comp
    (continuous_subtype_val.comp SU2.continuous_toSO3)

private def form (weights : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (Matrix.toBilin' (Matrix.diagonal weights)).toContinuousBilinearMap

private theorem form_apply (weights x y : Fin 3 → ℝ) :
    form weights x y = ∑ i, weights i * x i * y i := by
  simp [form, Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal,
    mul_comm, mul_left_comm]

private theorem form_one (x y : Fin 3 → ℝ) : form (fun _ ↦ 1) x y = x ⬝ᵥ y := by
  simp [form_apply, dotProduct]

private def cycle : Matrix (Fin 3) (Fin 3) ℝ := !![0,1,0; 0,0,1; 1,0,0]

private theorem cycle_mem : cycle ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  constructor
  · apply (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mpr
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [cycle, Matrix.mul_apply, Fin.sum_univ_three]
  · norm_num [cycle, Matrix.det_fin_three]

private theorem form_one_invariant :
    Representation.IsInvariantForm action.toRepresentation (form (fun _ ↦ 1)).toBilinForm := by
  apply Representation.isInvariantForm_iff.mpr
  intro g x y
  have hρ (g : SU2) (v : Fin 3 → ℝ) :
      (action.toRepresentation : Representation ℝ SU2 (Fin 3 → ℝ)) g v = action g v := rfl
  simp only [ContinuousLinearMap.toBilinForm_apply, hρ]
  rw [form_one, form_one, action_apply, action_apply]
  simp only [SU2.coe_toSO3]
  exact dotProduct_pauliRotation_mulVec _ x y

private theorem cycle_sum (weights : Fin 3 → ℝ) :
    ∃ g : SU2, form weights + (form weights).bilinearComp (action g) (action g) +
      (form weights).bilinearComp (action (g * g)) (action (g * g)) =
        (weights 0 + weights 1 + weights 2) • form (fun _ ↦ 1) := by
  obtain ⟨g, hg⟩ := SU2.toSO3_surjective ⟨cycle, cycle_mem⟩
  have hgc : (SU2.toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) = cycle :=
    congrArg Subtype.val hg
  have hgcc : (SU2.toSO3 (g * g) : Matrix (Fin 3) (Fin 3) ℝ) = cycle * cycle := by
    simp [hgc]
  refine ⟨g, ?_⟩
  ext x y
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.bilinearComp_apply, action_apply, hgc, hgcc, form_apply,
    Fin.sum_univ_three, smul_eq_mul]
  simp [cycle, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

private theorem average_form (weights : Fin 3 → ℝ) (x y : Fin 3 → ℝ) :
    letI : MeasurableSpace SU2 := borel SU2
    letI : BorelSpace SU2 := ⟨rfl⟩
    ContRepresentation.averageBilinearForm action continuous_action (form weights) x y =
      (weights 0 + weights 1 + weights 2) / 3 * (x ⬝ᵥ y) := by
  let : MeasurableSpace SU2 := borel SU2
  let : BorelSpace SU2 := ⟨rfl⟩
  obtain ⟨g, hg⟩ := cycle_sum weights
  have h := congrArg (ContRepresentation.averageBilinearForm action continuous_action) hg
  simp only [map_add, map_smul, ContRepresentation.averageBilinearForm_bilinearComp,
    ContRepresentation.averageBilinearForm_eq_self action continuous_action _
      form_one_invariant] at h
  have he := congrArg (fun B ↦ B x y) h
  simp only [add_apply, smul_apply,
    smul_eq_mul, form_one] at he
  linarith

private theorem integral_weighted (weights x y : Fin 3 → ℝ) :
    letI : MeasurableSpace SU2 := borel SU2
    letI : BorelSpace SU2 := ⟨rfl⟩
    (∫ g : SU2, ∑ i, weights i *
      ((SU2.toSO3 g⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) i *
      ((SU2.toSO3 g⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ y) i ∂haarProb SU2) =
      (weights 0 + weights 1 + weights 2) / 3 * (x ⬝ᵥ y) := by
  let : MeasurableSpace SU2 := borel SU2
  let : BorelSpace SU2 := ⟨rfl⟩
  rw [← average_form]
  rw [ContRepresentation.averageBilinearForm_apply]
  simp only [form_apply, action_apply]

local notation "S" => lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℂ))
  (GLSpecialUnitary (Fin 2) ℂ)

/-- A diagonal Pauli form, transported to the native real SU(2) Lie algebra. -/
def su2PauliForm (weights : Fin 3 → ℝ) : LinearMap.BilinForm ℝ S :=
  (Matrix.toBilin' (Matrix.diagonal weights)).compl₁₂
    SU2.pauliLieAlgebraEquiv.symm.toLinearMap SU2.pauliLieAlgebraEquiv.symm.toLinearMap

/-- Evaluation of a Pauli form on native Pauli Lie-algebra elements. -/
@[simp]
theorem su2PauliForm_apply (weights x y : Fin 3 → ℝ) :
    su2PauliForm weights (SU2.pauliLieAlgebraEquiv x) (SU2.pauliLieAlgebraEquiv y) =
      ∑ i, weights i * x i * y i := by
  simp [su2PauliForm, LinearMap.compl₁₂_apply, Matrix.toBilin'_apply', dotProduct,
    Matrix.mulVec_diagonal, mul_comm, mul_left_comm]

/-- Every diagonal Pauli form is symmetric. -/
theorem su2PauliForm_isSymm (weights : Fin 3 → ℝ) : (su2PauliForm weights).IsSymm := by
  constructor
  intro X Y
  obtain ⟨x, rfl⟩ := SU2.pauliLieAlgebraEquiv.surjective X
  obtain ⟨y, rfl⟩ := SU2.pauliLieAlgebraEquiv.surjective Y
  simp only [su2PauliForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Strictly positive coordinate weights give a positive-definite native form. -/
theorem su2PauliForm_posDef (weights : Fin 3 → ℝ) (hweights : ∀ i, 0 < weights i) :
    (su2PauliForm weights).toQuadraticMap.PosDef := by
  intro X hX
  obtain ⟨x, rfl⟩ := SU2.pauliLieAlgebraEquiv.surjective X
  rw [LinearMap.BilinMap.toQuadraticMap_apply, su2PauliForm_apply]
  have hx : x ≠ 0 := by
    intro hx
    apply hX
    rw [hx, map_zero]
  have hnonneg (i : Fin 3) : 0 ≤ weights i * x i * x i := by
    nlinarith [mul_nonneg (hweights i).le (sq_nonneg (x i))]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by simpa only [ne_eq, funext_iff, Pi.zero_apply,
    not_forall] using hx
  apply Finset.sum_pos' (fun j _ ↦ hnonneg j)
  refine ⟨i, Finset.mem_univ _, ?_⟩
  nlinarith [mul_pos (hweights i) (sq_pos_of_ne_zero hi)]

/-- The weighted form gives pairings minus six and four for the first adjoint operator, while
its Haar average gives minus four and four. The Killing form takes minus eight on that vector. -/
theorem su2_weightedPauliForm_skew_values :
    let e₁ := SU2.pauliLieAlgebraEquiv (Pi.single 2 1)
    let e₂ := SU2.pauliLieAlgebraEquiv (Pi.single 0 1)
    let e₃ := SU2.pauliLieAlgebraEquiv (Pi.single 1 1)
    su2PauliForm ![2, 3, 1] ⁅e₁, e₂⁆ e₃ = -6 ∧
      su2PauliForm ![2, 3, 1] e₂ ⁅e₁, e₃⁆ = 4 ∧
      (2 • su2PauliForm (fun _ ↦ 1)) ⁅e₁, e₂⁆ e₃ = -4 ∧
      (2 • su2PauliForm (fun _ ↦ 1)) e₂ ⁅e₁, e₃⁆ = 4 ∧
      killingForm ℝ S e₁ e₁ = -8 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [SU2.pauliLieAlgebraEquiv_lie, su2PauliForm_apply,
      SU2.killingForm_pauliLieAlgebraEquiv, cross_apply, dotProduct, Fin.sum_univ_three]

/-- The normalized Haar integral of the actual native inverse-adjoint pullbacks is the mean
weight times the standard native Pauli form. -/
theorem su2_integral_pauliForm (weights : Fin 3 → ℝ) (X Y : S) :
    letI : IsTopologicalGroup SU2 :=
      TauCeti.Matrix.instIsTopologicalGroupSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti
    letI : CompactSpace SU2 :=
      TauCeti.Matrix.instCompactSpaceSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti
    letI : MeasurableSpace SU2 := borel SU2
    letI : BorelSpace SU2 := ⟨rfl⟩
    (∫ g : SU2, su2PauliForm weights
      (SU2.adjointRepresentation g⁻¹ X) (SU2.adjointRepresentation g⁻¹ Y) ∂haarProb SU2) =
      (weights 0 + weights 1 + weights 2) / 3 * su2PauliForm (fun _ ↦ 1) X Y := by
  let : IsTopologicalGroup SU2 :=
    TauCeti.Matrix.instIsTopologicalGroupSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti
  let : CompactSpace SU2 :=
    TauCeti.Matrix.instCompactSpaceSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti
  let : MeasurableSpace SU2 := borel SU2
  let : BorelSpace SU2 := ⟨rfl⟩
  obtain ⟨x, rfl⟩ := SU2.pauliLieAlgebraEquiv.surjective X
  obtain ⟨y, rfl⟩ := SU2.pauliLieAlgebraEquiv.surjective Y
  simp only [SU2.adjointRepresentation_pauliLieAlgebraEquiv, su2PauliForm_apply,
    one_mul]
  simpa only [dotProduct] using integral_weighted weights x y
/-- In the ordered basis z, x, y and with starting weights (1, 2, 3), the actual normalized
Haar average has Gram matrix twice the identity. -/
theorem su2_integral_weightedPauliBasis (j k : Fin 3) :
    letI : IsTopologicalGroup SU2 :=
      TauCeti.Matrix.instIsTopologicalGroupSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti
    letI : CompactSpace SU2 :=
      TauCeti.Matrix.instCompactSpaceSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti
    letI : MeasurableSpace SU2 := borel SU2
    letI : BorelSpace SU2 := ⟨rfl⟩
    let X := SU2.pauliLieAlgebraEquiv (Pi.single (![(2 : Fin 3), 0, 1] j) 1)
    let Y := SU2.pauliLieAlgebraEquiv (Pi.single (![(2 : Fin 3), 0, 1] k) 1)
    (∫ g : SU2, su2PauliForm ![2, 3, 1]
      (SU2.adjointRepresentation g⁻¹ X) (SU2.adjointRepresentation g⁻¹ Y) ∂haarProb SU2) =
      if j = k then 2 else 0 := by
  let : IsTopologicalGroup SU2 :=
    TauCeti.Matrix.instIsTopologicalGroupSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti
  let : CompactSpace SU2 :=
    TauCeti.Matrix.instCompactSpaceSubtypeMatrixMemSubmonoidSpecialUnitaryGroup_tauCeti
  let : MeasurableSpace SU2 := borel SU2
  let : BorelSpace SU2 := ⟨rfl⟩
  dsimp only
  rw [su2_integral_pauliForm]
  fin_cases j <;> fin_cases k <;> norm_num [su2PauliForm_apply, Fin.sum_univ_three]

end TauCeti.Examples.LieGroups
