/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.Analysis.SpecialFunctions.Exponential
public import TauCeti.LinearAlgebra.Matrix.Block
import Mathlib.Topology.UniformSpace.Matrix
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# The exponential of an upper block triangular matrix

The exponential of `[[A, B], [0, D]]` has diagonal blocks `exp A` and `exp D` and upper-right
block `∫ t in 0..1, exp ((1-t) • A) * B * exp (t • D)`. The formula holds over every complete
real normed algebra, with no commutation assumption on the blocks and with empty blocks allowed.
For block-diagonal matrices, exponentiation commutes with forming the blocks over any complete
rational normed coefficient algebra.

For a final one-dimensional block `D`, this describes the last column of the exponential as a
linear function of `B`, which is the off-diagonal step in constructing triangular logarithms.

## Main results

* `Matrix.exp_fromBlocks_diagonal`: the exponential of a block-diagonal matrix.
* `Matrix.exp_fromBlocks_zero₂₁`: the exponential of an upper two-block matrix, with the
  off-diagonal block given by its exponential-weight integral.

## References

* C. F. Van Loan, *Computing Integrals Involving the Matrix Exponential*, IEEE Transactions
  on Automatic Control 23(3) (1978), 395–404, Theorem 1, pp. 395–396,
  DOI: 10.1109/TAC.1978.1101743.
-/

public section

noncomputable section

attribute [local instance] TauCeti.normedAlgebraRatOfReal

open NormedSpace

namespace Matrix

open scoped Matrix.Norms.Operator

variable {R m n : Type*} [NormedRing R] [CompleteSpace R]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

-- The operator norm and product uniformities on finite matrices coincide.
private local instance matrixCompleteSpace {p q : Type*} [Fintype p] [Fintype q] :
    @CompleteSpace (Matrix p q R)
      (Matrix.linftyOpNormedAddCommGroup (m := p) (n := q) (α := R)).toUniformSpace :=
  inferInstanceAs (CompleteSpace (p → q → R))

section Rational

variable [NormedAlgebra ℚ R]

private theorem exp_entry_hasSum {l : Type*} [Fintype l] [DecidableEq l]
    (M : Matrix l l R) (i j : l) :
    HasSum (fun k : ℕ ↦ (k.factorial⁻¹ : ℚ) • (M^k) i j) (exp M i j) := by
  let e := Matrix.entryLinearMap ℚ R i j
  have he : Continuous e := continuous_id.matrix_elem i j
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℚ) M).map e.toAddMonoidHom he
  refine h.congr (fun k ↦ ?_)
  simp [e]

private theorem exp_apply_eq_of_pow_apply_eq {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (M : Matrix p p R) (N : Matrix q q R) (i j : p) (u v : q)
    (hp : ∀ k : ℕ, (M ^ k) i j = (N ^ k) u v) : exp M i j = exp N u v := by
  have h := exp_entry_hasSum M i j
  simp only [hp] at h
  exact h.unique (exp_entry_hasSum N u v)

private theorem exp_corner11 (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R)
    (i j : m) : exp (fromBlocks A B 0 D) (Sum.inl i) (Sum.inl j) = exp A i j := by
  apply exp_apply_eq_of_pow_apply_eq
  intro k
  rw [fromBlocks_zero₂₁_pow, fromBlocks_apply₁₁]

private theorem exp_corner22 (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R)
    (i j : n) : exp (fromBlocks A B 0 D) (Sum.inr i) (Sum.inr j) = exp D i j := by
  apply exp_apply_eq_of_pow_apply_eq
  intro k
  rw [fromBlocks_zero₂₁_pow, fromBlocks_apply₂₂]

omit [CompleteSpace R] in
private theorem exp_corner21 (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R)
    (i : n) (j : m) : exp (fromBlocks A B 0 D) (Sum.inr i) (Sum.inl j) = 0 := by
  exact (upper_two_blockTriangular A B D (show (0 : ℕ) < 1 by decide)).exp
    (i := Sum.inr i) (j := Sum.inl j) (by simp)

private theorem exp_upper_structure (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    ∃ C : Matrix m n R, exp (fromBlocks A B 0 D) = fromBlocks (exp A) C 0 (exp D) := by
  refine ⟨(exp (fromBlocks A B 0 D)).toBlocks₁₂, ?_⟩
  ext (i | i) (j | j)
  · exact exp_corner11 A B D i j
  · rfl
  · exact exp_corner21 A B D i j
  · exact exp_corner22 A B D i j

/-- The exponential of a two-block diagonal matrix is block diagonal. A normed rational-algebra
structure on the coefficient ring suffices. -/
theorem exp_fromBlocks_diagonal (A : Matrix m m R) (D : Matrix n n R) :
    exp (fromBlocks A 0 0 D) = fromBlocks (exp A) 0 0 (exp D) := by
  ext (i | i) (j | j)
  · exact exp_corner11 A 0 D i j
  · have h := exp_entry_hasSum (fromBlocks A 0 0 D) (Sum.inl i) (Sum.inr j)
    simp only [fromBlocks_diagonal_pow, fromBlocks_apply₁₂, Matrix.zero_apply, smul_zero] at h
    exact h.unique hasSum_zero
  · exact exp_corner21 A 0 D i j
  · exact exp_corner22 A 0 D i j

end Rational

section Real

variable [NormedAlgebra ℝ R]

omit [CompleteSpace R] [DecidableEq m] [DecidableEq n] in
/-- Insert a rectangular matrix into the upper-right block of a square matrix. -/
private def upperRightCLM : Matrix m n R →L[ℝ] Matrix (m ⊕ n) (m ⊕ n) R :=
  { toLinearMap :=
      { toFun := fun X ↦ fromBlocks 0 X 0 0
        map_add' := fun X Y ↦ by simp only [fromBlocks_add, zero_add]
        map_smul' := fun c X ↦ by simp only [fromBlocks_smul, smul_zero, RingHom.id_apply] }
    cont := continuous_matrix fun i j ↦ by
      cases i <;> cases j
      · exact continuous_const
      · exact continuous_id.matrix_elem _ _
      · exact continuous_const
      · exact continuous_const }

omit [CompleteSpace R] [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] in
@[simp] private theorem upperRightCLM_apply (X : Matrix m n R) :
    upperRightCLM X = fromBlocks 0 X 0 0 := rfl

/-- The exponential of an upper two-block matrix. The off-diagonal block is an integral of the
left and right diagonal exponential weights, with no commutation hypotheses. -/
theorem exp_fromBlocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    exp (fromBlocks A B 0 D) =
      fromBlocks (exp A)
        (∫ t in (0 : ℝ)..1, exp ((1 - t) • A) * B * exp (t • D)) 0 (exp D) := by
  let E := upperRightCLM (R := R) (m := m) (n := n)
  let x := fromBlocks A (0 : Matrix m n R) 0 D
  let h := fromBlocks (0 : Matrix m m R) B 0 (0 : Matrix n n R)
  have hsum : x + h = fromBlocks A B 0 D := by simp [x, h, fromBlocks_add]
  have hm (t : ℝ) : exp ((1 - t) • (x + h)) * h * exp (t • x) =
      E (exp ((1 - t) • A) * B * exp (t • D)) := by
    simp only [hsum, x, h, fromBlocks_smul, smul_zero]
    obtain ⟨C, hC⟩ := exp_upper_structure ((1 - t) • A) ((1 - t) • B) ((1 - t) • D)
    rw [hC, exp_fromBlocks_diagonal]
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      E, upperRightCLM_apply]
  -- Select the norm-induced extended norm: the rectangular matrix default can follow
  -- a different instance path from the operator norm used by the integral.
  let _ : ENormedAddMonoid (Matrix m n R) := NormedAddGroup.toENormedAddMonoid
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ exp ((1 - t) • A) * B * exp (t • D)) MeasureTheory.volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) 0 1
  have hd : exp (x + h) - exp x =
      ∫ t in (0 : ℝ)..1, exp ((1 - t) • (x + h)) * h * exp (t • x) :=
    TauCeti.exp_add_sub_exp_eq_integral x h
  simp_rw [hm] at hd
  have hcomm : (∫ t in (0 : ℝ)..1, E (exp ((1 - t) • A) * B * exp (t • D))) =
      E (∫ t in (0 : ℝ)..1, exp ((1 - t) • A) * B * exp (t • D)) :=
    E.intervalIntegral_comp_comm hint
  rw [hcomm] at hd
  rw [hsum] at hd
  simp only [x, exp_fromBlocks_diagonal] at hd
  have heq := sub_eq_iff_eq_add.mp hd
  simpa only [E, upperRightCLM_apply, fromBlocks_add, zero_add, add_zero] using heq

end Real

end Matrix
