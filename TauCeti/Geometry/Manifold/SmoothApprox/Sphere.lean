/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Topology.Circle.Loop
public import Mathlib.Topology.Homotopy.Path
import Mathlib.Geometry.Manifold.SmoothApprox
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.AlgebraicTopology.Sphere.Puncture
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Smooth based loops in spheres

Every continuous based loop in a finite-dimensional unit sphere is homotopic, with its
basepoint fixed, to a loop whose map from `Circle` is smooth. Smoothness is asserted on the
circle, including across the identified endpoints of the interval.

The proof applies vector-valued Whitney approximation to the ambient circle map. Subtracting
its error at `1` fixes the basepoint exactly; radial projection returns it to the sphere.
The approximation is close enough that the pointwise straight segments avoid the origin, so
normalizing those segments gives a based path homotopy. No regularity of the original loop
near the basepoint is required.

## Main results

* `Path.exists_homotopic_contMDiff_toCircle`: a smooth circle representative of a based loop.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorems 6.21 and 6.26 (Whitney approximation and normalized straight-line homotopies).
-/

public noncomputable section

open Set Metric NormedSpace TauCeti
open scoped Manifold ContDiff unitInterval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

/-- Every continuous based loop in a finite-dimensional unit sphere is based-homotopic to a
loop whose factorization through the unit circle is smooth. -/
theorem Path.exists_homotopic_contMDiff_toCircle
    {x : sphere (0 : E) 1} (γ : Path x x) :
    ∃ γ' : Path x x, γ.Homotopic γ' ∧ ContMDiff (𝓡 1) (𝓡 n) ∞ γ'.toCircle := by
  let F : C(Circle, E) :=
    ⟨fun z ↦ (γ.toCircle z : E), continuous_subtype_val.comp γ.toCircle.continuous⟩
  obtain ⟨G, hG, -⟩ := F.continuous.exists_contMDiff_approx (𝓡 1) (⊤ : ℕ∞)
    (ε := fun _ ↦ (1 / 8 : ℝ)) continuous_const (fun _ ↦ by norm_num)
  -- Correct the single basepoint error without losing smoothness.
  let c : Circle → E := fun z ↦ G z - G 1 + (x : E)
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ c :=
    (G.contMDiff.sub contMDiff_const).add contMDiff_const
  have hc1 : c 1 = (x : E) := by simp [c]
  have hG1 : ‖G 1 - (x : E)‖ < 1 / 8 := by
    simpa only [F, ContinuousMap.coe_mk, γ.toCircle_one, dist_eq_norm] using hG 1
  have hclose (z : Circle) : ‖c z - (γ.toCircle z : E)‖ < 1 := by
    have hGz : ‖G z - (γ.toCircle z : E)‖ < 1 / 8 := by
      simpa only [F, ContinuousMap.coe_mk, dist_eq_norm] using hG z
    have heq : c z - (γ.toCircle z : E) =
        (G z - (γ.toCircle z : E)) - (G 1 - (x : E)) := by
      dsimp only [c]
      abel
    rw [heq]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hc0 (z : Circle) : c z ≠ 0 := by
    intro hz
    have h := hclose z
    rw [hz, zero_sub, norm_neg, mem_sphere_zero_iff_norm.mp (γ.toCircle z).property] at h
    exact lt_irrefl 1 h
  let cInto : Circle → (⟨{0}ᶜ, isOpen_compl_singleton⟩ : TopologicalSpace.Opens E) :=
    fun z ↦ ⟨c z, hc0 z⟩
  have hcInto : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ cInto := by
    rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
    exact hc
  obtain ⟨γ', hγ, hval⟩ := γ.exists_homotopic_normalize_of_norm_sub_lt_one
    (c ∘ TauCeti.unitToCircle) (hc.continuous.comp TauCeti.unitToCircle.continuous)
    (fun t ↦ by
      simpa only [Function.comp_apply, γ.toCircle_unitToCircle] using
        hclose (TauCeti.unitToCircle t))
    (by simpa only [Function.comp_apply, TauCeti.unitToCircle_zero] using hc1)
    (by simpa only [Function.comp_apply, TauCeti.unitToCircle_one] using hc1)
  refine ⟨γ', hγ, ((TauCeti.contMDiff_normalize_sphere (n := n) (m := ∞)).comp hcInto).congr ?_⟩
  intro z
  obtain ⟨t, rfl⟩ := TauCeti.unitToCircle_surjective z
  apply Subtype.ext
  rw [γ'.toCircle_unitToCircle]
  exact hval t
