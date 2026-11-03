import Yau.Proofs.V02FlowTimeDerivative
import Mathlib.Analysis.ODE.ExistUnique

/-! Radial real uniqueness for genuine complex-time solutions. -/

open scoped Topology NNReal
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02FlowProof

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem complex_ode_unique_on_ball {R : ℝ} {S : Set V} {L : ℝ≥0}
    {W : V → V} {u v : ℂ → V}
    (hLip : LipschitzOnWith L W S)
    (hu : ∀ z ∈ ball (0 : ℂ) R, HasDerivAt u (W (u z)) z)
    (hv : ∀ z ∈ ball (0 : ℂ) R, HasDerivAt v (W (v z)) z)
    (huS : ∀ z ∈ ball (0 : ℂ) R, u z ∈ S)
    (hvS : ∀ z ∈ ball (0 : ℂ) R, v z ∈ S)
    (hzero : u 0 = v 0) : EqOn u v (ball (0 : ℂ) R) := by
  intro t ht
  have hrad : ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) * t ∈ ball (0 : ℂ) R := by
    intro s hs
    rw [mem_ball, dist_zero_right]
    exact (norm_radial_time_le hs t).trans_lt (by simpa using ht)
  have hscaled : LipschitzOnWith (‖t‖₊ * L) (fun x => t • W x) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, ← smul_sub, norm_smul, NNReal.coe_mul, coe_nnnorm, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [dist_eq_norm] using (hLip.dist_le_mul x hx y hy)) (norm_nonneg t)
  have hU : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => u ((r : ℂ) * t)) (t • W (u ((s : ℂ) * t))) s :=
    fun s hs => HasDerivAt.radial_real (hu _ (hrad s hs))
  have hV : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => v ((r : ℂ) * t)) (t • W (v ((s : ℂ) * t))) s :=
    fun s hs => HasDerivAt.radial_real (hv _ (hrad s hs))
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ x => t • W x) (s := fun _ => S) (a := (0 : ℝ)) (b := 1)
    (fun _ _ => hscaled)
    (fun s hs => (hU s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hU s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s hs => huS _ (hrad s (Ico_subset_Icc_self hs)))
    (fun s hs => (hV s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hV s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s hs => hvS _ (hrad s (Ico_subset_Icc_self hs)))
    (by simpa using hzero)
  simpa using heq (show (1 : ℝ) ∈ Icc 0 1 by simp)

end Yau.Blueprint.V02FlowProof
