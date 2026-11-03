import Yau.LeafProofs.L05PerturbationFrozenCentralTransport

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_central_holder_mono {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] {eta B C : ℝ} {Q : Set (Point n)} {f : Point n → V}
    (hf : HolderBound eta Q f B) (hBC : B ≤ C) : HolderBound eta Q f C := by
  refine ⟨hf.1.trans hBC, fun p hp => (hf.2.1 p hp).trans hBC, ?_⟩
  intro p hp q hq
  exact (hf.2.2 p hp q hq).trans (mul_le_mul_of_nonneg_right hBC (by
    unfold holderWeight; positivity))

/-- A uniform numerical budget for the actual transported Schauder norm and Hessian. -/
theorem perturb_central_schauder_from_scaled {n : ℕ} {eta C : ℝ} (heta : eta < 1)
    (hC : 0 < C) {h : Point n → ℝ}
    (hv : SchauderBound eta (backward (1/2)) (fun p => h (perturbScale (1/2) p)) C) :
    let K := 16 * (1 + (Fintype.card (RIdx n) : ℝ)) * (1 + C)
    1 < K ∧ SchauderBound eta (backward (1/4)) h K ∧
      ∀ p ∈ backward (1/4), ‖hessian h p‖ ≤ K := by
  let d : ℝ := Fintype.card (RIdx n)
  let K : ℝ := 16 * (1 + d) * (1 + C)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hK : 1 < K := by dsimp [K]; nlinarith [mul_nonneg hd hC.le]
  have hK8 : 8 * C ≤ K := by dsimp [K]; nlinarith [mul_nonneg hd hC.le]
  have hKd : d * (4 * C) ≤ K := by dsimp [K]; nlinarith [mul_nonneg hd hC.le]
  have hj := perturb_central_actual_jets hv.1
  have hDD : HolderBound eta (backward (1/4)) (spatialDD h) (8 * C) :=
    perturb_central_holder_transport heta hv.2.2.2.1 (fun p hp => (hj.2 p hp).2.1)
  have hT : HolderBound eta (backward (1/4)) (timeD (backward (1/4)) h) (8 * C) :=
    perturb_central_holder_transport heta hv.2.2.2.2 (by
      intro p hp
      simpa only [smul_eq_mul] using (hj.2 p hp).2.2)
  refine ⟨hK, ⟨hj.1, by linarith, ?_, perturb_central_holder_mono hDD hK8,
    perturb_central_holder_mono hT hK8⟩, ?_⟩
  · intro p hp
    have hy := perturb_central_twice_back hp
    have hvp := hv.2.2.1 _ hy
    have hu : |h p| ≤ C := by simpa only [perturb_half_twice] using hvp.1
    have hD : ‖spatialD h p‖ ≤ 2 * C := by
      rw [(hj.2 p hp).1, norm_smul]
      norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left hvp.2 (by norm_num)
    exact ⟨hu.trans (by linarith), hD.trans (by linarith)⟩
  · intro p hp
    have hNorm : ‖spatialDD h p‖ ≤ 4 * C := by
      rw [(hj.2 p hp).2.1]
      exact perturb_central_four_norm_bound
        (hv.2.2.2.1.2.1 _ (perturb_central_twice_back hp))
    calc
      _ ≤ d * ‖spatialDD h p‖ := perturb_hessian_norm_le hj.1 hp
      _ ≤ d * (4 * C) := mul_le_mul_of_nonneg_left hNorm hd
      _ ≤ K := hKd

end Yau.LeafProofs.L05Aux
