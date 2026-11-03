import Yau.Proofs.C05ScalarTraceWord
import Yau.LeafProofs.L23TensorNormLinear

/-! The same-order intrinsic scalar-jet bound is a direct contraction of
the original curvature jet, with no chart-family differentiability premise. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarJetNorm_le_curvatureJetNorm (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (m : ℕ) (x : M.Carrier) :
    scalarJetNorm k (scalarCurvature k) m x ≤ (n : ℝ) * curvatureJetNorm k m x := by
  let G := realMetricFn k x (chartPt x x)
  let A := rmJet k x m (chartPt x x)
  have hG : G.PosDef := Yau.LeafProofs.L12Aux.realMetricFn_posDef k x _ (mem_extChartAt_target x)
  have he : scalarJet k (scalarCurvature k) x m (chartPt x x) =
      fun v => (1 / 2 : ℝ) * (scalarTraceWord m).eval G⁻¹ A (fun _ => 1) v := by
    funext v
    exact scalarJet_eq_curvature_trace_word k hk hK x m (mem_extChartAt_target x) v
  have hb : Real.sqrt (covTensorNormSq G (fun _ : Fin 0 → RIdx n => (1 : ℝ))) = 1 := by
    simp [covTensorNormSq]
  have hw := (scalarTraceWord m).eval_norm_le G hG A (fun _ => 1)
  rw [hb, mul_one] at hw
  unfold scalarJetNorm
  rw [he, sqrt_covTensorNormSq_const_mul]
  calc
    |(1 / 2 : ℝ)| * Real.sqrt (covTensorNormSq G ((scalarTraceWord m).eval G⁻¹ A (fun _ => 1))) ≤
        (1 / 2 : ℝ) * ((2 * n : ℕ) * Real.sqrt (covTensorNormSq G A)) := by
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left hw (by norm_num)
    _ = (n : ℝ) * curvatureJetNorm k m x := by
      unfold curvatureJetNorm
      dsimp only [G, A]
      push_cast
      ring

end Yau.Proofs.C05Aux
