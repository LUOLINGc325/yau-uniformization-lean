import Yau.Proofs.F01ShiftedNativeClock
import Yau.Proofs.F01ShiftedRealBackground

/-! The positive-time native potential supplies the actual C2 and
real log-determinant equation required by Chu, including both closed
faces and the original realification of its transformed Hessian. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem shifted_native_matrix_pos
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ τ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ + ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (a : M.Carrier) {p : Point n} (hp : p ∈ cylinder (ball 0 1) (-1) 1) :
    (chartPotentialMatrix (shiftedComplexBackground A a ρ τ) (shiftedNativePotential A U a ρ τ) p).PosDef := by
  rw [shifted_native_flow_matrix hg A h U hρ hρr hLower hUpper hU hpot a hp]
  have hz := shifted_space_maps A hρ hρr hp.1
  exact pullbackMatrix_posDef _ (A.chart a) (A.differentiable a) (A.inverse_differentiable a)
    (A.closedBall_source a (ball_subset_closedBall hz))

theorem shifted_native_real_equation
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ τ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ + ρ ^ 2 ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s) (a : M.Carrier) :
    let V := shiftedNativePotential A U a ρ τ
    let Q := cylinder (ball 0 1) (-1) 1
    C2 Q V ∧ ∀ p ∈ Q,
      timeD Q V p - logDetReal (iota (shiftedComplexBackground A a ρ τ p) +
        complexHessianMap (hessian V p)) = normalizedPotentialLogSource A a ρ p.1 := by
  let V := shiftedNativePotential A U a ρ τ
  have hC2 : C2 (cylinder (ball 0 1) (-1) 1) V :=
    closed_slab_parabolic_C2 isOpen_ball (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1))
      (shifted_native_potential_smooth A U hρ hρr hLower hUpper hU a)
  refine ⟨hC2, ?_⟩
  intro p hp
  have hSet : {s : ℝ | (p.1, s) ∈ cylinder (ball (0 : Space n) 1) (-1) 1} = Icc (-1) 1 := by
    ext s
    exact and_iff_right hp.1
  have hTime : timeD (cylinder (ball 0 1) (-1) 1) V p =
      flowLogDetRatio g h (A.chart a (affineParabolicPoint ρ 0 τ p).1)
        (affineParabolicPoint ρ 0 τ p).2 := by
    simpa only [timeD, hSet] using
      (shifted_native_clock_jet A h U hρ.ne' hLower hUpper hpde a p.1 hp.2).derivWithin
        (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1) p.2 hp.2)
  have hPos := shifted_native_matrix_pos hg A h U hρ hρr hLower hUpper hU hpot a hp
  rw [hTime, real_chart_potential_matrix hC2 hp, logDetReal_iota_posDef _ hPos,
    shifted_native_log_identity hg A h U hρ hρr hLower hUpper hU hpot a hp]
  ring

end Yau.NodeProofs.F01Aux
