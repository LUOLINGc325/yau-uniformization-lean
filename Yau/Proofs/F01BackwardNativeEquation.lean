import Yau.Proofs.F01BackwardNativeData
import Yau.Proofs.F01ShiftedNativeEquation
import Yau.Proofs.F01ShiftedPotentialSup

/-! The original real nonlinear equation and potential supremum hold
on a backward patch ending at the actual final time. No value after
that final time appears in either input. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem shifted_backward_native_real_equation
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T ρ τ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ ≤ T)
    (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s) (a : M.Carrier) :
    let V := shiftedNativePotential A U a ρ τ
    let Q := cylinder (ball 0 1) (-1) 0
    C2 Q V ∧ ∀ p ∈ Q,
      timeD Q V p - logDetReal (iota (shiftedComplexBackground A a ρ τ p) +
        complexHessianMap (hessian V p)) = normalizedPotentialLogSource A a ρ p.1 := by
  let V := shiftedNativePotential A U a ρ τ
  have hC2 : C2 (cylinder (ball 0 1) (-1) 0) V :=
    closed_slab_parabolic_C2 isOpen_ball (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0))
      (shifted_backward_native_potential_smooth A U hρ hρr hLower hUpper hU a)
  refine ⟨hC2, ?_⟩
  intro p hp
  have hSet : {s : ℝ | (p.1, s) ∈ cylinder (ball (0 : Space n) 1) (-1) 0} = Icc (-1) 0 := by
    ext s
    exact and_iff_right hp.1
  have hTime : timeD (cylinder (ball 0 1) (-1) 0) V p =
      flowLogDetRatio g h (A.chart a (affineParabolicPoint ρ 0 τ p).1)
        (affineParabolicPoint ρ 0 τ p).2 := by
    simpa only [timeD, hSet] using
      (shifted_backward_native_clock_jet A h U hρ.ne' hLower hUpper hpde a p.1 hp.2).derivWithin
        (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0) p.2 hp.2)
  have hPos := shifted_backward_native_matrix_pos hg A h U hρ hρr hLower hUpper hU hpot a hp
  rw [hTime, real_chart_potential_matrix hC2 hp, logDetReal_iota_posDef _ hPos,
    shifted_backward_native_log_identity hg A h U hρ hρr hLower hUpper hU hpot a hp]
  ring


theorem shifted_backward_native_potential_sup
    (g : HermitianField M) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T Tcap C ρ τ : ℝ}
    (hC : 1 ≤ C) (hLower : ρ ^ 2 ≤ τ) (hUpper : τ ≤ T) (hCap : T ≤ Tcap)
    (hU0 : ∀ x, U x 0 = 0)
    (hJet : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s)
    (hflow : ∀ x s, s ∈ Icc 0 T →
      (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) (a : M.Carrier) :
    ∀ p ∈ cylinder (ball 0 1) (-1) 0,
      |shiftedNativePotential A U a ρ τ p| ≤ (ρ ^ 2)⁻¹ * (((n : ℝ) * Real.log C) * Tcap) := by
  have hT : 0 ≤ T := by nlinarith [sq_nonneg ρ]
  have hA : 0 ≤ (n : ℝ) * Real.log C := mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hC)
  intro p hp
  have ht := shifted_backward_clock_maps hLower hUpper hp.2
  have hu := potential_sup_from_metric_sandwich g h U hT hC hU0 hJet hflow
    (A.chart a (affineParabolicPoint ρ 0 τ p).1) (affineParabolicPoint ρ 0 τ p).2 ht
  have hBound := hu.trans (mul_le_mul_of_nonneg_left (ht.2.trans hCap) hA)
  dsimp only [shiftedNativePotential, affineParabolicPotential, affineParabolicPullback]
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ρ))]
  exact mul_le_mul_of_nonneg_left hBound (inv_nonneg.mpr (sq_nonneg ρ))


end Yau.NodeProofs.F01Aux
