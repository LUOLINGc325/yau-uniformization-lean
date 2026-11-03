import Yau.LeafProofs.L05AutonomousBallMeanCutoffDecomposition
import Yau.LeafProofs.L05AutonomousBallMeanOuter
import Yau.LeafProofs.L05AutonomousBallMeanApproximation

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_ballMean_laplacian_zero_outside {n : ℕ} {g : Space n → ℝ} {x : Space n}
    (hx : x∉tsupport g) : autoBallMeanLaplacian g x=0 := by
  have hxD : x∉tsupport (fderiv ℝ g) := fun h => hx (tsupport_fderiv_subset ℝ h)
  have hDD := fderiv_of_notMem_tsupport ℝ hxD
  simp only [autoBallMeanLaplacian,hDD,ContinuousLinearMap.zero_apply,Finset.sum_const_zero]

theorem auto_ballMean_radial_test_tsupport_both {n : ℕ} {phi : ℝ → ℝ} {a R : ℝ}
    (hs : tsupport phi ⊆ Icc a R) :
    tsupport (fun x : Space n => phi ‖x‖) ⊆ {x : Space n | ‖x‖∈Icc a R} := by
  apply closure_minimal ?_ (isClosed_Icc.preimage continuous_norm)
  intro x hx
  exact hs (subset_closure hx)

theorem auto_ballMean_test_laplacian_decomposition {n : ℕ} (hn : 0 < n) {omega r eta : ℝ}
    (hOmega : 0 < omega) (hr : 0 < r) (heta : 0 < eta) (hetar : eta < r/8)
    (v : Space n → ℝ) (x : Space n) :
    v x*autoBallMeanLaplacian (fun y : Space n => autoGreenTest (2*n) omega r eta ‖y‖) x=
      v x*autoGreenCutoffProduct r eta ‖x‖/(omega*r^(2*n))+
      autoBallMeanInnerError omega r eta v (deriv (autoGreenInner eta)) (deriv (deriv (autoGreenInner eta))) x+
      autoBallMeanOuterError omega r eta v (deriv (autoGreenOuter r eta)) (deriv (deriv (autoGreenOuter r eta))) x := by
  by_cases hs : ‖x‖∈Ioo 0 r
  · have hx : x≠0 := norm_pos_iff.mp hs.1
    have hPhi : ContDiff ℝ ∞ (autoGreenTest (2*n) omega r eta) :=
      auto_green_test_contDiff (by omega : 2 ≤ 2*n) omega hr heta
    have hD (s : ℝ) (_hs : 0 < s) : HasDerivAt (autoGreenTest (2*n) omega r eta)
        (deriv (autoGreenTest (2*n) omega r eta) s) s :=
      (contDiff_infty_iff_deriv.mp hPhi).1.differentiableAt.hasDerivAt
    have hDD (s : ℝ) (_hs : 0 < s) : HasDerivAt (deriv (autoGreenTest (2*n) omega r eta))
        (deriv (deriv (autoGreenTest (2*n) omega r eta)) s) s :=
      (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hPhi).2).1.differentiableAt.hasDerivAt
    have hRad := auto_ballMean_radial_laplacian hD hDD
      (fun s _ => (hPhi.of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞)).contDiffAt) hx
    have hLap := auto_green_test_scalar_laplacian (by omega : 0 < 2*n) hOmega hr heta hs
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hLap
    rw [hRad,hLap,auto_green_error_decomposition (2*n) omega heta hetar hs.1]
    dsimp only [autoBallMeanInnerError,autoBallMeanOuterError]
    split_ifs <;> ring
  · have hNot : ‖x‖∉Icc eta (r-eta) := by
      intro h
      exact hs ⟨heta.trans_le h.1,by linarith [h.2]⟩
    have hNotG : x∉tsupport (fun y : Space n => autoGreenTest (2*n) omega r eta ‖y‖) := by
      intro h
      exact hNot (auto_ballMean_radial_test_tsupport_both (auto_green_test_tsupport omega r heta) h)
    have hNotI : ‖x‖∉Icc eta (2*eta) := by
      intro h
      exact hNot ⟨h.1,by linarith [h.2]⟩
    have hNotO : ‖x‖∉Icc (r-2*eta) (r-eta) := by
      intro h
      exact hNot ⟨by linarith [h.1],h.2⟩
    have hQ : autoGreenCutoffProduct r eta ‖x‖=0 := by
      by_cases hxr : ‖x‖ < r
      · have hx0 : ‖x‖=0 := le_antisymm (le_of_not_gt (fun h => hs ⟨h,hxr⟩)) (norm_nonneg x)
        have hI : autoGreenInner eta 0=0 := auto_green_inner_zero heta (by simpa only [abs_zero] using heta.le)
        simp only [autoGreenCutoffProduct,hx0,hI,zero_mul]
      · simp only [autoGreenCutoffProduct,autoGreenOuter,ite_eq_right hxr,mul_zero]
    simp only [auto_ballMean_laplacian_zero_outside hNotG,hQ,autoBallMeanInnerError,
      autoBallMeanOuterError,ite_eq_right hNotI,ite_eq_right hNotO,mul_zero,zero_div,add_zero]

end Yau.LeafProofs.L05AutonomousAux
