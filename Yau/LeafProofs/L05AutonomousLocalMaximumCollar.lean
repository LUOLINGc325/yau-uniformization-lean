import Yau.LeafProofs.L05AutonomousLocalMaximumCenter
import Yau.LeafProofs.L05AutonomousHarnackOscillation

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The local maximum estimate on arbitrary fixed nested closed cylinders, including terminal time. -/
theorem auto_local_maximum_collar (n : ℕ) (hn : 0< n) (ell L : ℝ) (hell : 0< ell) (hL : ell≤ L)
    (p : ℝ) (hp : 0< p) {r R : ℝ} (hr : 0< r) (hrR : r< R) :
    ∃ C : ℝ, 0< C ∧ ∀ w : Point n → ℝ, ContinuousOn w (autoClosed 0 R 0) →
      viscositySub (autoOpen 0 R 0) (fun H _ => pucciPlus ell L H) (fun _ => 0) w →
      ∀ z∈autoClosed (0 : Space n) r 0,
        max (w z) 0≤ C*(∫ q in autoOpen (0 : Space n) R 0, (max (w q) 0)^p)^(1/p) := by
  obtain ⟨C₀,hC₀,hMax⟩ := auto_local_maximum_center n hn ell L hell hL p hp
  let rho := (R-r)/2
  have hRho : 0< rho := half_pos (sub_pos.mpr hrR)
  have hMargin : r+rho< R := by dsimp only [rho];linarith only [hrR]
  have hTime : r^2+rho^2< R^2 := by
    dsimp only [rho]
    nlinarith only [hr,hrR,mul_pos hr (sub_pos.mpr hrR),sq_pos_of_pos (sub_pos.mpr hrR)]
  let jac := rho^(2*n+2)
  have hJac : 0< jac := pow_pos hRho _
  let C := C₀*(jac⁻¹)^(1/p)
  have hC : 0< C := mul_pos hC₀ (Real.rpow_pos_of_pos (inv_pos.mpr hJac) _)
  refine ⟨C,hC,?_⟩
  intro w hw hsub z hz
  have hLocal (q : Point n) (hq : q∈autoClosed z.1 rho z.2) :
      ‖q.1‖< R ∧ -R^2< q.2 ∧ q.2≤ 0 := by
    have hzNorm : ‖z.1‖≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
    have hqNorm : ‖q.1-z.1‖≤ rho := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hq.1
    have htri := norm_add_le (q.1-z.1) z.1
    rw [sub_add_cancel] at htri
    have hzTime : -r^2≤ z.2 ∧ z.2≤ 0 := by simpa only [zero_sub,mem_Icc] using hz.2
    have hqTime : z.2-rho^2≤ q.2 ∧ q.2≤ z.2 := hq.2
    exact ⟨by linarith only [htri,hzNorm,hqNorm,hMargin],
      by linarith only [hzTime.1,hqTime.1,hTime],hqTime.2.trans hzTime.2⟩
  have hClosed : autoClosed z.1 rho z.2⊆autoClosed (0 : Space n) R 0 := by
    intro q hq
    obtain ⟨hspace,ht0,ht1⟩ := hLocal q hq
    exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hspace.le,
      by simpa only [zero_sub,mem_Icc] using And.intro ht0.le ht1⟩
  have hOpen : autoOpen z.1 rho z.2⊆autoOpen (0 : Space n) R 0 := by
    intro q hq
    have hqc : q∈autoClosed z.1 rho z.2 := ⟨Metric.ball_subset_closedBall hq.1,Ioo_subset_Icc_self hq.2⟩
    obtain ⟨hspace,ht0,ht1⟩ := hLocal q hqc
    have hqt : q.2< 0 := hq.2.2.trans_le (by simpa only [zero_sub,mem_Icc] using hz.2.2)
    exact ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hspace,
      by simpa only [zero_sub,mem_Ioo] using And.intro ht0 hqt⟩
  have hStep := hMax z.1 rho z.2 hRho w (hw.mono hClosed) (viscositySub_mono_domain hsub hOpen)
  have hPhi : ContinuousOn (fun q => (max (w q) 0)^p) (autoClosed (0 : Space n) R 0) :=
    (Real.continuous_rpow_const hp.le).comp_continuousOn (hw.sup continuousOn_const)
  have hInt : IntegrableOn (fun q => (max (w q) 0)^p) (autoOpen (0 : Space n) R 0) :=
    (hPhi.integrableOn_compact (autoClosed_isCompact _ _ _)).mono_set
      (fun q hq => ⟨Metric.ball_subset_closedBall hq.1,Ioo_subset_Icc_self hq.2⟩)
  have hMono : (∫ q in autoOpen z.1 rho z.2, (max (w q) 0)^p)≤
      ∫ q in autoOpen (0 : Space n) R 0, (max (w q) 0)^p :=
    setIntegral_mono_set hInt (ae_of_all _ fun q => Real.rpow_nonneg (le_max_right _ _) _)
      (ae_of_all volume fun q hq => hOpen hq)
  have hPow := Real.rpow_le_rpow (div_nonneg (integral_nonneg fun q => Real.rpow_nonneg (le_max_right _ _) _) hJac.le)
    (div_le_div_of_nonneg_right hMono hJac.le) (one_div_pos.mpr hp).le
  have hBound := hStep.trans (mul_le_mul_of_nonneg_left hPow hC₀.le)
  have hTotal0 : 0≤ ∫ q in autoOpen (0 : Space n) R 0, (max (w q) 0)^p :=
    integral_nonneg fun q => Real.rpow_nonneg (le_max_right _ _) _
  have hFactor : C₀*((∫ q in autoOpen (0 : Space n) R 0, (max (w q) 0)^p)/jac)^(1/p)=
      C*(∫ q in autoOpen (0 : Space n) R 0, (max (w q) 0)^p)^(1/p) := by
    rw [div_eq_mul_inv,Real.mul_rpow hTotal0 (inv_nonneg.mpr hJac.le)]
    dsimp only [C]
    ring
  simpa only [Prod.eta,hFactor] using hBound

end Yau.LeafProofs.L05AutonomousAux
