import Yau.Proofs.P02Poisson

noncomputable section
open Filter Metric Complex InnerProductSpace
open scoped Topology

namespace Yau.NodeProofs.P02Aux

theorem poissonKernel_far_bound (r η : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hη : 0 < η) (hgap : 1-r ≤ η/2) (z ξ : ℂ)
    (hz : ‖z‖ = 1) (hξ : ‖ξ‖ = 1) (hfar : η ≤ ‖ξ-z‖) :
    poissonKernel 0 ((r : ℂ)*z) ξ ≤ 4*(1-r^2)/η^2 := by
  have hnorm : ‖(r : ℂ)*z-z‖ = 1-r := by
    have heq : (r : ℂ)*z-z = ((r-1 : ℝ) : ℂ)*z := by push_cast; ring
    rw [heq,norm_mul,hz,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  have htri := norm_add_le (ξ-(r : ℂ)*z) ((r : ℂ)*z-z)
  rw [sub_add_sub_cancel] at htri
  rw [hnorm] at htri
  have hden : η/2 ≤ ‖ξ-(r : ℂ)*z‖ := by linarith
  have hnum : 0 ≤ 1-r^2 := by nlinarith
  rw [poissonKernel_unit_circle r z ξ hz hξ]
  calc
    _ ≤ (1-r^2)/(η/2)^2 := by
      apply div_le_div_of_nonneg_left hnum (sq_pos_of_pos (by positivity))
      nlinarith [norm_nonneg (ξ-(r : ℂ)*z)]
    _ = _ := by field_simp; ring

theorem poissonApprox_error (F : ℂ → ℝ) (hF : ContinuousOn F (sphere 0 1))
    (r η δ B : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hη : 0 < η)
    (hgap : 1-r ≤ η/2) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hbound : ∀ ξ ∈ sphere (0 : ℂ) 1, |F ξ| ≤ B)
    (hmod : ∀ z ∈ sphere (0 : ℂ) 1, ∀ ξ ∈ sphere (0 : ℂ) 1,
      ‖ξ-z‖ < η → |F ξ-F z| ≤ δ)
    (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1) :
    |poissonApprox F r z-F z| ≤ δ+8*B*(1-r^2)/η^2 := by
  have hzn : ‖z‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hz
  have hnorm : ‖(r : ℂ)*z‖ < 1 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0,hzn,mul_one]
    exact hr1
  have hoff : (r : ℂ)*z ∉ sphere 0 |(1 : ℝ)| := by
    simpa only [mem_sphere,dist_zero_right,abs_one] using ne_of_lt hnorm
  have hFc : ContinuousOn F (sphere 0 |(1 : ℝ)|) := by simpa only [abs_one] using hF
  have hFi : CircleIntegrable F 0 1 := hFc.circleIntegrable'
  let P := poissonKernel 0 ((r : ℂ)*z)
  have hPc : ContinuousOn P (sphere 0 |(1 : ℝ)|) := by
    rw [show P = Complex.re ∘ herglotzRieszKernel 0 ((r : ℂ)*z) from
      poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hoff)
  have hPi : CircleIntegrable P 0 1 := hPc.circleIntegrable'
  let T : ℂ → ℝ := fun ξ => P ξ*(F ξ-F z)
  have hTc : ContinuousOn T (sphere 0 |(1 : ℝ)|) := hPc.mul (hFc.sub continuousOn_const)
  have hTi : CircleIntegrable T 0 1 := hTc.circleIntegrable'
  have hTP : CircleIntegrable (fun ξ => δ*P ξ+8*B*(1-r^2)/η^2) 0 1 :=
    ((continuousOn_const.mul hPc).add continuousOn_const).circleIntegrable'
  have hpoint (ξ : ℂ) (hξ : ξ ∈ sphere 0 |(1 : ℝ)|) :
      |T ξ| ≤ δ*P ξ+8*B*(1-r^2)/η^2 := by
    have hξ' : ξ ∈ sphere (0 : ℂ) 1 := by simpa only [abs_one] using hξ
    have hξn : ‖ξ‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hξ'
    have hP0 : 0 ≤ P ξ := poissonKernel_unit_nonneg r hr0 hr1 z ξ hzn hξn
    have hnum : 0 ≤ 1-r^2 := by nlinarith
    dsimp only [T]
    rw [abs_mul,abs_of_nonneg hP0]
    by_cases hnear : ‖ξ-z‖ < η
    · have HH := mul_le_mul_of_nonneg_left (hmod z hz ξ hξ' hnear) hP0
      have Htail : 0 ≤ 8*B*(1-r^2)/η^2 := by positivity
      nlinarith
    · have Hkernel := poissonKernel_far_bound r η hr0 hr1 hη hgap z ξ hzn hξn
        (le_of_not_gt hnear)
      have HF : |F ξ-F z| ≤ 2*B := by
        have HH := abs_sub_le (F ξ) 0 (F z)
        simp only [sub_zero,zero_sub,abs_neg] at HH
        linarith [hbound ξ hξ',hbound z hz]
      have HH := mul_le_mul HF Hkernel hP0 (show 0 ≤ 2*B by positivity)
      change |F ξ-F z| * P ξ ≤ 2*B*(4*(1-r^2)/η^2) at HH
      have HδP : 0 ≤ δ*P ξ := mul_nonneg hδ hP0
      change P ξ * |F ξ-F z| ≤ _
      calc
        _ = |F ξ-F z| * P ξ := mul_comm _ _
        _ ≤ 2*B*(4*(1-r^2)/η^2) := HH
        _ = 8*B*(1-r^2)/η^2 := by ring
        _ ≤ _ := le_add_of_nonneg_left HδP
  have Havg := (Real.abs_circleAverage_le_circleAverage_abs (f := T) (c := 0) (R := 1)).trans
    (Real.circleAverage_mono (hTc.abs.circleIntegrable') hTP hpoint)
  have Hmass := poissonKernel_mass_one ((r : ℂ)*z) hnorm
  change Real.circleAverage P 0 1 = 1 at Hmass
  have HavgT : Real.circleAverage T 0 1 = poissonApprox F r z-F z := by
    have hfun : T = fun ξ => P ξ*F ξ-F z*P ξ := by funext ξ; dsimp [T]; ring
    have hPFi : CircleIntegrable (fun ξ => P ξ*F ξ) 0 1 := by
      simpa only [Pi.mul_def] using (hPc.mul hFc).circleIntegrable'
    have hFzPi : CircleIntegrable (fun ξ => F z*P ξ) 0 1 := by
      simpa only [Pi.mul_def] using
        ((continuousOn_const (c := F z)).mul hPc).circleIntegrable'
    rw [hfun,Real.circleAverage_fun_sub hPFi hFzPi]
    have hsmul : Real.circleAverage (fun ξ => F z*P ξ) 0 1 =
        F z*Real.circleAverage P 0 1 := by
      simpa only [smul_eq_mul] using
        (Real.circleAverage_fun_smul (a := F z) (f := P) (c := 0) (R := 1))
    rw [hsmul,Hmass,mul_one]
    rw [poissonApprox_eq F hFi r z (by simpa only [abs_one] using hoff)]
  have hδPi : CircleIntegrable (fun ξ => δ*P ξ) 0 1 := by
    simpa only [Pi.mul_def] using ((continuousOn_const (c := δ)).mul hPc).circleIntegrable'
  have hci : CircleIntegrable (fun _ : ℂ => 8*B*(1-r^2)/η^2) 0 1 :=
    continuousOn_const.circleIntegrable'
  rw [HavgT,Real.circleAverage_fun_add hδPi hci,Real.circleAverage_const] at Havg
  have hsmul : Real.circleAverage (fun ξ => δ*P ξ) 0 1 =
      δ*Real.circleAverage P 0 1 := by
    simpa only [smul_eq_mul] using
      (Real.circleAverage_fun_smul (a := δ) (f := P) (c := 0) (R := 1))
  rw [hsmul,Hmass,mul_one] at Havg
  exact Havg

theorem exists_harmonic_boundary_approx (F : ℂ → ℝ)
    (hF : ContinuousOn F (sphere 0 1)) (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H (closedBall 0 1) ∧
      H 0 = Real.circleAverage F 0 1 ∧
      ∀ z ∈ sphere (0 : ℂ) 1, |H z-F z| < ε := by
  obtain ⟨C,hC⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn hF
  let B := max 1 C
  have hB : 0 < B := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) (le_max_left _ _)
  have hbound : ∀ ξ ∈ sphere (0 : ℂ) 1, |F ξ| ≤ B := by
    intro ξ hξ
    have HH : |F ξ| ≤ C := by simpa only [Real.norm_eq_abs] using hC ξ hξ
    exact HH.trans (le_max_right _ _)
  have hUC := (isCompact_sphere (0 : ℂ) 1).uniformContinuousOn_of_continuous hF
  obtain ⟨η,hη,hmod⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε/2) (by positivity)
  let d := min (1/2 : ℝ) (min (η/4) (ε*η^2/(64*B)))
  have hd : 0 < d := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hdhalf : d ≤ (1/2 : ℝ) := min_le_left _ _
  have hdη : d ≤ η/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε*η^2/(64*B) := (min_le_right _ _).trans (min_le_right _ _)
  let r := 1-d
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hgap : 1-r ≤ η/2 := by dsimp [r]; linarith
  have hmod' : ∀ z ∈ sphere (0 : ℂ) 1, ∀ ξ ∈ sphere (0 : ℂ) 1,
      ‖ξ-z‖ < η → |F ξ-F z| ≤ ε/2 := by
    intro z hz ξ hξ hdist
    exact le_of_lt (by simpa only [Real.dist_eq] using
      (hmod ξ hξ z hz (by simpa only [dist_eq_norm] using hdist)))
  have htail : 8*B*(1-r^2)/η^2 ≤ ε/4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hη)).mpr
    have Hd := (le_div_iff₀ (show 0 < 64*B by positivity)).mp hdε
    have Hr : 1-r^2 ≤ 2*d := by dsimp [r]; nlinarith [sq_nonneg d]
    nlinarith [mul_le_mul_of_nonneg_left Hr (show 0 ≤ 8*B by positivity)]
  refine ⟨poissonApprox F r,poissonApprox_harmonic F hF r hr0 hr1,?_,?_⟩
  · exact poissonApprox_zero F (by apply ContinuousOn.circleIntegrable'; simpa only [abs_one] using hF) r
  · intro z hz
    have H := poissonApprox_error F hF r η (ε/2) B hr0 hr1 hη hgap
      (by positivity) hB.le hbound hmod' z hz
    linarith

end Yau.NodeProofs.P02Aux
