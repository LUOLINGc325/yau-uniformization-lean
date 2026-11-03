import Yau.Proofs.P07SupportWeakFourier
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Elementary lower-test comparison and the actual scalar circle supermean. -/
noncomputable section
open Filter Set Metric InnerProductSpace Laplacian
open scoped Topology ContDiff
namespace Yau.NodeProofs.P07Aux.SupportWeak

/-- The ordinary real two-dimensional Laplacian, without a factor of four. -/
def complexLap (q : ℂ → ℝ) (z : ℂ) : ℝ := Laplacian.laplacian q z

theorem complexLap_eq_hessian (q : ℂ → ℝ) (z : ℂ) :
    complexLap q z = fderiv ℝ (fderiv ℝ q) z 1 1 +
      fderiv ℝ (fderiv ℝ q) z Complex.I Complex.I := by
  simp [complexLap, laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply]

theorem complexLap_norm_sq (z : ℂ) : complexLap (fun ζ : ℂ => ‖ζ‖ ^ 2) z = 4 := by
  rw [complexLap_eq_hessian]
  rw [fderiv_norm_sq]
  simp only [two_smul]
  rw [fderiv_add (innerSL ℝ (E := ℂ)).differentiableAt
    (innerSL ℝ (E := ℂ)).differentiableAt, (innerSL ℝ (E := ℂ)).fderiv]
  change inner ℝ (1 : ℂ) 1 + inner ℝ (1 : ℂ) 1 +
    (inner ℝ Complex.I Complex.I + inner ℝ Complex.I Complex.I) = 4
  norm_num [real_inner_self_eq_norm_sq]

theorem complexLap_add {f g : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    complexLap (fun ζ => f ζ + g ζ) z = complexLap f z + complexLap g z :=
  hf.laplacian_add hg

theorem complexLap_sub {f g : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    complexLap (fun ζ => f ζ - g ζ) z = complexLap f z - complexLap g z :=
  hf.laplacian_sub hg

theorem complexLap_const (c : ℝ) (z : ℂ) : complexLap (fun _ => c) z = 0 := by
  simp [complexLap]

theorem complexLap_const_mul {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (c : ℝ) :
    complexLap (fun ζ => c * f ζ) z = c * complexLap f z :=
  laplacian_smul c hf

def ScalarLowerTestUpperOn (O : Set ℂ) (k : ℂ → ℝ) (b : ℝ) : Prop :=
  ∀ z ∈ O, ∀ q : ℂ → ℝ, ContDiffAt ℝ 2 q z → q z = k z →
    (∀ᶠ ζ in 𝓝 z, q ζ ≤ k ζ) → complexLap q z ≤ b

/-- A strict smooth subsolution below the boundary remains below throughout the disc. -/
theorem le_of_boundary_and_strictLap
    {k B : ℂ → ℝ} (hk : ContinuousOn k (closedBall 0 1))
    (hB : ContDiff ℝ 2 B)
    (htest : ScalarLowerTestUpperOn (ball 0 1) k 0)
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → B z ≤ k z)
    (hstrict : ∀ z ∈ ball (0 : ℂ) 1, 0 < complexLap B z) :
    ∀ z ∈ closedBall (0 : ℂ) 1, B z ≤ k z := by
  by_contra h
  push_neg at h
  obtain ⟨z, hz, hzk⟩ := h
  obtain ⟨w, hw, hmin⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMinOn
    ⟨z, hz⟩ (hk.sub hB.continuous.continuousOn)
  have hwneg : k w - B w < 0 := lt_of_le_of_lt (hmin hz) (sub_neg.mpr hzk)
  have hwball : w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right]
    have hle : ‖w‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hw
    apply lt_of_le_of_ne hle
    intro heq
    exact (not_le_of_gt hwneg) (sub_nonneg.mpr (hboundary w heq))
  let q : ℂ → ℝ := fun ζ => B ζ + (k w - B w)
  have hq : ContDiffAt ℝ 2 q w := hB.contDiffAt.add contDiffAt_const
  have hqtest : ∀ᶠ ζ in 𝓝 w, q ζ ≤ k ζ := by
    filter_upwards [isOpen_ball.mem_nhds hwball] with ζ hζ
    have hm := hmin (ball_subset_closedBall hζ)
    change k w - B w ≤ k ζ - B ζ at hm
    dsimp [q]
    linarith
  have ht := htest w hwball q hq (by dsimp [q]; ring) hqtest
  have hLap : complexLap q w = complexLap B w := by
    simpa only [complexLap, Pi.add_def, laplacian_const, Pi.zero_apply, add_zero] using
      hB.contDiffAt.laplacian_add (contDiffAt_const (c := k w - B w))
  rw [hLap] at ht
  exact (not_le_of_gt (hstrict w hwball)) ht

/-- Finite harmonic boundary approximation plus the strict quadratic barrier gives supermean. -/
theorem circleSupermean_of_lowerTests
    {k : ℂ → ℝ} (hk : ContinuousOn k (closedBall (0 : ℂ) 1))
    (htest : ScalarLowerTestUpperOn (ball 0 1) k 0) :
    Real.circleAverage k 0 1 ≤ k 0 := by
  have happrox : ∀ ε : ℝ, 0 < ε → Real.circleAverage k 0 1 ≤ k 0 + 3 * ε := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_re_polynomial_boundary_approx hk hε
    let H : ℂ → ℝ := fun z => (p.eval z).re
    have hHhar := harmonicOnNhd_re_polynomial p
    have hHs : ContDiff ℝ 2 H :=
      contDiff_iff_contDiffAt.mpr (fun z => (hHhar z (mem_univ z)).1)
    let B : ℂ → ℝ := fun z => H z + ε * ‖z‖ ^ 2 - 2 * ε
    have hBs : ContDiff ℝ 2 B :=
      (hHs.add (contDiff_const.mul (contDiff_norm_sq ℝ))).sub contDiff_const
    have hbound : ∀ z ∈ closedBall (0 : ℂ) 1, B z ≤ k z := by
      apply le_of_boundary_and_strictLap hk hBs htest
      · intro z hz
        have hpz := (abs_lt.mp (hp z hz)).2
        dsimp [B, H]
        rw [hz]
        nlinarith
      · intro z hz
        have hH0 : complexLap H z = 0 := (hHhar z (mem_univ z)).2.self_of_nhds
        have hεs : ContDiffAt ℝ 2 (fun ζ : ℂ => ε * ‖ζ‖ ^ 2) z :=
          contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt
        have hLap : complexLap B z = 4 * ε := by
          dsimp only [B]
          rw [complexLap_sub (hHs.contDiffAt.add hεs) contDiffAt_const,
            complexLap_add hHs.contDiffAt hεs, complexLap_const,
            complexLap_const_mul (contDiff_norm_sq ℝ).contDiffAt,
            complexLap_norm_sq, hH0]
          ring
        rw [hLap]
        positivity
    have hcenter : H 0 - 2 * ε ≤ k 0 := by
      simpa only [B, norm_zero, zero_pow two_ne_zero, mul_zero, add_zero] using
        hbound 0 (by simp)
    have hkint : CircleIntegrable k 0 1 :=
      (hk.mono (by simpa only [abs_one] using (sphere_subset_closedBall : sphere (0 : ℂ) 1 ⊆ closedBall 0 1))).circleIntegrable'
    have hHint : CircleIntegrable H 0 1 := hHs.continuous.continuousOn.circleIntegrable'
    have hm : Real.circleAverage k 0 1 ≤ Real.circleAverage (fun z => H z + ε) 0 1 := by
      apply Real.circleAverage_mono hkint (hHs.continuous.add continuous_const |>.continuousOn.circleIntegrable')
      intro z hz
      have hz' : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right, abs_one] using hz
      have hpz := (abs_lt.mp (hp z hz')).1
      dsimp [H]
      linarith
    have hmean : Real.circleAverage H 0 1 = H 0 :=
      (hHhar.mono (subset_univ _)).circleAverage_eq
    have hadd : Real.circleAverage (fun z => H z + ε) 0 1 = Real.circleAverage H 0 1 + ε := by
      simpa only [Pi.add_def, Real.circleAverage_const] using
        Real.circleAverage_add hHint (circleIntegrable_const ε 0 1)
    rw [hadd, hmean] at hm
    linarith
  by_contra h
  have hgap : 0 < Real.circleAverage k 0 1 - k 0 := sub_pos.mpr (lt_of_not_ge h)
  have hh := happrox ((Real.circleAverage k 0 1 - k 0) / 4) (by positivity)
  linarith

end Yau.NodeProofs.P07Aux.SupportWeak
