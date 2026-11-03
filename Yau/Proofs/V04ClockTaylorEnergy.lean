import Yau.Proofs.V03DirichletScaling
import Yau.Proofs.V03ScalarAreaFourier
import Yau.Proofs.V03EnergyTraceBounds
import Yau.Proofs.V04BackwardClockRealization

/-! The logarithmically parametrized original backward clock has the
exact quadratic Dirichlet energy. All real conversions occur at finite energies. -/
open scoped Topology ContDiff lp
noncomputable section
namespace Yau.Blueprint.V04Proof.ClockTaylorAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

def logBackwardClock (F : VariationDisc X) (Γ : ℂ → ℂ) (u : ℝ) : VariationDisc X :=
  backwardClock F Γ (F.s * Real.exp u)

theorem logBackwardClock_w (F : VariationDisc X) (Γ : ℂ → ℂ) (hs : 0 < F.s) (u : ℝ) :
    (logBackwardClock F Γ u).w = fun ζ => F.w ζ + ((u / 2 : ℝ) : ℂ) * Γ ζ := by
  have he : F.s * Real.exp u / F.s = Real.exp u := by field_simp
  funext ζ
  simp only [logBackwardClock, backwardClock, he, Real.log_exp]
  push_cast
  ring

theorem logBackwardClock_boundary_time {d : VariationData X q} {k : ClockData X} {j a : ℕ}
    {F : VariationDisc X} {Γ : ℂ → ℂ} (hΓ : ClockLift d k j a F Γ)
    (hs : 0 < F.s) (u θ : ℝ) :
    discTime (logBackwardClock F Γ u) (circlePoint θ) =
      discTime F (circlePoint θ) * Real.exp (u * clockWeight d k j a F θ) := by
  have he : Real.log (F.s * Real.exp u / F.s) = u := by
    rw [show F.s * Real.exp u / F.s = Real.exp u from by field_simp, Real.log_exp]
  rw [logBackwardClock, backwardClock_discTime_factor F Γ hs (mul_pos hs (Real.exp_pos u)),
    he, hΓ.2.2 θ]
  congr 2
  ring

theorem logBackwardClock_zero (F : VariationDisc X) (Γ : ℂ → ℂ) (hs : 0 < F.s) :
    logBackwardClock F Γ 0 = F := by
  simp [logBackwardClock, backwardClock, hs.ne']

theorem closedDisc_boundaryDSq_ne_top {g : ℂ → ℂ}
    (hg : ContDiffOn ℂ ∞ g (Metric.closedBall (0 : ℂ) 1)) :
    boundaryDSq (fun θ (_ : Unit) => g (circlePoint θ)) ≠ ⊤ := by
  rw [boundaryDSq_scalar_eq_inverse_area hg]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (normDiscArea_ne_top_of_closedDisc hg)

theorem dirichletVector_real_mul {u : ℝ → ℂ} (c : ℝ)
    (hu : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hc : boundaryDSq (fun θ (_ : Unit) => (c : ℂ) * u θ) ≠ ⊤) :
    dirichletVector (fun θ => (c : ℂ) * u θ) hc = (c : ℂ) • dirichletVector u hu := by
  apply Subtype.ext
  funext k
  change dirichletCoeff (fun θ => (c : ℂ) * u θ) k = (c : ℂ) • dirichletCoeff u k
  rw [dirichletCoeff, circleFourier_const_mul, dirichletCoeff,
    smul_eq_mul]
  ring

theorem boundaryDSq_real_affine_quadratic {w v : ℝ → ℂ}
    (hw : Continuous w) (hv : Continuous v)
    (hwf : boundaryDSq (fun θ (_ : Unit) => w θ) ≠ ⊤)
    (hvf : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤) (c : ℝ) :
    (boundaryDSq (fun θ (_ : Unit) => w θ + (c : ℂ) * v θ)).toReal =
      (boundaryDSq (fun θ (_ : Unit) => w θ)).toReal +
      2 * c * (dirichletPair w v).re + c ^ 2 * (boundaryDSq (fun θ (_ : Unit) => v θ)).toReal := by
  have hcf : boundaryDSq (fun θ (_ : Unit) => (c : ℂ) * v θ) ≠ ⊤ := by
    rw [boundaryDSq_const_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvf
  have hcv : Continuous (fun θ => (c : ℂ) * v θ) := continuous_const.mul hv
  have hsum : boundaryDSq (fun θ (_ : Unit) => w θ + (c : ℂ) * v θ) ≠ ⊤ := by
    simpa only [Pi.mul_def] using boundaryDSq_add_ne_top hw hcv hwf hcf
  have hp : (inner ℂ (dirichletVector w hwf) (dirichletVector v hvf)).re = (dirichletPair w v).re := by
    rw [dirichletPair_eq_inner w v hwf hvf]
    simpa only [RCLike.re_eq_complex_re] using inner_re_symm (𝕜 := ℂ)
      (dirichletVector w hwf) (dirichletVector v hvf)
  rw [← dirichletVector_norm_sq _ hsum,
    dirichletVector_add hw hcv hwf hcf hsum,
    dirichletVector_real_mul c hvf hcf, norm_add_sq (𝕜 := ℂ), inner_smul_right]
  simp only [RCLike.re_eq_complex_re, Complex.re_ofReal_mul, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, hp, dirichletVector_norm_sq]
  ring

def clockEnergyLinear (F : VariationDisc X) (Γ : ℂ → ℂ) : ℝ :=
  (2 * Real.pi) * (dirichletPair (fun θ => F.w (circlePoint θ)) (fun θ => Γ (circlePoint θ))).re

theorem logBackwardClock_clockArea (F : VariationDisc X) (Γ : ℂ → ℂ)
    (hs : 0 < F.s) (hw : ContDiffOn ℂ ∞ F.w (Metric.closedBall (0 : ℂ) 1))
    (hΓ : ContDiffOn ℂ ∞ Γ (Metric.closedBall (0 : ℂ) 1)) (u : ℝ) :
    (clockArea (logBackwardClock F Γ u)).toReal = (clockArea F).toReal +
      u * clockEnergyLinear F Γ + (Real.pi / 2) * u ^ 2 *
        (boundaryDSq (fun θ (_ : Unit) => Γ (circlePoint θ))).toReal := by
  have hwnew : ContDiffOn ℂ ∞ (logBackwardClock F Γ u).w (Metric.closedBall (0 : ℂ) 1) := by
    rw [logBackwardClock_w F Γ hs]
    exact hw.add (contDiffOn_const.mul hΓ)
  have harea (F : VariationDisc X) (hF : ContDiffOn ℂ ∞ F.w (Metric.closedBall (0 : ℂ) 1)) :
      (clockArea F).toReal = (2 * Real.pi) *
        (boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ))).toReal := by
    rw [clockArea_eq_normDiscArea, normDiscArea_scalar_eq_boundaryDSq hF,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [harea _ hwnew, harea _ hw, logBackwardClock_w F Γ hs]
  rw [boundaryDSq_real_affine_quadratic
    (closedDisc_scalar_trace_contDiff hw).continuous (closedDisc_scalar_trace_contDiff hΓ).continuous
    (closedDisc_boundaryDSq_ne_top hw) (closedDisc_boundaryDSq_ne_top hΓ)]
  unfold clockEnergyLinear
  ring

theorem logBackwardClock_energy_difference {d : VariationData X q} {j : ℕ}
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) {Γ : ℂ → ℂ}
    (hΓ : ContDiffOn ℂ ∞ Γ (Metric.closedBall (0 : ℂ) 1)) (u : ℝ) :
    (variationEnergy d j (logBackwardClock F Γ u)).toReal - (variationEnergy d j F).toReal =
      u * clockEnergyLinear F Γ + (Real.pi / 2) * u ^ 2 *
        (boundaryDSq (fun θ (_ : Unit) => Γ (circlePoint θ))).toReal := by
  have hnew : ContDiffOn ℂ ∞ (logBackwardClock F Γ u).w (Metric.closedBall (0 : ℂ) 1) := by
    rw [logBackwardClock_w F Γ hF.2.2.2.1]
    exact hF.2.1.add (contDiffOn_const.mul hΓ)
  have hfinite : variationEnergy d j (logBackwardClock F Γ u) ≠ ⊤ :=
    backwardClock_energy_ne_top hF.2.2.2.2.2.2.2.2 hnew
  rw [variationEnergy_toReal_split hfinite, variationEnergy_toReal_split hF.2.2.2.2.2.2.2.2,
    logBackwardClock_clockArea F Γ hF.2.2.2.1 hF.2.1 hΓ u]
  simp only [logBackwardClock, backwardClock]
  ring

theorem clockEnergyLinear_bound {d : VariationData X q} {j : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) {Γ : ℂ → ℂ}
    (hΓ : ContDiffOn ℂ ∞ Γ (Metric.closedBall (0 : ℂ) 1)) {C : ℝ} (hC : 0 ≤ C)
    (hΓbound : boundaryDSq (fun θ (_ : Unit) => Γ (circlePoint θ)) ≤
      ENNReal.ofReal C * variationEnergy d j F) :
    |clockEnergyLinear F Γ| ≤ (1 / 2 + Real.pi * C) * (variationEnergy d j F).toReal := by
  let D := (boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ))).toReal
  let H := (boundaryDSq (fun θ (_ : Unit) => Γ (circlePoint θ))).toReal
  let e := (variationEnergy d j F).toReal
  have hΓR : H ≤ C * e := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF.2.2.2.2.2.2.2.2) hΓbound
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using hh
  have hD : D ≤ (2 * Real.pi)⁻¹ * e := by
    rw [show D = (ENNReal.ofReal ((2 * Real.pi)⁻¹) * clockArea F).toReal from by
      dsimp only [D]
      rw [boundaryDSq_scalar_eq_inverse_area hF.2.1]
      rfl,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)]
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hF.2.2.2.2.2.2.2.2 (clockArea_le_variationEnergy d j F)) (by positivity)
  have hp := (Complex.abs_re_le_norm (dirichletPair (fun θ => F.w (circlePoint θ))
    (fun θ => Γ (circlePoint θ)))).trans
    (dirichletPair_norm_le _ _ (closedDisc_boundaryDSq_ne_top hF.2.1) (closedDisc_boundaryDSq_ne_top hΓ))
  have hpair : 2 * |(dirichletPair (fun θ => F.w (circlePoint θ)) (fun θ => Γ (circlePoint θ))).re| ≤ D + H := by
    have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
    have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
    have hDs := Real.sq_sqrt hD0
    have hHs := Real.sq_sqrt hH0
    nlinarith [sq_nonneg (Real.sqrt D - Real.sqrt H)]
  have hπ : Real.pi * (2 * Real.pi)⁻¹ = 1 / 2 := by field_simp
  unfold clockEnergyLinear
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  change 2 * Real.pi * |(dirichletPair (fun θ => F.w (circlePoint θ))
    (fun θ => Γ (circlePoint θ))).re| ≤ (1 / 2 + Real.pi * C) * e
  have hπD := mul_le_mul_of_nonneg_left hD Real.pi_pos.le
  rw [← mul_assoc, hπ] at hπD
  have hπH := mul_le_mul_of_nonneg_left hΓR Real.pi_pos.le
  have hπpair := mul_le_mul_of_nonneg_left hpair Real.pi_pos.le
  nlinarith

end Yau.Blueprint.V04Proof.ClockTaylorAux
