import Yau.Proofs.Y03FlowLevi
import Yau.Proofs.Y03StripBound

/-! The geometric strip comparison in a fixed actual metric frame. -/

open scoped Topology ContDiff Matrix
open Set

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X} {h : Flow X} {U P₀ ρ : STF X}

theorem logarithmic_gMat_inverse_contDiff (hflow : FlowStage X o h U P₀ ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (i j : Fin n) :
    ContDiff ℝ ∞ (fun τ => (gMat (h (t * Real.exp τ)) x)⁻¹ i j) := by
  apply contDiff_iff_contDiffAt.2
  intro τ
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hnhds : chartTarget x ×ˢ Ici 0 ∈ 𝓝 (chartPt x x, t * Real.exp τ) :=
    prod_mem_nhds ((isOpen_extChartAt_target x).mem_nhds hx)
      (Ici_mem_nhds (mul_pos ht (Real.exp_pos τ)))
  exact ((metricFamily_hMat_inv_contDiffOn hflow.1.1.2.1 x i j).contDiffAt hnhds).comp
    (f := fun s : ℝ => (chartPt x x, t * Real.exp s)) τ (by fun_prop)

theorem fixed_frame_inverse_continuousOn (hflow : FlowStage X o h U P₀ ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (P : Herm n) (T : ℝ) (i j : Fin n) :
    ContinuousOn (fun τ => (P.conjTranspose * gMat (h (t * Real.exp τ)) x * P)⁻¹ i j) (Icc 0 T) := by
  simp only [Matrix.mul_inv_rev, Matrix.mul_apply]
  apply continuousOn_finsetSum
  intro l _
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finsetSum
  intro a _
  exact (logarithmic_gMat_inverse_contDiff hflow x ht l a).continuous.continuousOn.mul continuousOn_const

theorem metricStripCurve_dualNorm (x : Pt X) (P : Herm n) {t : ℝ} (ht : 0 < t)
    (μ : Fin n → ℝ) (a : ComplexVector n) (z : ℂ) :
    dualNormChart (h (Real.exp (2 * (metricStripCurve (chartPt x x) P t μ a z).2.2.re))) x
      (metricStripCurve (chartPt x x) P t μ a z).1
      (metricStripCurve (chartPt x x) P t μ a z).2.1 =
        dualNormMat (P.conjTranspose * gMat (h (t * Real.exp z.re)) x * P) (stripCovector μ a z) := by
  rw [metricStripCurve_time _ _ ht]
  change dualNormMat (gMat (h (t * Real.exp z.re)) x)
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (P⁻¹).transpose (stripCovector μ a z)) = _
  rw [dualNormMat_conjugate]
  rfl

theorem fixed_frame_geometric_strip_bound
    (hflow : FlowStage X o h U P₀ ρ) (hjoint : JointPositiveClock X h)
    {t T : ℝ} (ht : 0 < t) (hT : 0 < T) (P : Herm n) (μ : Fin n → ℝ)
    (hstart : P.conjTranspose * gMat (h t) o * P = 1)
    (hfinish : P.conjTranspose * gMat (h (t * Real.exp T)) o * P =
      Matrix.diagonal (fun i => (Real.exp (-μ i * T) : ℂ))) (a : ComplexVector n) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T →
      dualNormMat (P.conjTranspose * gMat (h (t * Real.exp z.re)) o * P)
        (stripCovector μ a z) ≤ ∑ i, ‖a i‖ ^ 2 := by
  let H : ℝ → Herm n := fun τ => P.conjTranspose * gMat (h (t * Real.exp τ)) o * P
  obtain ⟨C, hC⟩ := dualNormMat_strip_bounded H μ a T (fixed_frame_inverse_continuousOn hflow o ht P T)
  let γ := metricStripCurve (chartPt o o) P t μ a
  have hγ : ∀ z : ℂ, ContDiffAt ℂ 2 γ z := fun z =>
    ((metricStripCurve_contDiff (chartPt o o) P t μ a).of_le (by norm_num)).contDiffAt
  have hchart : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T → (γ z).1 ∈ chartTarget o :=
    fun _ _ _ => mem_extChartAt_target o
  have hnorm := jointPositiveClock_bounded_strip hflow hjoint o γ T (∑ i, ‖a i‖ ^ 2) C hT hγ hchart
  have hbound : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T →
      dualNormChart (h (Real.exp (2 * (γ z).2.2.re))) o (γ z).1 (γ z).2.1 ≤ C := by
    intro z hz₀ hzT
    dsimp only [γ]
    rw [metricStripCurve_dualNorm o P ht]
    exact hC z hz₀ hzT
  have hleft : ∀ y : ℝ,
      dualNormChart (h (Real.exp (2 * (γ ((y : ℂ) * Complex.I)).2.2.re))) o
        (γ ((y : ℂ) * Complex.I)).1 (γ ((y : ℂ) * Complex.I)).2.1 ≤ ∑ i, ‖a i‖ ^ 2 := by
    intro y
    dsimp only [γ]
    rw [metricStripCurve_dualNorm o P ht]
    have hz : ((y : ℂ) * Complex.I).re = 0 := by simp
    rw [hz, Real.exp_zero, mul_one, hstart]
    have hb := stripCovector_diagonal_boundary μ a 0 ((y : ℂ) * Complex.I) hz
    simpa only [mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, Matrix.diagonal_one] using hb.le
  have hright : ∀ y : ℝ,
      dualNormChart (h (Real.exp (2 * (γ ((T : ℂ) + (y : ℂ) * Complex.I)).2.2.re))) o
        (γ ((T : ℂ) + (y : ℂ) * Complex.I)).1
        (γ ((T : ℂ) + (y : ℂ) * Complex.I)).2.1 ≤ ∑ i, ‖a i‖ ^ 2 := by
    intro y
    dsimp only [γ]
    rw [metricStripCurve_dualNorm o P ht]
    have hz : ((T : ℂ) + (y : ℂ) * Complex.I).re = T := by simp
    rw [hz, hfinish]
    exact (stripCovector_diagonal_boundary μ a T _ hz).le
  intro z hz₀ hzT
  rw [← metricStripCurve_dualNorm o P ht]
  exact hnorm hbound hleft hright z hz₀ hzT

end Yau.Blueprint.Alignment.Y03Proof
