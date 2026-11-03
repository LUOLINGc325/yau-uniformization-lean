import Yau.Proofs.D05ScalarCauchyGreenLinear
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Smooth localization for the actual scalar Cauchy–Green operator.
One fixed cutoff gives one linear operator for every matrix coefficient. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau

theorem contDiff_cutoff_product {U : Set ℂ} (hU : IsOpen U) {b : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b U) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun z => (χ z : ℂ) * b z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hχ.contDiffAt).mul
      ((hb z (hsχ hz)).contDiffAt (hU.mem_nhds (hsχ hz)))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with w hw
    simp [image_eq_zero_of_notMem_tsupport hw]

def cutoffDbarSolution (χ : ℂ → ℝ) (b : ℂ → ℂ) : ℂ → ℂ :=
  compactDbarSolution (fun z => (χ z : ℂ) * b z)

theorem cutoffDbarSolution_smooth {U : Set ℂ} (hU : IsOpen U) {b : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b U) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ U) (hcχ : HasCompactSupport χ) :
    ContDiff ℝ ∞ (cutoffDbarSolution χ b) := by
  exact compactDbarSolution_smooth (contDiff_cutoff_product hU hb hχ hsχ)
    ((hcχ.comp_left (g := Complex.ofReal) (by simp)).mul_right)

theorem cutoffDbarSolution_dbar {U : Set ℂ} (hU : IsOpen U) {b : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b U) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ U) (hcχ : HasCompactSupport χ)
    {z : ℂ} (hz : χ z = 1) :
    wirtBar (cutoffDbarSolution χ b) z 1 = b z := by
  rw [cutoffDbarSolution, compactDbarSolution_dbar
    (contDiff_cutoff_product hU hb hχ hsχ)
    ((hcχ.comp_left (g := Complex.ofReal) (by simp)).mul_right), hz]
  simp

theorem cutoffDbarSolution_neg {U : Set ℂ} (hU : IsOpen U) {b : ℂ → ℂ}
    (hb : ContDiffOn ℝ ∞ b U) {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ U) (hcχ : HasCompactSupport χ) :
    cutoffDbarSolution χ (fun z => -b z) = fun z => -cutoffDbarSolution χ b z := by
  have heq : (fun z => (χ z : ℂ) * -b z) =
      fun z => -((χ z : ℂ) * b z) := by
    funext z
    ring
  unfold cutoffDbarSolution
  rw [heq, compactDbarSolution_neg (contDiff_cutoff_product hU hb hχ hsχ)
    ((hcχ.comp_left (g := Complex.ofReal) (by simp)).mul_right)]

theorem disc_cutoff_exists {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Metric.ball (0 : ℂ) R ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) ρ, χ z = 1 := by
  let χ : ContDiffBump (0 : ℂ) :=
    { rIn := ρ
      rOut := (ρ + R) / 2
      rIn_pos := hρ
      rIn_lt_rOut := by linarith }
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, ?_, ?_⟩
  · rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [χ]; linarith)
  · exact fun z hz => χ.one_of_mem_closedBall hz

theorem differentiableAt_of_wirtBar_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hd : wirtBar f z 1 = 0) :
    DifferentiableAt ℂ f z := by
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨hf, ?_⟩
  have hsum : fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I = 0 := by
    simpa only [wirtBar, smul_eq_mul, mul_one, mul_eq_zero,
      div_ne_zero (by norm_num : (1 : ℂ) ≠ 0) (by norm_num : (2 : ℂ) ≠ 0),
      false_or] using hd
  simp only [smul_eq_mul]
  linear_combination -Complex.I * hsum + fderiv ℝ f z Complex.I * Complex.I_sq

end Yau.Blueprint.D05Proof
