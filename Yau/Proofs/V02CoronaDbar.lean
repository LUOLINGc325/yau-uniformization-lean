import Yau.Proofs.V02DbarLinear
import Yau.Proofs.V02ClosedHolomorphic
import Yau.Proofs.V02CoronaAlgebra

/-! The within-disc antiholomorphic derivative and the genuine Cauchy--Riemann
criterion used by the finite corona construction. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.LeafProofs

def discDbarWithin (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (discEnergyPartial f 1 z + Complex.I * discEnergyPartial f Complex.I z)

theorem discDbarWithin_contDiffOn {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (discDbarWithin f) (Metric.closedBall (0 : ℂ) 1) :=
  contDiffOn_const.mul ((discEnergyPartial_contDiffOn hf 1).add
    (contDiffOn_const.mul (discEnergyPartial_contDiffOn hf Complex.I)))

theorem discDbarWithin_eq_wirtBar (f : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) : discDbarWithin f z = wirtBar f z 1 := by
  simp only [discDbarWithin, wirtBar, discEnergyPartial_eq_fderiv _ _ hz,
    smul_eq_mul, mul_one]

theorem differentiableAt_complex_of_wirtBar_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hbar : wirtBar f z 1 = 0) :
    DifferentiableAt ℂ f z := by
  let D := fderiv ℝ f z
  let L : ℂ →L[ℂ] ℂ := (1 : ℂ →L[ℂ] ℂ).smulRight (D 1)
  have hraw : D 1 + Complex.I * D Complex.I = 0 := by
    change (1 / 2 : ℂ) * (D 1 + Complex.I * D (Complex.I • (1 : ℂ))) = 0 at hbar
    simp only [smul_eq_mul, mul_one] at hbar
    linear_combination (2 : ℂ) * hbar
  have hI : D Complex.I = Complex.I * D 1 := by
    linear_combination -Complex.I * hraw + D Complex.I * Complex.I_sq
  have he : L.restrictScalars ℝ = D := by
    apply ContinuousLinearMap.ext
    intro v
    change v * D 1 = D v
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by simp [Complex.real_smul]
    conv_rhs => rw [hv, map_add, map_smul, map_smul, hI]
    conv_lhs => rw [← Complex.re_add_im v]
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  exact (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt he).differentiableAt

variable {ι : Type*} [Fintype ι]

def coronaDbarDensity (σ : ι → ℂ → ℂ) (i j : ι) (z : ℂ) : ℂ :=
  σ i z * discDbarWithin (σ j) z - σ j z * discDbarWithin (σ i) z

theorem coronaDbarDensity_contDiffOn {σ : ι → ℂ → ℂ}
    (hσ : ∀ i, ContDiffOn ℝ ∞ (σ i) (Metric.closedBall (0 : ℂ) 1)) (i j : ι) :
    ContDiffOn ℝ ∞ (coronaDbarDensity σ i j) (Metric.closedBall (0 : ℂ) 1) :=
  ((hσ i).mul (discDbarWithin_contDiffOn (hσ j))).sub
    ((hσ j).mul (discDbarWithin_contDiffOn (hσ i)))

theorem coronaDbarDensity_skew (σ : ι → ℂ → ℂ) (i j : ι) (z : ℂ) :
    coronaDbarDensity σ i j z = -coronaDbarDensity σ j i z := by
  unfold coronaDbarDensity
  ring

def coronaDbarCorrection (σ : ι → ℂ → ℂ) (i j : ι) : ℂ → ℂ :=
  discDbarSolution (coronaDbarDensity σ i j)

theorem coronaDbarCorrection_contDiffOn {σ : ι → ℂ → ℂ}
    (hσ : ∀ i, ContDiffOn ℝ ∞ (σ i) (Metric.closedBall (0 : ℂ) 1)) (i j : ι) :
    ContDiffOn ℝ ∞ (coronaDbarCorrection σ i j) (Metric.closedBall (0 : ℂ) 1) :=
  discDbarSolution_contDiffOn (coronaDbarDensity_contDiffOn hσ i j)

theorem coronaDbarCorrection_skew {σ : ι → ℂ → ℂ}
    (hσ : ∀ i, ContDiffOn ℝ ∞ (σ i) (Metric.closedBall (0 : ℂ) 1))
    (i j : ι) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    coronaDbarCorrection σ i j z = -coronaDbarCorrection σ j i z :=
  discDbarSolution_skew (coronaDbarDensity σ) (coronaDbarDensity_contDiffOn hσ)
    (fun i j z _ => coronaDbarDensity_skew σ i j z) i j hz

theorem coronaDbarCorrection_dbar {σ : ι → ℂ → ℂ}
    (hσ : ∀ i, ContDiffOn ℝ ∞ (σ i) (Metric.closedBall (0 : ℂ) 1))
    (i j : ι) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    wirtBar (coronaDbarCorrection σ i j) z 1 = coronaDbarDensity σ i j z :=
  discDbarSolution_dbar (coronaDbarDensity_contDiffOn hσ i j) hz

end Yau.Blueprint.V02Proof
