import Yau.Proofs.V02CoronaDbar

/-! The actual finite corona correction uses the canonical Green operator.
Its holomorphicity and Bezout identity are proved from the defining formula. -/

open scoped Topology ContDiff
open Filter Finset

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.LeafProofs

variable {ι : Type*} [Fintype ι]

def coronaSolution (a σ : ι → ℂ → ℂ) (i : ι) (z : ℂ) : ℂ :=
  σ i z + ∑ j, coronaDbarCorrection σ i j z * a j z

theorem coronaSolution_real_contDiffOn {a σ : ι → ℂ → ℂ}
    (ha : ∀ i, ContDiffOn ℂ ∞ (a i) (Metric.closedBall (0 : ℂ) 1))
    (hσ : ∀ i, ContDiffOn ℝ ∞ (σ i) (Metric.closedBall (0 : ℂ) 1)) (i : ι) :
    ContDiffOn ℝ ∞ (coronaSolution a σ i) (Metric.closedBall (0 : ℂ) 1) :=
  (hσ i).add (ContDiffOn.sum (fun j _ =>
    (coronaDbarCorrection_contDiffOn hσ i j).mul ((ha j).restrict_scalars ℝ)))

theorem normalized_dbar_sum_zero {a σ : ι → ℂ → ℂ}
    (ha : ∀ i, ContDiffOn ℂ ∞ (a i) (Metric.closedBall (0 : ℂ) 1))
    (hσ : ∀ i, ContDiffOn ℝ ∞ (σ i) (Metric.closedBall (0 : ℂ) 1))
    (hnorm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, σ i z * a i z = 1)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ∑ i, wirtBar (σ i) z 1 * a i z = 0 := by
  have hc (i : ι) : DifferentiableAt ℂ (a i) z :=
    ((ha i).contDiffAt (discEnergy_closedBall_mem_nhds hz)).differentiableAt (by simp)
  have hs (i : ι) : DifferentiableAt ℝ (σ i) z :=
    (discEnergy_contDiffAt (hσ i) hz).differentiableAt (by simp)
  have hp (i : ι) : DifferentiableAt ℝ (fun w => σ i w * a i w) z :=
    (hs i).mul ((hc i).restrictScalars ℝ)
  have he : (fun w => ∑ i, σ i w * a i w) =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact hnorm w (Metric.ball_subset_closedBall hw)
  have hzbar : wirtBar (fun w => ∑ i, σ i w * a i w) z 1 = 0 := by
    simp only [wirtBar, he.fderiv_eq, fderiv_fun_const, Pi.zero_apply, zero_apply,
      smul_eq_mul, mul_zero, add_zero]
  calc
    _ = ∑ i, wirtBar (fun w => σ i w * a i w) z 1 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [V03Proof.wirtBar_mul (hs i) ((hc i).restrictScalars ℝ),
        V03Proof.wirtBar_holomorphic (hc i)]
      ring
    _ = wirtBar (fun w => ∑ i, σ i w * a i w) z 1 :=
      (V03Proof.wirtBar_sum Finset.univ (fun i w => σ i w * a i w) z 1 (fun i _ => hp i)).symm
    _ = 0 := hzbar

theorem coronaSolution_dbar_zero {a σ : ι → ℂ → ℂ}
    (ha : ∀ i, ContDiffOn ℂ ∞ (a i) (Metric.closedBall (0 : ℂ) 1))
    (hσ : ∀ i, ContDiffOn ℝ ∞ (σ i) (Metric.closedBall (0 : ℂ) 1))
    (hnorm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, σ i z * a i z = 1)
    (i : ι) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    wirtBar (coronaSolution a σ i) z 1 = 0 := by
  classical
  have hc (j : ι) : DifferentiableAt ℂ (a j) z :=
    ((ha j).contDiffAt (discEnergy_closedBall_mem_nhds hz)).differentiableAt (by simp)
  have hs : DifferentiableAt ℝ (σ i) z :=
    (discEnergy_contDiffAt (hσ i) hz).differentiableAt (by simp)
  have hQ (j : ι) : DifferentiableAt ℝ (coronaDbarCorrection σ i j) z :=
    (discEnergy_contDiffAt (coronaDbarCorrection_contDiffOn hσ i j) hz).differentiableAt (by simp)
  have hp (j : ι) : DifferentiableAt ℝ (fun w => coronaDbarCorrection σ i j w * a j w) z :=
    (hQ j).mul ((hc j).restrictScalars ℝ)
  have hsum : DifferentiableAt ℝ (fun w => ∑ j, coronaDbarCorrection σ i j w * a j w) z :=
    DifferentiableAt.fun_sum (fun j _ => hp j)
  have hterm (j : ι) :
      wirtBar (fun w => coronaDbarCorrection σ i j w * a j w) z 1 =
        coronaDbarDensity σ i j z * a j z := by
    rw [V03Proof.wirtBar_mul (hQ j) ((hc j).restrictScalars ℝ),
      coronaDbarCorrection_dbar hσ i j hz, V03Proof.wirtBar_holomorphic (hc j)]
    ring
  calc
    _ = wirtBar (σ i) z 1 + ∑ j, coronaDbarDensity σ i j z * a j z := by
      unfold coronaSolution
      rw [V03Proof.wirtBar_add (σ i) (fun w => ∑ j, coronaDbarCorrection σ i j w * a j w) z 1 hs hsum,
        V03Proof.wirtBar_sum Finset.univ (fun j w => coronaDbarCorrection σ i j w * a j w)
          z 1 (fun j _ => hp j)]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => hterm j)
    _ = 0 := by
      simp_rw [coronaDbarDensity, discDbarWithin_eq_wirtBar _ hz]
      exact corona_dbar_correction_zero (fun j => a j z) (fun j => σ j z)
        (fun j => wirtBar (σ j) z 1) (hnorm z (Metric.ball_subset_closedBall hz))
        (normalized_dbar_sum_zero ha hσ hnorm hz) i

theorem coronaSolution_complex_contDiffOn {a σ : ι → ℂ → ℂ}
    (ha : ∀ i, ContDiffOn ℂ ∞ (a i) (Metric.closedBall (0 : ℂ) 1))
    (hσ : ∀ i, ContDiffOn ℝ ∞ (σ i) (Metric.closedBall (0 : ℂ) 1))
    (hnorm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, σ i z * a i z = 1) (i : ι) :
    ContDiffOn ℂ ∞ (coronaSolution a σ i) (Metric.closedBall (0 : ℂ) 1) := by
  have hr := coronaSolution_real_contDiffOn ha hσ i
  apply real_closed_holomorphic_contDiffOn hr
  intro z hz
  exact (differentiableAt_complex_of_wirtBar_zero
    ((discEnergy_contDiffAt hr hz).differentiableAt (by simp))
    (coronaSolution_dbar_zero ha hσ hnorm i hz)).differentiableWithinAt

theorem coronaSolution_sum_eq_one {a σ : ι → ℂ → ℂ}
    (hσ : ∀ i, ContDiffOn ℝ ∞ (σ i) (Metric.closedBall (0 : ℂ) 1))
    (hnorm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, σ i z * a i z = 1)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    ∑ i, coronaSolution a σ i z * a i z = 1 := by
  classical
  exact corona_sum_eq_one (fun i => a i z) (fun i => σ i z)
    (fun i j => coronaDbarCorrection σ i j z) (hnorm z hz)
      (fun i j => coronaDbarCorrection_skew hσ i j hz)

end Yau.Blueprint.V02Proof
