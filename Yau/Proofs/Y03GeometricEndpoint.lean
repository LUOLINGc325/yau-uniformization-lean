import Yau.Proofs.Y03StepMetric
import Yau.Proofs.Y03FlowDerivative
import Yau.Proofs.Y03EndpointForms

/-! Endpoint derivative inequalities for the original metric flow in the actual fixed frame. -/

open scoped Topology ContDiff Matrix
open Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X} {h : Flow X} {U P₀ ρ : STF X}

theorem matrix_det_eventually_isUnit {H : ℝ → Herm n} {x : ℝ}
    (hc : ∀ i j, ContinuousAt (fun y => H y i j) x) (hd : IsUnit (H x).det) :
    ∀ᶠ y in 𝓝 x, IsUnit (H y).det := by
  have hmat : ContinuousAt H x := continuousAt_pi.2 fun i => continuousAt_pi.2 (hc i)
  have hdc : ContinuousAt (fun y => (H y).det) x :=
    continuous_id.matrix_det.continuousAt.comp hmat
  filter_upwards [hdc.eventually_ne hd.ne_zero] with y hy
  exact isUnit_iff_ne_zero.2 hy

theorem fixed_frame_inverse_contDiff (hflow : FlowStage X o h U P₀ ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (P : Herm n) (i j : Fin n) :
    ContDiff ℝ ∞ (fun τ => (P.conjTranspose * gMat (h (t * Real.exp τ)) x * P)⁻¹ i j) := by
  simp only [Matrix.mul_inv_rev, Matrix.mul_apply]
  apply ContDiff.sum
  intro l _
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro a _
  exact (logarithmic_gMat_inverse_contDiff hflow x ht l a).mul contDiff_const

theorem fixed_frame_geometric_endpoint_order
    (hflow : FlowStage X o h U P₀ ρ) (hjoint : JointPositiveClock X h)
    {t T : ℝ} (ht : 0 < t) (hT : 0 < T) (P : Herm n) (μ : Fin n → ℝ)
    (hstart : P.conjTranspose * gMat (h t) o * P = 1)
    (hfinish : P.conjTranspose * gMat (h (t * Real.exp T)) o * P =
      Matrix.diagonal (fun i => (Real.exp (-μ i * T) : ℂ))) (v : Fin n → ℂ) :
    matrixForm (P.conjTranspose * ((t : ℂ) • ricci (h t) o) * P) v ≤
        ∑ i, μ i * ‖v i‖ ^ 2 ∧
      (∑ i, μ i * Real.exp (μ i * T) * ‖v i‖ ^ 2) ≤
        matrixForm ((P.conjTranspose * gMat (h (t * Real.exp T)) o * P)⁻¹ *
          (P.conjTranspose * (((t * Real.exp T : ℝ) : ℂ) • ricci (h (t * Real.exp T)) o) * P) *
          (P.conjTranspose * gMat (h (t * Real.exp T)) o * P)⁻¹) v := by
  let H : ℝ → Herm n := fun τ => P.conjTranspose * gMat (h (t * Real.exp τ)) o * P
  have hH (τ : ℝ) := fixed_frame_logarithmic_metric_hasDerivAt hflow.1.1 o P ht τ
  have hK (τ : ℝ) (i j : Fin n) : DifferentiableAt ℝ (fun y => (H y)⁻¹ i j) τ :=
    (fixed_frame_inverse_contDiff hflow o ht P i j).differentiable (by norm_num) τ
  have hdet0 : IsUnit (H 0).det := by
    simp only [H, Real.exp_zero, mul_one, hstart, Matrix.det_one, isUnit_one]
  have hdetT : IsUnit (H T).det := by
    change IsUnit (P.conjTranspose * gMat (h (t * Real.exp T)) o * P).det
    rw [hfinish, Matrix.det_diagonal]
    apply isUnit_iff_ne_zero.2
    apply Finset.prod_ne_zero_iff.2
    intro i _
    exact Complex.ofReal_ne_zero.2 (ne_of_gt (Real.exp_pos _))
  have hdet (τ : ℝ) (hτ : IsUnit (H τ).det) : ∀ᶠ y in 𝓝 τ, IsUnit (H y).det :=
    matrix_det_eventually_isUnit (fun i j => (hH τ i j).continuousAt) hτ
  have hstrip := fixed_frame_geometric_strip_bound hflow hjoint ht hT P μ hstart hfinish
  constructor
  · apply inverse_form_left_endpoint H _ μ hT (by simpa only [H, Real.exp_zero, mul_one] using hstart)
      hstrip _ (hK 0) (hdet 0 hdet0) v
    intro i j
    simpa only [H, Real.exp_zero, mul_one] using hH 0 i j
  · exact inverse_form_right_endpoint H _ μ hT hfinish hstrip (hH T) (hK T) (hdet T hdetT) v

end Yau.Blueprint.Alignment.Y03Proof
