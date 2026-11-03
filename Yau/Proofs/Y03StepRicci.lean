import Yau.Proofs.Y03GeometricEndpoint
import Yau.Proofs.Y03NormalizeEndpoint

/-! Both instantaneous Ricci endpoints are expressed in the given step's singular frames. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {X : KahlerManifold n}

def chartFrameRicci (o : Pt X) (h : Flow X) (Φ : ℝ → ComplexVector n → Pt X)
    (t : ℝ) (V : Herm n) : Herm n :=
  (centerFrameMatrix o (Φ t) * V).conjTranspose * ((t : ℂ) • ricci (h t) o) *
    (centerFrameMatrix o (Φ t) * V)

theorem diagonal_eq_endpointDiagonal {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E) (k : ℕ) :
    diagonal F tk E k = endpointDiagonal (rate F tk E k) (Real.log (tk (k + 1) / tk k)) := by
  unfold diagonal endpointDiagonal
  apply congrArg Matrix.diagonal
  funext i
  rw [singularLength_eq_exp_rate hE k i]

theorem stepFixedFrame_ricci_finish {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    (hlate : ∀ k, t₀ ≤ tk k) (k : ℕ) :
    (stepFixedFrame o Φ tk E k).conjTranspose *
      ((tk (k + 1) : ℂ) • ricci (h (tk (k + 1))) o) * stepFixedFrame o Φ tk E k =
      endpointDiagonal (rate F tk E k) (Real.log (tk (k + 1) / tk k)) *
        chartFrameRicci o h Φ (tk (k + 1)) (E.finish k) *
        endpointDiagonal (rate F tk E k) (Real.log (tk (k + 1) / tk k)) := by
  rw [stepFixedFrame_finish hCharts hE hlate, diagonal_eq_endpointDiagonal hE,
    Matrix.conjTranspose_mul]
  simp only [endpointDiagonal, real_diagonal_conjTranspose]
  unfold chartFrameRicci
  noncomm_ring

theorem actual_step_endpoint_ricci_order {o : Pt X} {h : Flow X} {U P₀ ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hflow : FlowStage X o h U P₀ ρ) (hjoint : JointPositiveClock X h)
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    (hlate : ∀ k, t₀ ≤ tk k) (k : ℕ) (v : Fin n → ℂ) :
    matrixForm (chartFrameRicci o h Φ (tk k) (E.start k)) v ≤
        ∑ i, rate F tk E k i * ‖v i‖ ^ 2 ∧
      (∑ i, rate F tk E k i * ‖v i‖ ^ 2) ≤
        matrixForm (chartFrameRicci o h Φ (tk (k + 1)) (E.finish k)) v := by
  let T := Real.log (tk (k + 1) / tk k)
  let μ := rate F tk E k
  have ht' : 0 < tk (k + 1) := (hE (k + 1)).1
  have heq : tk k * Real.exp T = tk (k + 1) := by
    dsimp [T]
    rw [Real.exp_log (div_pos ht' (hE k).1)]
    field_simp [ne_of_gt (hE k).1]
  have hfinish : (stepFixedFrame o Φ tk E k).conjTranspose *
      gMat (h (tk k * Real.exp T)) o * stepFixedFrame o Φ tk E k =
        Matrix.diagonal (fun i => (Real.exp (-μ i * T) : ℂ)) := by
    rw [heq]
    exact stepFixedFrame_gram_finish hCharts hE hlate k
  have hb (w : Fin n → ℂ) := fixed_frame_geometric_endpoint_order hflow hjoint (hE k).1
    (log_time_ratio_pos (hE k).1 (hE k).2.1) (stepFixedFrame o Φ tk E k) μ
    (stepFixedFrame_gram_start hCharts hE hlate k) hfinish w
  constructor
  · exact (hb v).1
  · apply right_endpoint_form_normalization μ T _ _ v
    intro w
    have hr := (hb w).2
    rw [hfinish, inverse_exp_diagonal, heq, stepFixedFrame_ricci_finish hCharts hE hlate] at hr
    exact hr

end Yau.Blueprint.Alignment.Y03Proof
