import Yau.Proofs.Y03CenterFrame
import Yau.Proofs.Y03MetricStrip

/-! The strip endpoints come from the given charts and the actual transition's singular frames. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {X : KahlerManifold n}

def stepFixedFrame (o : Pt X) (Φ : ℝ → ComplexVector n → Pt X) (tk : ℕ → ℝ)
    (E : Frames n) (k : ℕ) : Herm n := centerFrameMatrix o (Φ (tk k)) * E.start k

theorem stepFixedFrame_gram_start {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    (hlate : ∀ k, t₀ ≤ tk k) (k : ℕ) :
    (stepFixedFrame o Φ tk E k).conjTranspose * gMat (h (tk k)) o * stepFixedFrame o Φ tk E k = 1 := by
  have hgram := unitaryChart_centerFrame_gram (hCharts.2.2.2.2.1 (tk k) (hlate k))
  unfold stepFixedFrame
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (E.start k).conjTranspose *
        ((centerFrameMatrix o (Φ (tk k))).conjTranspose * gMat (h (tk k)) o *
          centerFrameMatrix o (Φ (tk k))) * E.start k := by noncomm_ring
    _ = 1 := by rw [hgram, Matrix.mul_one, (hE k).2.2.1.1]

theorem stepFixedFrame_finish {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    (hlate : ∀ k, t₀ ≤ tk k) (k : ℕ) :
    stepFixedFrame o Φ tk E k = centerFrameMatrix o (Φ (tk (k + 1))) * E.finish k * diagonal F tk E k := by
  have htrans := hCharts.2.2.2.2.2.1 (tk k) (tk (k + 1)) (hlate k) (hE k).2.1.le
  have hchain := centerFrameMatrix_chain o hCharts.1 (hCharts.1.trans hCharts.2.1)
    (hCharts.2.2.2.2.1 (tk (k + 1)) (hlate (k + 1))).1.1
    htrans.1 htrans.2.2.1 htrans.2.2.2.1
  have hAV : derivativeMatrix (F (tk k) (tk (k + 1))) * E.start k =
      E.finish k * diagonal F tk E k := by
    calc
      _ = (E.finish k * (E.finish k).conjTranspose) *
          (derivativeMatrix (F (tk k) (tk (k + 1))) * E.start k) := by
        rw [(hE k).2.2.2.1.2, Matrix.one_mul]
      _ = E.finish k * transformedDerivative F tk E k := by
        unfold transformedDerivative
        noncomm_ring
      _ = _ := by rw [(hE k).2.2.2.2.1]
  unfold stepFixedFrame
  rw [← hchain]
  calc
    _ = centerFrameMatrix o (Φ (tk (k + 1))) *
        (derivativeMatrix (F (tk k) (tk (k + 1))) * E.start k) := by noncomm_ring
    _ = _ := by rw [hAV, Matrix.mul_assoc]

theorem stepFixedFrame_gram_finish {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    (hlate : ∀ k, t₀ ≤ tk k) (k : ℕ) :
    (stepFixedFrame o Φ tk E k).conjTranspose * gMat (h (tk (k + 1))) o * stepFixedFrame o Φ tk E k =
      Matrix.diagonal (fun i => (Real.exp (-rate F tk E k i * Real.log (tk (k + 1) / tk k)) : ℂ)) := by
  have hgram := unitaryChart_centerFrame_gram (hCharts.2.2.2.2.1 (tk (k + 1)) (hlate (k + 1)))
  rw [stepFixedFrame_finish hCharts hE hlate, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have hDstar : (diagonal F tk E k).conjTranspose = diagonal F tk E k := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [diagonal, Matrix.conjTranspose_apply]
    · simp [diagonal, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  rw [hDstar]
  calc
    _ = diagonal F tk E k * ((E.finish k).conjTranspose *
        ((centerFrameMatrix o (Φ (tk (k + 1)))).conjTranspose * gMat (h (tk (k + 1))) o *
          centerFrameMatrix o (Φ (tk (k + 1)))) * E.finish k) * diagonal F tk E k := by noncomm_ring
    _ = diagonal F tk E k * diagonal F tk E k := by
      rw [hgram, Matrix.mul_one, (hE k).2.2.2.1.1, Matrix.mul_one]
    _ = _ := by
      unfold diagonal
      rw [Matrix.diagonal_mul_diagonal]
      apply congrArg Matrix.diagonal
      funext i
      rw [← Complex.ofReal_mul, singularLength_eq_exp_rate hE k i, ← Real.exp_add]
      congr 1
      ring

theorem actual_step_geometric_strip_bound {o : Pt X} {h : Flow X} {U P₀ ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hflow : FlowStage X o h U P₀ ρ) (hjoint : JointPositiveClock X h)
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    (hlate : ∀ k, t₀ ≤ tk k) (k : ℕ) (a : ComplexVector n) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ Real.log (tk (k + 1) / tk k) →
      dualNormMat ((stepFixedFrame o Φ tk E k).conjTranspose *
        gMat (h (tk k * Real.exp z.re)) o * stepFixedFrame o Φ tk E k)
        (stripCovector (rate F tk E k) a z) ≤ ∑ i, ‖a i‖ ^ 2 := by
  have ht' : 0 < tk (k + 1) := (hE (k + 1)).1
  have heq : tk k * Real.exp (Real.log (tk (k + 1) / tk k)) = tk (k + 1) := by
    rw [Real.exp_log (div_pos ht' (hE k).1)]
    field_simp [ne_of_gt (hE k).1]
  apply fixed_frame_geometric_strip_bound hflow hjoint (hE k).1
    (log_time_ratio_pos (hE k).1 (hE k).2.1) (stepFixedFrame o Φ tk E k) (rate F tk E k)
    (stepFixedFrame_gram_start hCharts hE hlate k)
  rw [heq]
  exact stepFixedFrame_gram_finish hCharts hE hlate k

end Yau.Blueprint.Alignment.Y03Proof
