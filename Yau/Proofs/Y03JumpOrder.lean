import Yau.Proofs.Y03StepRicci

/-! Shared endpoints give the covector order with the literal jump matrix. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {X : KahlerManifold n}

theorem chartFrameRicci_jump {o : Pt X} {h : Flow X}
    {Φ : ℝ → ComplexVector n → Pt X} {tk : ℕ → ℝ} {E : Frames n}
    (k : ℕ) (hU : Unitary (E.finish k)) :
    jump E k * chartFrameRicci o h Φ (tk (k + 1)) (E.finish k) * (jump E k).conjTranspose =
      chartFrameRicci o h Φ (tk (k + 1)) (E.start (k + 1)) := by
  unfold jump chartFrameRicci
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    _ = (E.start (k + 1)).conjTranspose * ((E.finish k * (E.finish k).conjTranspose) *
        ((centerFrameMatrix o (Φ (tk (k + 1)))).conjTranspose *
          ((tk (k + 1) : ℂ) • ricci (h (tk (k + 1))) o) *
          centerFrameMatrix o (Φ (tk (k + 1)))) *
        (E.finish k * (E.finish k).conjTranspose)) * E.start (k + 1) := by noncomm_ring
    _ = _ := by rw [hU.2, Matrix.one_mul, Matrix.mul_one]; noncomm_ring

theorem actual_covector_rate_order {o : Pt X} {h : Flow X} {U P₀ ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hflow : FlowStage X o h U P₀ ρ) (hjoint : JointPositiveClock X h)
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    (hlate : ∀ k, t₀ ≤ tk k) (k : ℕ) (v : Fin n → ℂ) :
    (∑ l, rate F tk E k l * ‖(v ᵥ* jump E k) l‖ ^ 2) ≤
      ∑ i, rate F tk E (k + 1) i * ‖v i‖ ^ 2 := by
  have hOld := (actual_step_endpoint_ricci_order hflow hjoint hCharts hE hlate k
    ((jump E k).conjTranspose *ᵥ star v)).2
  have hNew := (actual_step_endpoint_ricci_order hflow hjoint hCharts hE hlate (k + 1) (star v)).1
  rw [matrixForm_conjugate, Matrix.conjTranspose_conjTranspose,
    chartFrameRicci_jump k (hE k).2.2.2.1] at hOld
  have hb := hOld.trans hNew
  simpa only [Matrix.mulVec_conjTranspose, star_star, Pi.star_apply, norm_star] using hb

end Yau.Blueprint.Alignment.Y03Proof
