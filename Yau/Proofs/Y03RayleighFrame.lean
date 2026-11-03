import Yau.Proofs.Y03StepRicci
import Yau.Proofs.Y03Rayleigh

/-! Compare the actual Ricci minimum with normalized singular-frame directions. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem matrixForm_single (A : Herm n) (i : Fin n) :
    matrixForm A (Pi.single i 1) = (A i i).re := by
  simp [matrixForm, dotProduct, Matrix.mulVec, Pi.single_apply]

theorem relative_min_le_unit_frame {G A P : Herm n}
    (hmin : 0 < relMinEigenvalue G A) (hgram : P.conjTranspose * G * P = 1) (i : Fin n) :
    relMinEigenvalue G A ≤ ((P.conjTranspose * A * P) i i).re := by
  let e : Fin n → ℂ := Pi.single i 1
  let w := P *ᵥ e
  have hden : matrixForm G w = 1 := by
    rw [matrixForm_conjugate, hgram, matrixForm_single]
    simp
  have hw : (WithLp.toLp 2 w : ComplexVector n) ≠ 0 := by
    intro hz
    have hwzero : w = 0 := by
      exact congrArg WithLp.ofLp hz
    have : matrixForm G w = 0 := by simp [matrixForm, hwzero]
    linarith
  have hl := relMinEigenvalue_le_of_pos hmin (WithLp.toLp 2 w) hw
  change relMinEigenvalue G A ≤ matrixForm A w / matrixForm G w at hl
  rw [hden, div_one, matrixForm_conjugate, matrixForm_single] at hl
  exact hl

theorem actual_rate_ge_ricciMin {X : KahlerManifold n} {o : Pt X} {h : Flow X} {U P₀ ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hflow : FlowStage X o h U P₀ ρ) (hjoint : JointPositiveClock X h)
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E)
    (hlate : ∀ k, t₀ ≤ tk k) (k : ℕ) (hmin : 0 < ricciMin o h (tk k)) (i : Fin n) :
    ricciMin o h (tk k) ≤ rate F tk E k i := by
  have hl := relative_min_le_unit_frame hmin (stepFixedFrame_gram_start hCharts hE hlate k) i
  have hu := (actual_step_endpoint_ricci_order hflow hjoint hCharts hE hlate k (Pi.single i 1)).1
  rw [matrixForm_single] at hu
  have hs : (∑ j, rate F tk E k j * ‖(Pi.single i (1 : ℂ) : Fin n → ℂ) j‖ ^ 2) = rate F tk E k i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · simp
  rw [hs] at hu
  exact hl.trans hu

end Yau.Blueprint.Alignment.Y03Proof
