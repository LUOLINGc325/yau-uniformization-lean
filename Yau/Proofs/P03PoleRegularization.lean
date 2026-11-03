import Yau.Geometry.Calculus

open scoped Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

def poleEpsilon (j : ℕ) : ℝ := 1 / (4 * ((j : ℝ) + 1))

theorem poleEpsilon_pos (j : ℕ) : 0 < poleEpsilon j := by
  unfold poleEpsilon
  positivity

theorem poleEpsilon_le_quarter (j : ℕ) : poleEpsilon j ≤ 1 / 4 := by
  unfold poleEpsilon
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith

theorem poleEpsilon_antitone : Antitone poleEpsilon := by
  intro i j hij
  unfold poleEpsilon
  apply one_div_le_one_div_of_le (by positivity : 0 < 4 * ((i : ℝ) + 1))
  have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  nlinarith

def modelLogPole {n : ℕ} (a : ComplexVector n) (ε : ℝ) (z : ComplexVector n) : ℝ :=
  Real.log (‖z - a‖ ^ 2 + ε)

theorem modelLogPole_contDiff {n : ℕ} (a : ComplexVector n) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (modelLogPole a ε) := by
  have hq : ContDiff ℝ ∞ (fun z : ComplexVector n => ‖z - a‖ ^ 2 + ε) :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).add contDiff_const
  exact hq.log fun z => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hε)

theorem modelLogPole_mono_epsilon {n : ℕ} (a z : ComplexVector n)
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) :
    modelLogPole a ε z ≤ modelLogPole a δ z := by
  exact Real.log_le_log (add_pos_of_nonneg_of_pos (sq_nonneg _) hε) (by linarith)

theorem modelLogPole_nonpos {n : ℕ} (a z : ComplexVector n) {ε : ℝ}
    (hε : 0 < ε) (hbound : ‖z - a‖ ^ 2 + ε ≤ 1) : modelLogPole a ε z ≤ 0 :=
  Real.log_nonpos (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).le hbound

def cutoffPoleRegularization {n : ℕ} (c : ℝ) (θ : ComplexVector n → ℝ)
    (a : ComplexVector n) (ε : ℝ) (z : ComplexVector n) : ℝ :=
  c * θ z * modelLogPole a ε z

theorem cutoffPoleRegularization_contDiff {n : ℕ} (c : ℝ) (θ : ComplexVector n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (a : ComplexVector n) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (cutoffPoleRegularization c θ a ε) :=
  (contDiff_const.mul hθ).mul (modelLogPole_contDiff a hε)

theorem cutoffPoleRegularization_antitone {n : ℕ} (c : ℝ) (θ : ComplexVector n → ℝ)
    (hc : 0 ≤ c) (hθ : ∀ z, 0 ≤ θ z) (a z : ComplexVector n) :
    Antitone (fun j => cutoffPoleRegularization c θ a (poleEpsilon j) z) := by
  intro i j hij
  apply mul_le_mul_of_nonneg_left
    (modelLogPole_mono_epsilon a z (poleEpsilon_pos j) (poleEpsilon_antitone hij))
    (mul_nonneg hc (hθ z))

end Yau.NodeProofs.P03Aux
