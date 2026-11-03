import Yau.Proofs.V03ClosedDiscTower
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Absolutely summable polynomially weighted coefficients define a
holomorphic power series with complex C∞ regularity on the closed disc. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof

def powerJetTerm (b : ℕ → ℂ) (k n : ℕ) (z : ℂ) : ℂ :=
  b n * (n.descFactorial k : ℂ) * z ^ (n - k)

def powerJet (b : ℕ → ℂ) (k : ℕ) (z : ℂ) : ℂ := ∑' n, powerJetTerm b k n z

theorem powerJetTerm_norm_le (b : ℕ → ℂ) (k n : ℕ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    ‖powerJetTerm b k n z‖ ≤ (n : ℝ) ^ k * ‖b n‖ := by
  have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hd : (n.descFactorial k : ℝ) ≤ (n : ℝ) ^ k := by
    exact_mod_cast Nat.descFactorial_le_pow n k
  have hn : ‖(n.descFactorial k : ℂ)‖ = (n.descFactorial k : ℝ) := by simp
  rw [powerJetTerm, norm_mul, norm_mul, norm_pow, hn]
  calc
    ‖b n‖ * (n.descFactorial k : ℝ) * ‖z‖ ^ (n - k) ≤
        ‖b n‖ * (n.descFactorial k : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg z) hz1) (by positivity)
    _ ≤ (n : ℝ) ^ k * ‖b n‖ := by
      simpa only [mul_one, mul_comm] using mul_le_mul_of_nonneg_left hd (norm_nonneg (b n))

theorem powerJetTerm_hasDerivAt (b : ℕ → ℂ) (k n : ℕ) (z : ℂ) :
    HasDerivAt (powerJetTerm b k n) (powerJetTerm b (k + 1) n z) z := by
  have he : n - k - 1 = n - (k + 1) := by omega
  convert (hasDerivAt_pow (n - k) z).const_mul (b n * (n.descFactorial k : ℂ)) using 1
  · rfl
  · simp only [powerJetTerm, Nat.descFactorial_succ, Nat.cast_mul, he]
    ring

theorem powerJet_continuousOn {b : ℕ → ℂ} (hb : ∀ k : ℕ,
    Summable (fun n : ℕ => (n : ℝ) ^ k * ‖b n‖)) (k : ℕ) :
    ContinuousOn (powerJet b k) (Metric.closedBall (0 : ℂ) 1) := by
  apply continuousOn_tsum (fun n => by unfold powerJetTerm; fun_prop) (hb k)
  exact fun n z hz => powerJetTerm_norm_le b k n hz

theorem powerJet_hasDerivAt {b : ℕ → ℂ} (hb : ∀ k : ℕ,
    Summable (fun n : ℕ => (n : ℝ) ^ k * ‖b n‖)) (k : ℕ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) : HasDerivAt (powerJet b k) (powerJet b (k + 1) z) z := by
  apply hasDerivAt_tsum_of_isPreconnected (hb (k + 1)) Metric.isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected
    (fun n w _ => powerJetTerm_hasDerivAt b k n w)
    (fun n w hw => powerJetTerm_norm_le b (k + 1) n (Metric.ball_subset_closedBall hw))
    (by simp : (0 : ℂ) ∈ Metric.ball 0 1)
  · exact Summable.of_norm_bounded (hb k) (fun n => powerJetTerm_norm_le b k n (by simp))
  · exact hz

theorem contDiffOn_powerSeries_closedDisc {b : ℕ → ℂ}
    (hb : ∀ k : ℕ, Summable (fun n : ℕ => (n : ℝ) ^ k * ‖b n‖)) :
    ContDiffOn ℂ ∞ (fun z => ∑' n, b n * z ^ n) (Metric.closedBall 0 1) := by
  have hh := contDiffOn_closedDisc_of_derivative_tower (powerJet b)
    (powerJet_continuousOn hb) (fun k z hz => powerJet_hasDerivAt hb k hz)
  have hzero : powerJet b 0 = fun z => ∑' n, b n * z ^ n := by
    funext z
    simp only [powerJet, powerJetTerm, Nat.descFactorial_zero, Nat.cast_one, mul_one, Nat.sub_zero]
  rw [hzero] at hh
  exact hh

end Yau.Blueprint.V03Proof
