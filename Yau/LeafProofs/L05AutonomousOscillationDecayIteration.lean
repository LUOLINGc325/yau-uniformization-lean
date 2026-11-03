import Yau.LeafProofs.L05AutonomousOscillationDecayEnergy

noncomputable section
open Set
open scoped BigOperators
set_option maxHeartbeats 2400000
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Iterate the literal contraction on the actual good-set extrema, at the actual 1/8 radii. -/
theorem auto_jet_osc_geometric {n m : ℕ} {S : Set (Point n)} {B theta : ℝ}
    (w : Fin m → Point n → ℝ) (hb : ∀ j, ∀ p ∈ S, |w j p| ≤ B)
    (c : Space n) {R : ℝ} (T : ℝ) (hR : 0 < R) (ht : 0 ≤ theta)
    (hne : ∀ r, 0 < r → r ≤ R → (S ∩ autoClosed c r T).Nonempty)
    (hstep : ∀ r, 0 < r → r ≤ R →
      autoJetOsc S w c (r/8) T ≤ theta*autoJetOsc S w c r T) :
    ∀ j : ℕ, autoJetOsc S w c (autoJetRadius R j) T ≤ theta^j*(2*(m : ℝ)*B) := by
  intro j
  induction j with
  | zero =>
    simpa only [autoJetRadius, pow_zero, mul_one, one_mul] using
      auto_jet_osc_budget w hb c R T (hne R hR le_rfl)
  | succ j ih =>
    calc
      _ = autoJetOsc S w c (autoJetRadius R j/8) T := by rw [autoJetRadius_succ]
      _ ≤ theta*autoJetOsc S w c (autoJetRadius R j) T :=
        hstep _ (autoJetRadius_pos hR j) (autoJetRadius_le hR.le j)
      _ ≤ theta*(theta^j*(2*(m : ℝ)*B)) := mul_le_mul_of_nonneg_left ih ht
      _ = _ := by rw [pow_succ]; ring

/-- Intermediate radii use monotonicity of the actual suprema and actual infima. -/
theorem auto_jet_osc_decay {n m : ℕ} {S : Set (Point n)} {B theta eta : ℝ}
    (w : Fin m → Point n → ℝ) (hb : ∀ j, ∀ p ∈ S, |w j p| ≤ B)
    (hB : 0 ≤ B) (c : Space n) {R : ℝ} (T : ℝ) (hR : 0 < R)
    (ht : 0 ≤ theta) (he : 0 ≤ eta) (hslow : theta ≤ (1/8 : ℝ)^eta)
    (hne : ∀ r, 0 < r → r ≤ R → (S ∩ autoClosed c r T).Nonempty)
    (hstep : ∀ r, 0 < r → r ≤ R →
      autoJetOsc S w c (r/8) T ≤ theta*autoJetOsc S w c r T)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    autoJetOsc S w c r T ≤ (8 : ℝ)^eta*(r/R)^eta*(2*(m : ℝ)*B) := by
  obtain ⟨j,hjLow,hjHigh⟩ := autoJetRadius_cover hR hr hrR
  calc
    _ ≤ autoJetOsc S w c (autoJetRadius R j) T :=
      auto_jet_osc_mono w hb c T hr.le hjLow (hne r hr hrR)
    _ ≤ theta^j*(2*(m : ℝ)*B) := auto_jet_osc_geometric w hb c T hR ht hne hstep j
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (auto_jet_power_bound ht he hslow hR hr.le hjHigh) (by positivity)

end Yau.LeafProofs.L05AutonomousAux
