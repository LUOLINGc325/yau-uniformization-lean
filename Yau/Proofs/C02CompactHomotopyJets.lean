import Yau.Proofs.C02CompactJets
import Yau.Proofs.C02RadialJetEstimate

noncomputable section
open Set
open scoped ContDiff
universe u
namespace Yau.Blueprint.C02Proof
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem compactJetNorm_radialHomotopy_le (T : E → E →L[ℝ] F) (hT : ContDiff ℝ ∞ T)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) :
    compactJetNorm (radialHomotopy (E := E) (F := F) T) (radialHomotopy_smooth (E := E) (F := F) T hT) (k + 1) ρ ≤
      ρ / ((k : ℝ) + 3) * compactJetNorm T hT (k + 1) ρ +
      ((k : ℝ) + 1) / ((k : ℝ) + 2) * compactJetNorm T hT k ρ := by
  have ht := compactJetNorm_nonneg T hT (k + 1) ρ
  have hl := compactJetNorm_nonneg T hT k ρ
  apply compactJetNorm_le _ _ _ _ _ (by positivity)
  intro x hx
  have hx' : ‖x‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  apply norm_iteratedFDeriv_radialHomotopy_le T hT k x ρ _ _ hx' ht hl
  · intro t ht
    apply norm_iteratedFDeriv_le_compactJetNorm T hT
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans hx'
  · intro t ht
    apply norm_iteratedFDeriv_le_compactJetNorm T hT
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans hx'

end Yau.Blueprint.C02Proof
