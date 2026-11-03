import Yau.Proofs.F01ACanonicalComparison
import Yau.Proofs.F01ACoreConsequences
import Yau.Proofs.F01AOriginalAverageGrowth
import Yau.Proofs.F01AOriginalPointGrowth
import Yau.Proofs.F01AProperSupercaloric

/-! A conditional assembly at the unchanged original localized-flow type.
The analytic inputs concern one existing global tuple and its comparison
against every smooth Ricci weight. They contain neither growth clause nor
proper barrier nor an assumption of the complete localized-flow conclusion.
An actual producer of those inputs is still required for original F01. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem localizedFlow_of_core_and_smooth_comparison
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u) (h : Flow X) (U P ρ : STF X)
    (hcore : LocalizedFlowCore X h U P ρ) {η : ℝ} (hη : 0 < η)
    (hcomparison : SmoothRicciWeightComparison X u U P η)
    (hinitial : CanonicalInitialData X o) : LocalizedFlow X o h U P ρ := by
  obtain ⟨Ξ, hΞ, hRic, hΞgrowth⟩ := hinitial.2
  obtain ⟨K, hK, hcontrolled⟩ := hu.2.2.2
  have hcompare (x : Pt X) : 1 + distFrom X.metric.form o x ≤ K * u x := by
    calc
      _ = K * (K⁻¹ * (1 + distFrom X.metric.form o x)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcontrolled x).1 hK.le
  have hcanonical := canonical_rho_bound_of_smooth_comparison
    X o u U P η hcomparison Ξ hΞ hRic hΞgrowth hK hcompare
    (localizedFlowCore_potential_nonpositive hcore)
  have hρ : ∀ x t, 0 ≤ t → ρ x t = -P x t := by
    rcases hcore with ⟨_, _, _, _, _, _, _, _, _, hrho, _⟩
    exact fun x t ht => (hrho x t ht).1
  have havg := original_average_growth_of_canonical_bound
    X o u hu P ρ hη hcanonical hinitial hρ
  have hpoint := original_point_growth_of_canonical_bound
    X o u P ρ hη hcanonical hinitial hρ
  have hproper := properSupercaloric_of_smooth_comparison
    X o u hu h U P ρ hcore hη hcomparison Ξ hΞ hRic hΞgrowth
  rcases hcore with ⟨hflow, hU, hP, hrho, hupper, hpot, hzero, hUt,
    hlog, hsign, hPt⟩
  exact ⟨hflow, hU, hP, hrho, hupper, hpot, hzero, hUt, hlog, hsign,
    hPt, havg, hpoint, hproper⟩

end Yau.NodeProofs.F01Aux
