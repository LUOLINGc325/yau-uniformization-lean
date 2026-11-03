import Yau.Proofs.C04ClockInverse

/-! The physical clock's strictness preserves all original good-window comparisons. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter Set

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

theorem clockSpeed_le_of_clock_le (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u)
    (hs : ρ o t ≤ ρ o u) : clockSpeed o h t ≤ clockSpeed o h u := by
  have htu := ((rho_strictMonoOn_nonneg X o h U P ρ hf hH).le_iff_le ht.le hu).mp hs
  exact clockSpeed_monotoneOn X o h U P ρ hf hH ht (le_refl t) htu htu

theorem late_of_clock_level (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) {A t : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t)
    (hs : ρ o A ≤ ρ o t) : A ≤ t :=
  ((rho_strictMonoOn_nonneg X o h U P ρ hf hH).le_iff_le hA ht).mp hs

end Yau.Proofs.C04Aux
