import Yau.Proofs.C01RicciCoercivityPropagation
import Yau.Proofs.C01MetricPowerDecay

/-! The entire original compact power-contraction clause, with CK = 1.
Every lower bound and moving frame has been constructed from the original
flow and its proved Harnack inequality. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_compact_metric_decay
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h) :
    ∀ K : Set (Pt X), IsCompact K → ∃ CK aK : ℝ, 0 < aK ∧
      ∀ t, 1 ≤ t → ∀ x ∈ K,
        HermLE (gMat (h t) x) (((CK * t ^ (-aK) : ℝ) : ℂ) • gMat X.metric.form x) := by
  intro K hK
  obtain ⟨c, hc, hbound⟩ := localizedFlow_compact_ricci_coercivity_one hflow hjoint K hK
  refine ⟨1, c, hc, ?_⟩
  intro t ht x hx
  have hcurv := localizedFlow_ricci_bound_from_one hflow hjoint x c (hbound x hx)
  simpa only [one_mul] using localizedFlow_metric_power_bound hflow x c hcurv t ht

end Yau.NodeProofs.C01Aux
