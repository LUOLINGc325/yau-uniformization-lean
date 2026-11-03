import Yau.Blueprint.Nodes

/-! Spatial smoothness at each actual nonnegative flow time. -/

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamily_metricSmooth {h : ℝ → HermitianField M} {I : Set ℝ}
    (hh : MetricFamilySmooth h I) {t : ℝ} (ht : t ∈ I) : MetricSmooth (h t) := by
  intro x a b
  let q : ComplexVector n → ComplexVector n × ℝ := fun z => (z, t)
  have hq : ContDiffOn ℝ ∞ q (chartTarget x) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hmap : Set.MapsTo q (chartTarget x) (chartTarget x ×ˢ I) :=
    fun z hz => ⟨hz, ht⟩
  simpa only [q, Function.comp_def] using (hh x a b).comp (f := q) hq hmap

theorem flow_metricSmooth {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X} (hflow : FlowStage X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) : MetricSmooth (h t) :=
  metricFamily_metricSmooth hflow.1.1.2.1 ht

end Yau.Proofs.C07Aux
