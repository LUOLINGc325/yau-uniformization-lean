import Yau.Proofs.Y03MetricSmooth

/-! The finite left-time limit turns the strip maximum principle into monotonicity. -/

open scoped Topology
open Filter Set

noncomputable section

namespace Yau.Proofs.C07Aux

theorem monotoneOn_of_interval_maximum {N : ℝ → ℝ}
    (hcont : ContinuousWithinAt N (Ici 0) 0)
    (hmin : ∀ t, 0 < t → N 0 ≤ N t)
    (hstrip : ∀ {a b t : ℝ}, 0 < a → a ≤ t → t ≤ b →
      N t ≤ max (N a) (N b)) : MonotoneOn N (Ioi 0) := by
  intro t ht u hu htu
  by_contra hbad
  have hbad' : N u < N t := lt_of_not_ge hbad
  have hnear : ∀ᶠ a in 𝓝[Ici 0] 0, N a < N t :=
    hcont.eventually (Iio_mem_nhds ((hmin u hu).trans_lt hbad'))
  have hnear' : ∀ᶠ a in 𝓝[Ioi 0] 0, N a < N t :=
    hnear.filter_mono (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hlt : ∀ᶠ a in 𝓝[Ioi 0] 0, a < t :=
    (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
  obtain ⟨a, hNa, hat, ha⟩ := (hnear'.and (hlt.and self_mem_nhdsWithin)).exists
  exact (not_lt_of_ge (hstrip ha hat.le htu)) (max_lt hNa hbad')

end Yau.Proofs.C07Aux
