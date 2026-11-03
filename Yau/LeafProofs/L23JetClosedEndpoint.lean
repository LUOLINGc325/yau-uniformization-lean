import Yau.LeafProofs.L23JetClosedContinuity

/-! Uniform interior-time bounds pass to the original closed upper face. -/

noncomputable section
open Filter
open scoped Topology
namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {n : ℕ} {M : ComplexManifold n}

theorem jetSq_time_continuousOn_closed (h : ℝ → HermitianField M) (a b : ℝ)
    (hab : a < b) (hh : MetricFamilySmooth h (Set.Icc a b)) (k : ℕ) (q : M.Carrier) :
    ContinuousOn (fun t => jetSq (h t) k q) (Set.Icc a b) := by
  exact (jetSq_continuousOn_closed h a b hab hh k).comp (f := fun t : ℝ => (q,t))
    (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨Set.mem_univ q,ht⟩)

theorem jetSq_bound_at_closed_right (h : ℝ → HermitianField M) (a b c C : ℝ)
    (hac : a ≤ c) (hcb : c < b) (hh : MetricFamilySmooth h (Set.Icc a b))
    (k : ℕ) (q : M.Carrier)
    (hbound : ∀ t ∈ Set.Ioo c b, jetSq (h t) k q≤C) : jetSq (h b) k q≤C := by
  have hsub : Set.Ioo c b ⊆ Set.Icc a b :=
    fun t ht => ⟨hac.trans ht.1.le,ht.2.le⟩
  have hc : ContinuousWithinAt (fun t => jetSq (h t) k q) (Set.Icc a b) b :=
    (jetSq_time_continuousOn_closed h a b (hac.trans_lt hcb) hh k q) b
      ⟨(hac.trans_lt hcb).le,le_rfl⟩
  letI : NeBot (𝓝[Set.Ioo c b] b) := right_nhdsWithin_Ioo_neBot hcb
  exact le_of_tendsto (hc.mono hsub)
    (Filter.mem_of_superset self_mem_nhdsWithin (fun t ht => hbound t ht))

end Yau.LeafProofs.L23Aux
