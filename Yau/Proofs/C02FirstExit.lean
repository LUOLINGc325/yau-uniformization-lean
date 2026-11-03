import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-! A compact first-exit argument: strict improvement under a preceding
weak bound prevents the first crossing of that bound. -/

noncomputable section
open Set
namespace Yau.Blueprint.C02Proof

theorem first_exit_barrier {f : ℝ → ℝ} {b : ℝ}
    (hf : Continuous f) (h0 : f 0 < b)
    (himprove : ∀ t ∈ Icc (0 : ℝ) 1,
      (∀ s ∈ Icc (0 : ℝ) t, f s ≤ b) → f t < b) :
    ∀ t ∈ Icc (0 : ℝ) 1, f t < b := by
  intro t ht
  by_contra hbad
  let S : Set ℝ := Icc (0 : ℝ) 1 ∩ {s | b ≤ f s}
  have hS : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const hf)
  have hSne : S.Nonempty := ⟨t, ht, le_of_not_gt hbad⟩
  obtain ⟨a, ha⟩ := hS.exists_isLeast hSne
  have ha0 : 0 < a := lt_of_le_of_ne ha.1.1.1 (by
    intro he
    have hab := ha.1.2
    rw [← he] at hab
    exact (not_le_of_gt h0) hab)
  have hbefore : ∀ s ∈ Icc (0 : ℝ) a, f s ≤ b := by
    intro s hs
    by_cases he : s = a
    · subst s
      by_contra hfa
      have hnear := hf.continuousAt.eventually (isOpen_Ioi.mem_nhds (lt_of_not_ge hfa))
      obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
      let s' := a - min (δ / 2) (a / 2)
      have hm : 0 < min (δ / 2) (a / 2) := lt_min (by positivity) (by positivity)
      have hsa : s' < a := sub_lt_self _ hm
      have hs0 : 0 ≤ s' := by dsimp [s']; have := min_le_right (δ / 2) (a / 2); linarith
      have hdist : dist s' a < δ := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hsa)]
        dsimp [s']
        have := min_le_left (δ / 2) (a / 2)
        linarith
      have hbs : b < f s' := hδsub hdist
      have hmin := ha.2 ⟨⟨hs0, hsa.le.trans ha.1.1.2⟩, hbs.le⟩
      exact (not_le_of_gt hsa) hmin
    · by_contra hfs
      have hmin := ha.2 ⟨⟨hs.1, hs.2.trans ha.1.1.2⟩, (lt_of_not_ge hfs).le⟩
      exact he (le_antisymm hs.2 hmin)
  exact (not_lt_of_ge ha.1.2) (himprove a ha.1.1 hbefore)

end Yau.Blueprint.C02Proof
