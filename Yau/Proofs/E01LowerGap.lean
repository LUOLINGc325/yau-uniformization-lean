import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-! A genuine uniform real margin for lower semicontinuous extended-real data. -/

noncomputable section

namespace Yau.NodeProofs.E01Aux

theorem exists_uniform_real_gap_of_lsc
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    (v : E → EReal) (hv : LowerSemicontinuousOn v K) (a : ℝ)
    (ha : ∀ x ∈ K, (a : EReal) < v x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ((a + δ : ℝ) : EReal) ≤ v x := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hK hv
    obtain ⟨b, hab, hb⟩ := EReal.exists_between_coe_real (ha x hx)
    have hab' : a < b := EReal.coe_lt_coe_iff.mp hab
    refine ⟨b - a, sub_pos.mpr hab', fun y hy => ?_⟩
    have heq : a + (b - a) = b := by ring
    rw [heq]
    exact hb.le.trans (hmin hy)
  · refine ⟨1, zero_lt_one, fun x hx => ?_⟩
    exact (hne ⟨x, hx⟩).elim

end Yau.NodeProofs.E01Aux
