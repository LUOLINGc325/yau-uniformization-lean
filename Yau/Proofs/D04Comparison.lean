import Yau.Proofs.D04L1Bounds

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

/-- A psh representative is bounded pointwise by any USC function that
bounds it almost everywhere. The right function need not be psh in these
coordinates, which is essential when comparing different atlas charts. -/
theorem psh_le_usc_of_ae_le
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {p q : ComplexVector n → EReal} (hp : IsPshOn p O) (hq : UpperSemicontinuousOn q O)
    (hae : ∀ᵐ y ∂volume.restrict O, p y ≤ q y) :
    ∀ x ∈ O, p x ≤ q x := by
  intro x hx
  by_contra hnot
  have hlt : q x < p x := lt_of_not_ge hnot
  obtain ⟨b, hqb, hbp⟩ := EReal.exists_between_coe_real hlt
  obtain ⟨a, hqa, hab⟩ := EReal.exists_between_coe_real hqb
  have habreal : a < b := EReal.coe_lt_coe_iff.mp hab
  have hqnear : ∀ᶠ y in 𝓝 x, q y < (a : EReal) := by
    have h := hq x hx (a : EReal) hqa
    simpa only [hO.nhdsWithin_eq hx] using h
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ O ∧ q y < (a : EReal) :=
    Filter.Eventually.and (hO.mem_nhds hx) hqnear
  obtain ⟨r, hr, hrball⟩ := Metric.mem_nhds_iff.mp hnear
  let K : Set (ComplexVector n) := Metric.closedBall x (r / 2)
  have hK : IsCompact K := isCompact_closedBall x (r / 2)
  have hKO : K ⊆ O := fun y hy =>
    (hrball ((Metric.closedBall_subset_ball (half_lt_self hr)) hy)).1
  have hqbound (y : ComplexVector n) (hy : y ∈ K) : q y ≤ (a : EReal) :=
    (hrball ((Metric.closedBall_subset_ball (half_lt_self hr)) hy)).2.le
  obtain ⟨hfinite, hi⟩ := finiteL1_on_closedBall_of_anchor hp (half_pos hr).le hKO hbp.le
  have hmean := closedBall_submean hp (half_pos hr).le hKO hbp.le
  have hupper : (∫ y in K, (p y).toReal) ≤ ∫ _ in K, a := by
    apply integral_mono_ae hi (integrableOn_const hK.measure_lt_top.ne)
    filter_upwards [hfinite, ae_restrict_of_ae_restrict_of_subset hKO hae,
      ae_restrict_mem hK.measurableSet] with y hy hpy hyK
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_toReal hy.2 hy.1]
    exact hpy.trans (hqbound y hyK)
  rw [setIntegral_const, smul_eq_mul] at hupper
  have hmass : 0 < volume.real K := ENNReal.toReal_pos
    (Metric.measure_closedBall_pos volume x (half_pos hr)).ne' hK.measure_lt_top.ne
  change b * volume.real K ≤ ∫ y in K, (p y).toReal at hmean
  nlinarith

theorem psh_eq_of_ae_eq
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {p q : ComplexVector n → EReal} (hp : IsPshOn p O) (hq : IsPshOn q O)
    (hae : p =ᵐ[volume.restrict O] q) : Set.EqOn p q O := by
  intro x hx
  exact le_antisymm
    (psh_le_usc_of_ae_le hO hp hq.2.1 (hae.mono fun _ h => h.le) x hx)
    (psh_le_usc_of_ae_le hO hq hp.2.1 (hae.mono fun _ h => h.ge) x hx)

end Yau.Proofs.D04Aux
