import Yau.Proofs.V04ClockRegularity
import Yau.Proofs.V04BackwardClockAlgebra
import Yau.Proofs.V03ClockRadial

/-! Actual admissible backward clocks, including finite energy and the
original center chart. The spatial disc and the chosen lift stay fixed. -/

open scoped Topology ContDiff
open Filter
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem backwardClock_energy_ne_top {d : VariationData X q} {j : ℕ}
    {F : VariationDisc X} (hF : variationEnergy d j F ≠ ⊤) {Γ : ℂ → ℂ} {s' : ℝ}
    (hw : ContDiffOn ℂ ∞ (backwardClock F Γ s').w (Metric.closedBall 0 1)) :
    variationEnergy d j (backwardClock F Γ s') ≠ ⊤ := by
  obtain ⟨hA, hB, _, hD⟩ := energy_components_ne_top hF
  have hC := clockArea_ne_top_of_closedDisc hw
  unfold variationEnergy
  simp only [ENNReal.add_ne_top]
  exact ⟨⟨⟨⟨hA, hB⟩, ENNReal.ofReal_ne_top⟩, hC⟩, hD⟩

theorem center_time_neighborhood {d : VariationData X q} {F : VariationDisc X}
    (hc : InCotangentTimeChart d.chart (F.f 0) F.s (interior (centerCylinder d))) :
    ∃ r : ℝ, 0 < r ∧ ∀ s', F.s - r < s' → s' < F.s →
      InCotangentTimeChart d.chart (F.f 0) s' (centerCylinder d) := by
  have hnear : {s' : ℝ | (cotangentChart d.chart (F.f 0), s') ∈
      interior (centerCylinder d)} ∈ 𝓝 F.s :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds hc.2)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r, hr, fun s' hlo hhi => ⟨hc.1, interior_subset (hsub ?_)⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hhi)]
  linarith

theorem backwardClockRealization_of_cutoffs {d : VariationData X q} (hd : VariationSetup d)
    {k : ClockData X} (hk : ClockCutoffs d k) (j a : ℕ) :
    BackwardClockRealization d k j a := by
  intro F hF hc
  obtain ⟨Γ, hΓ, hβ⟩ := exists_clockLift hd hk hF
  obtain ⟨r, hr, hcenter⟩ := center_time_neighborhood hc
  refine ⟨Γ, hΓ, r, hr, fun s' hs' hlo hhi => ?_⟩
  obtain ⟨hf, hw, hw0, hs, hsT, _, ht, hb, henergy⟩ := hF
  have hnew := backwardClock_smooth_center hw hw0 hΓ.1 hΓ.2.1 s'
  have htime := backwardClock_discTime_le F Γ hs hs' hhi.le hβ
  refine ⟨⟨hf, hnew.1, hnew.2, hs', hhi.trans hsT, hcenter s' hlo hhi,
    fun ζ hζ => (htime ζ hζ).trans_lt (ht ζ hζ), hb,
    backwardClock_energy_ne_top henergy hnew.1⟩, htime, ?_⟩
  exact backwardClock_boundary_time hΓ hs hs'

end Yau.Blueprint.V04Proof
