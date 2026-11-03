import Yau.Proofs.V03OrderedCosts
import Yau.Proofs.V03ContactGap

/-! Strict contact and the actual total-cost bounds localize centers and
bound their averaged cotangent norm in the original order of limits. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem localizedMinimizers_centers_zero {d : VariationData X q} (hd : VariationSetup d)
    {F : ℕ → ℝ → ℕ → VariationDisc X} (hF : LocalizedMinimizers d F) :
    LocalizedZero (fun j ε ν =>
      ‖(cotangentChart d.chart ((F j ε ν).f 0), (F j ε ν).s) - d.contact‖) := by
  intro r hr
  obtain ⟨γ, hγ, hgap⟩ := contactGap_uniform_pos_away hd hr
  filter_upwards [localizedMinimizers_cost_small hd hF (half_pos hγ), hF] with j hj hmin
  filter_upwards [hj, hmin, self_mem_nhdsWithin] with ε hεcost hmin hε
  filter_upwards [hεcost] with ν hν
  have ha := hmin.1 ν
  rw [abs_of_nonneg (norm_nonneg _)]
  apply le_of_lt
  by_contra hn
  have hcenter := ha.2.2.2.2.2.1.2
  have hγbound := hgap _ hcenter (le_of_not_gt hn)
  have hcost := contactGap_le_penalizedFunctional hd ha hε.le
  have hreal : γ ≤ penalizedFunctional d j ε (F j ε ν) :=
    EReal.coe_le_coe_iff.mp (hγbound.trans hcost)
  linarith

theorem localizedMinimizers_norm_average_bounded {d : VariationData X q} (hd : VariationSetup d)
    {F : ℕ → ℝ → ℕ → VariationDisc X} (hF : LocalizedMinimizers d F) :
    ∃ C : ℝ, ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop,
      circleAverage (fun θ => let y := (F j ε ν).f (circlePoint θ)
        dualNorm (d.h (discTime (F j ε ν) (circlePoint θ))) y.1 y.2) ≤ C := by
  obtain ⟨M, hM⟩ := hd.2.2.2.2.2.2.2.1.1.bddAbove_image (contactTest_continuousOn hd)
  refine ⟨1 + M, ?_⟩
  filter_upwards [localizedMinimizers_cost_small hd hF zero_lt_one, hF] with j hj hmin
  filter_upwards [hj, hmin, self_mem_nhdsWithin] with ε hεcost hmin hε
  filter_upwards [hεcost] with ν hν
  have ha := hmin.1 ν
  have hc := ha.2.2.2.2.2.1
  have htest : d.test ((F j ε ν).f 0) (F j ε ν).s ≤ M := by
    have hh := hM ⟨(cotangentChart d.chart ((F j ε ν).f 0), (F j ε ν).s), hc.2, rfl⟩
    simpa only [contactTest, cotangentChart_left_inv d.chart hc.1] using hh
  have hw := admissible_wallAverage_nonneg hd ha
  have he : 0 ≤ ε * (variationEnergy d j (F j ε ν)).toReal :=
    mul_nonneg hε.le ENNReal.toReal_nonneg
  unfold penalizedFunctional at hν
  rw [admissible_boundaryCost_split hd ha] at hν
  linarith

end Yau.Blueprint.V03Proof
