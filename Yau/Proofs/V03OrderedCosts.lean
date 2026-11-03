import Yau.Proofs.V03InfimumZero
import Yau.Proofs.V03InfimumRightLimit

/-! The actual total costs and wall averages vanish in the prescribed
sequence, then positive-penalty, then index order. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem localizedMinimizers_cost_small {d : VariationData X q} (hd : VariationSetup d)
    {F : ℕ → ℝ → ℕ → VariationDisc X} (hF : LocalizedMinimizers d F)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop,
      penalizedFunctional d j ε (F j ε ν) ≤ r := by
  have hzero := (EReal.tendsto_toReal (by simp : (0 : EReal) ≠ ⊤)
    (by simp : (0 : EReal) ≠ ⊥)).comp (localizedInfimum_zero_tendsto hd)
  have hzeroR : Tendsto (fun j => (localizedInfimum d j 0).toReal) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, EReal.toReal_zero] using hzero
  have hμ0small := hzeroR.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < r / 3))
  filter_upwards [hμ0small, admissible_nonempty_eventually hd, hF] with j hj hNon hmin
  have hμ0 := localizedInfimum_finite_of_nonempty hd hNon (ε := 0) le_rfl
  have hright := (EReal.tendsto_toReal hμ0.2 hμ0.1).comp
    (localizedInfimum_right_tendsto_of_nonempty hd hNon)
  have hμεsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (localizedInfimum d j ε).toReal < (localizedInfimum d j 0).toReal + r / 3 :=
    hright.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hμεsmall, hmin, self_mem_nhdsWithin] with ε hεμ hmin hε
  have hμε := localizedInfimum_finite_of_nonempty hd hNon hε.le
  have hseq := (EReal.tendsto_toReal hμε.2 hμε.1).comp hmin.2
  have hseqR : Tendsto (fun ν => penalizedFunctional d j ε (F j ε ν)) atTop
      (𝓝 (localizedInfimum d j ε).toReal) := by
    simpa only [Function.comp_def, EReal.toReal_coe] using hseq
  have hlate := hseqR.eventually (Iio_mem_nhds
    (by linarith : (localizedInfimum d j ε).toReal < (localizedInfimum d j ε).toReal + r / 3))
  filter_upwards [hlate] with ν hν
  linarith

theorem localizedMinimizers_wall_zero {d : VariationData X q} (hd : VariationSetup d)
    {F : ℕ → ℝ → ℕ → VariationDisc X} (hF : LocalizedMinimizers d F) :
    LocalizedZero (fun j ε ν => circleAverage (fun θ =>
      wallCost d j ((F j ε ν).f (circlePoint θ))
        (discTime (F j ε ν) (circlePoint θ)) (F j ε ν).s)) := by
  intro r hr
  filter_upwards [localizedMinimizers_cost_small hd hF hr, hF] with j hj hmin
  filter_upwards [hj, hmin, self_mem_nhdsWithin] with ε hεcost hmin hε
  filter_upwards [hεcost] with ν hν
  have ha := hmin.1 ν
  have hnonneg := admissible_wallAverage_nonneg hd ha
  have hlower := penalizedFunctional_lower_wall_energy hd ha ε
  have henergy : 0 ≤ ε * (variationEnergy d j (F j ε ν)).toReal :=
    mul_nonneg hε.le ENNReal.toReal_nonneg
  rw [abs_of_nonneg hnonneg]
  linarith

end Yau.Blueprint.V03Proof
