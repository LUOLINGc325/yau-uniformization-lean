import Yau.Proofs.V03InfimumRightLimit
import Yau.Proofs.V03MinimizingPenalty

/-! The original sequence limit is inside the positive-penalty limit.
No common sequence threshold or energy bound is imposed. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem localizedMinimizers_penalty_zero {d : VariationData X q} (hd : VariationSetup d)
    {F : ℕ → ℝ → ℕ → VariationDisc X} (hF : LocalizedMinimizers d F) :
    ∀ᶠ j in atTop, EpsSeqZero (fun ε ν =>
      ε * (1 + (variationEnergy d j (F j ε ν)).toReal)) := by
  filter_upwards [admissible_nonempty_eventually hd, hF] with j hNon hmin
  intro r hr
  have hμ0 := localizedInfimum_finite_of_nonempty hd hNon (ε := 0) le_rfl
  have hreal := (EReal.tendsto_toReal hμ0.2 hμ0.1).comp
    (localizedInfimum_right_tendsto_of_nonempty hd hNon)
  have hμsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (localizedInfimum d j ε).toReal < (localizedInfimum d j 0).toReal + r / 3 :=
    hreal.eventually (Iio_mem_nhds (by linarith))
  have hεsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < r / 3 :=
    mem_inf_of_left (Iio_mem_nhds (by linarith))
  filter_upwards [hmin, hμsmall, hεsmall, self_mem_nhdsWithin] with ε hmin hμsmall hεsmall hε
  have hμε := localizedInfimum_finite_of_nonempty hd hNon hε.le
  have hpen := minimizingSequence_penalty_upper hd hNon hε hmin (r := r / 3) (by linarith)
  filter_upwards [hpen] with ν hν
  have hb : ε * (variationEnergy d j (F j ε ν)).toReal ≤
      (localizedInfimum d j ε).toReal - (localizedInfimum d j 0).toReal + r / 3 := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [EReal.coe_add, EReal.coe_sub, EReal.coe_mul,
      EReal.coe_toReal hμε.2 hμε.1, EReal.coe_toReal hμ0.2 hμ0.1] using hν
  have he : 0 ≤ (variationEnergy d j (F j ε ν)).toReal := ENNReal.toReal_nonneg
  rw [abs_of_nonneg (mul_nonneg hε.le (by positivity))]
  nlinarith

end Yau.Blueprint.V03Proof
