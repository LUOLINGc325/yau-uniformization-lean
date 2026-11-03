import Yau.Proofs.V03LocalizationNonempty

/-! The minimizing-sequence penalty estimate in the original EReal form.
Finiteness is derived from actual nonempty admissible competitors. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem minimizingSequence_penalty_upper {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} (hNon : ∃ F : VariationDisc X, AdmissibleVariationDisc d j F)
    {ε : ℝ} (hε : 0 < ε) {F : ℕ → VariationDisc X} (hF : MinimizingSequence d j ε F)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ ν in atTop, (ε * (variationEnergy d j (F ν)).toReal : EReal) ≤
      localizedInfimum d j ε - localizedInfimum d j 0 + (r : EReal) := by
  have hμ0 := localizedInfimum_finite_of_nonempty hd hNon (ε := 0) le_rfl
  have hμε := localizedInfimum_finite_of_nonempty hd hNon hε.le
  have ht := (EReal.tendsto_toReal hμε.2 hμε.1).comp hF.2
  have hreal : Tendsto (fun ν => penalizedFunctional d j ε (F ν)) atTop
      (𝓝 (localizedInfimum d j ε).toReal) := by
    simpa only [Function.comp_def, EReal.toReal_coe] using ht
  have hbound : ∀ᶠ ν in atTop,
      penalizedFunctional d j ε (F ν) < (localizedInfimum d j ε).toReal + r :=
    hreal.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hbound] with ν hν
  have hlower : (localizedInfimum d j 0).toReal ≤ penalizedFunctional d j 0 (F ν) := by
    have hh := EReal.toReal_le_toReal (localizedInfimum_le 0 (hF.1 ν)) hμ0.1 (EReal.coe_ne_top _)
    simpa only [EReal.toReal_coe] using hh
  have hid := penalizedFunctional_sub d j 0 ε (F ν)
  have hp : ε * (variationEnergy d j (F ν)).toReal ≤
      (localizedInfimum d j ε).toReal - (localizedInfimum d j 0).toReal + r := by
    simp only [sub_zero] at hid
    linarith
  have he := EReal.coe_le_coe_iff.mpr hp
  simpa only [EReal.coe_add, EReal.coe_sub, EReal.coe_mul, EReal.coe_toReal hμε.2 hμε.1,
    EReal.coe_toReal hμ0.2 hμ0.1] using he

end Yau.Blueprint.V03Proof
