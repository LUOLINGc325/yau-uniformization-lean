import Yau.Proofs.V03ContactGap

/-! A fixed-index cost cap is chosen before every family and penalty.
The empty admissible class is handled without assigning an infimum value. -/

open Filter Set
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem fixed_index_boundary_cost_cap {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ F : ℕ → VariationDisc X, MinimizingSequence d j ε F →
        ∀ᶠ ν in atTop, boundaryCost d j (F ν) ≤ M := by
  classical
  by_cases hnon : ∃ F : VariationDisc X, AdmissibleVariationDisc d j F
  · obtain ⟨F₀, hF₀⟩ := hnon
    have hc := hd.2.2.2.2.2.2.2.1
    obtain ⟨testMax, htestMax⟩ := hc.1.bddAbove_image (contactTest_continuousOn hd)
    let K := penalizedFunctional d j 0 F₀ + (variationEnergy d j F₀).toReal
    let M := max 1 (K + 1 + testMax)
    refine ⟨M, le_max_left _ _, fun ε hε hε1 F hF => ?_⟩
    have hcomp : penalizedFunctional d j ε F₀ ≤ K := by
      have henergy : 0 ≤ (variationEnergy d j F₀).toReal := ENNReal.toReal_nonneg
      dsimp [K, penalizedFunctional]
      nlinarith
    have hμ : localizedInfimum d j ε ≤ (K : EReal) :=
      (localizedInfimum_le ε hF₀).trans (EReal.coe_le_coe_iff.mpr hcomp)
    have hsmall : localizedInfimum d j ε < ((K + 1 : ℝ) : EReal) :=
      hμ.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
    filter_upwards [hF.2.eventually (Iio_mem_nhds hsmall)] with ν hν
    have hcenter := (hF.1 ν).2.2.2.2.2.1
    have htest : d.test ((F ν).f 0) (F ν).s ≤ testMax := by
      have hh := htestMax ⟨(cotangentChart d.chart ((F ν).f 0), (F ν).s), hcenter.2, rfl⟩
      change d.test (cotangentChartInv d.chart (cotangentChart d.chart ((F ν).f 0)))
        (F ν).s ≤ testMax at hh
      rw [cotangentChart_left_inv d.chart hcenter.1] at hh
      exact hh
    have hcost : penalizedFunctional d j ε (F ν) < K + 1 := EReal.coe_lt_coe_iff.mp hν
    have hpen : 0 ≤ ε * (variationEnergy d j (F ν)).toReal :=
      mul_nonneg hε.le ENNReal.toReal_nonneg
    have hbound : boundaryCost d j (F ν) ≤ K + 1 + testMax := by
      unfold penalizedFunctional at hcost
      linarith
    exact hbound.trans (le_max_right _ _)
  · refine ⟨1, le_rfl, fun ε _ _ F hF => ?_⟩
    exact False.elim (hnon ⟨F 0, hF.1 0⟩)

end Yau.Blueprint.V04Proof
