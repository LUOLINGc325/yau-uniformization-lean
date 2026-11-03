import Yau.Proofs.V03RawCompetitor
import Yau.Proofs.V03FixedDiscCost
import Yau.Proofs.V03LocalizationNonempty

/-! The original unpenalized EReal infima tend to zero. Raw comparison
discs are selected from the actual liminf envelope and acquire the original
admissibility conditions for sufficiently large indices. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem exists_fixed_comparison_eventually {d : VariationData X q} (hd : VariationSetup d)
    {η : ℝ} (hη : 0 < η) :
    ∃ F : VariationDisc X, ∀ᶠ j in atTop, AdmissibleVariationDisc d j F ∧
      penalizedFunctional d j 0 F < η := by
  obtain ⟨F, hf, hw, hw0, hs, hsT, hc, ht, havg⟩ :=
    contact_raw_almost_minimizer hd (half_pos hη)
  have hc' : InCotangentTimeChart d.chart (F.f 0) F.s (centerCylinder d) :=
    ⟨hc.1, interior_subset hc.2⟩
  refine ⟨F, ?_⟩
  filter_upwards [fixedDisc_admissible_eventually hd F hf hw hw0 hs hsT hc' ht,
    fixedDisc_cutoff_plateaus hd hf, fixedDisc_baseCost_small hd F hf hw hs ht (half_pos hη)]
    with j ha hplateau hsmall
  refine ⟨ha, ?_⟩
  have hwall : circleAverage (fun θ => wallCost d j (F.f (circlePoint θ))
      (discTime F (circlePoint θ)) F.s) ≤ η / 2 := by
    apply circleAverage_le_of_le (admissible_wallTrace_contDiff hd ha).continuous
    intro θ
    obtain ⟨hb, hfi⟩ := hplateau _ (circlePoint_mem_closedBall θ)
    simpa only [wallCost, wallBase, wallFiber, hb, hfi, inv_one, sub_self,
      add_zero, mul_zero] using hsmall _ (circlePoint_mem_closedBall θ)
  have hsplit := admissible_boundaryCost_split hd ha
  unfold penalizedFunctional
  rw [zero_mul, add_zero, hsplit]
  linarith

theorem localizedInfimum_zero_tendsto {d : VariationData X q} (hd : VariationSetup d) :
    Tendsto (fun j => localizedInfimum d j 0) atTop (𝓝 0) := by
  have hreal : Tendsto (fun j => (localizedInfimum d j 0).toReal) atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    obtain ⟨F, hF⟩ := exists_fixed_comparison_eventually hd hη
    filter_upwards [hF, localizedInfimum_finite_eventually hd] with j hj hfinite
    have hfin := hfinite.2 0 le_rfl
    have hlo : 0 ≤ (localizedInfimum d j 0).toReal := by
      have hh := EReal.toReal_le_toReal (localizedInfimum_nonneg hd j (ε := 0) le_rfl)
        (EReal.coe_ne_bot 0) hfin.2
      simpa only [EReal.toReal_coe, EReal.toReal_zero] using hh
    have hup : (localizedInfimum d j 0).toReal ≤ penalizedFunctional d j 0 F := by
      have hh := EReal.toReal_le_toReal (localizedInfimum_le 0 hj.1) hfin.1 (EReal.coe_ne_top _)
      simpa only [EReal.toReal_coe] using hh
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
    exact hup.trans_lt hj.2
  have ht := EReal.tendsto_coe.mpr hreal
  simp only [EReal.coe_zero] at ht
  apply ht.congr'
  filter_upwards [localizedInfimum_finite_eventually hd] with j hj
  exact EReal.coe_toReal (hj.2 0 le_rfl).2 (hj.2 0 le_rfl).1

end Yau.Blueprint.V03Proof
