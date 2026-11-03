import Yau.Proofs.V03LocalizationNonempty

/-! The exact right-hand limit of the original EReal penalized infimum,
using one finite-energy competitor for each requested error. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem exists_admissible_cost_near_infimum {d : VariationData X q} {j : ℕ}
    (hfinite : localizedInfimum d j 0 ≠ ⊥ ∧ localizedInfimum d j 0 ≠ ⊤)
    {η : ℝ} (hη : 0 < η) :
    ∃ F : VariationDisc X, AdmissibleVariationDisc d j F ∧
      penalizedFunctional d j 0 F < (localizedInfimum d j 0).toReal + η := by
  have heq := EReal.coe_toReal hfinite.2 hfinite.1
  have hlt : localizedInfimum d j 0 < ((localizedInfimum d j 0).toReal + η : ℝ) := by
    calc
      localizedInfimum d j 0 = ((localizedInfimum d j 0).toReal : EReal) := heq.symm
      _ < ((localizedInfimum d j 0).toReal + η : ℝ) :=
        EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨F, hF⟩ := iInf_lt_iff.mp hlt
  obtain ⟨ha, hc⟩ := iInf_lt_iff.mp hF
  exact ⟨F, ha, EReal.coe_lt_coe_iff.mp hc⟩

theorem localizedInfimum_right_tendsto_of_nonempty {d : VariationData X q}
    (hd : VariationSetup d) {j : ℕ} (hNon : ∃ F : VariationDisc X, AdmissibleVariationDisc d j F) :
    Tendsto (localizedInfimum d j) (𝓝[>] (0 : ℝ)) (𝓝 (localizedInfimum d j 0)) := by
  have hfinite0 := localizedInfimum_finite_of_nonempty hd hNon (ε := 0) le_rfl
  have hfinite (ε : ℝ) (hε : 0 ≤ ε) := localizedInfimum_finite_of_nonempty hd hNon hε
  have hreal : Tendsto (fun ε => (localizedInfimum d j ε).toReal) (𝓝[>] (0 : ℝ))
      (𝓝 (localizedInfimum d j 0).toReal) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    obtain ⟨F, hF, hcost⟩ := exists_admissible_cost_near_infimum hfinite0 (half_pos hη)
    let e := (variationEnergy d j F).toReal
    have he : 0 ≤ e := ENNReal.toReal_nonneg
    let δ := η / (2 * (1 + e))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < δ := by
      filter_upwards [self_mem_nhdsWithin, mem_inf_of_left (Iio_mem_nhds hδ)] with ε hε hεδ
      exact ⟨hε, hεδ⟩
    filter_upwards [hsmall] with ε hε
    have hμ := hfinite ε hε.1.le
    have hlo : (localizedInfimum d j 0).toReal ≤ (localizedInfimum d j ε).toReal :=
      EReal.toReal_le_toReal (localizedInfimum_mono d j hε.1.le) hfinite0.1 hμ.2
    have hup : (localizedInfimum d j ε).toReal ≤ penalizedFunctional d j ε F := by
      have hh := EReal.toReal_le_toReal (localizedInfimum_le ε hF) hμ.1 (EReal.coe_ne_top _)
      simpa only [EReal.toReal_coe] using hh
    have hpen : ε * e < η / 2 := by
      calc
        ε * e ≤ ε * (1 + e) := mul_le_mul_of_nonneg_left (by linarith) hε.1.le
        _ < δ * (1 + e) := mul_lt_mul_of_pos_right hε.2 (by linarith)
        _ = η / 2 := by
          have he1 : 1 + e ≠ 0 := by linarith
          dsimp [δ]
          field_simp [he1]
    have hid : penalizedFunctional d j ε F = penalizedFunctional d j 0 F + ε * e := by
      unfold penalizedFunctional
      dsimp [e]
      ring
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
    rw [hid] at hup
    linarith
  have ht := EReal.tendsto_coe.mpr hreal
  rw [EReal.coe_toReal hfinite0.2 hfinite0.1] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact EReal.coe_toReal (hfinite ε hε.le).2 (hfinite ε hε.le).1

end Yau.Blueprint.V03Proof
