import Yau.Proofs.P06FormUniquenessIteration
import Yau.Proofs.P06ScalarUniquenessVolume

/-! Actual Bishop volume growth for bounded form heat uniqueness. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n k : ℕ} {M : ComplexManifold n}

theorem boundedFormHeat_difference_polynomial_energy
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {A : RealForm M k} {U V : ℝ → RealForm M k}
    (hU : IsBoundedFormHeat g.form A U) (hV : IsBoundedFormHeat g.form A V)
    (o : M.Carrier) (χ : ℕ → M.Carrier → ℝ)
    (hχ : MetricCutoffFamily g.form o χ) :
    ∀ T : ℝ, 0 < T → ∃ D : ℝ, 0 ≤ D ∧
      ∀ j : ℕ, 1 ≤ j → ∀ t, 0 < t → t ≤ T →
        (∫ x, χ j x ^ 2 * formNormSq g.form (U t - V t) x ∂μ) ≤
          D * (j : ℝ) ^ (2 * n) := by
  obtain ⟨c, hc, hχ⟩ := hχ
  intro T hT
  obtain ⟨B, hB, hb⟩ := boundedFormHeat_difference_bound g.form hU.2.2.1 hV.2.2.1 hT
  refine ⟨B * (2 : ℝ) ^ (2 * n) * μ.real (distBall g.form o 1), by positivity, ?_⟩
  intro j hj t ht htT
  have hcut := hχ j hj
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have heq : (∫ x in distBall g.form o (2 * j), χ j x ^ 2 *
      formNormSq g.form (U t - V t) x ∂μ) =
      ∫ x, χ j x ^ 2 * formNormSq g.form (U t - V t) x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx' : x ∉ tsupport (χ j) := fun h => hx (hcut.2.2.2.2.1 h)
    simp only [image_eq_zero_of_notMem_tsupport hx', zero_pow (by omega : 2 ≠ 0), zero_mul]
  have hnorm := norm_setIntegral_le_of_norm_le_const
    (distBall_measure_lt_top g μ hμ o (by positivity : 0 < 2 * (j : ℝ)))
    (f := fun x => χ j x ^ 2 * formNormSq g.form (U t - V t) x) (C := B) (fun x _ => by
      change ‖χ j x ^ 2 * formNormSq g.form (U t - V t) x‖ ≤ B
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (sq_nonneg _) (L03.formNormSq_nonneg _ _ _))]
      have hsq : χ j x ^ 2 ≤ 1 := by
        have hr := hcut.2.2.1 x
        nlinarith
      exact (mul_le_of_le_one_left (L03.formNormSq_nonneg _ _ _) hsq).trans (hb x t ht htT))
  rw [heq, Real.norm_eq_abs] at hnorm
  have hrad : 1 ≤ 2 * (j : ℝ) := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hvol := distBall_real_volume_polynomial g hK hRic μ hμ o hrad
  calc
    _ ≤ B * μ.real (distBall g.form o (2 * j)) := (le_abs_self _).trans hnorm
    _ ≤ B * ((2 * (j : ℝ)) ^ (2 * n) * μ.real (distBall g.form o 1)) :=
      mul_le_mul_of_nonneg_left hvol hB.le
    _ = _ := by rw [mul_pow]; ring

theorem boundedFormHeat_unique_of_nonnegativeRicci
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (U V : ℝ → RealForm M k)
    (hU : IsBoundedFormHeat g.form A U) (hV : IsBoundedFormHeat g.form A V) :
    ∀ t, 0 ≤ t → U t = V t := by
  intro t ht
  rcases eq_or_lt_of_le ht with rfl | ht
  · exact hU.2.1.1.trans hV.2.1.1.symm
  · obtain ⟨o⟩ := (inferInstance : Nonempty M.Carrier)
    obtain ⟨χ, hχ⟩ := metricCutoffFamily g o
    exact boundedFormHeat_unique_of_polynomial_energy g μ hμ hU hV o χ hχ
      (boundedFormHeat_difference_polynomial_energy g hK hRic μ hμ hU hV o χ hχ) t ht

end Yau.NodeProofs.P06Aux
