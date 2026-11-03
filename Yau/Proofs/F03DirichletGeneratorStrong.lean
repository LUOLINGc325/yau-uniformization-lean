import Yau.Proofs.F03DirichletGeneratorDifference

/-! Strong initial-generator limits on every actual restricted L² input. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletComplexDifference_range_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t)
    (f : Lp ℂ 2 (μ.restrict O)) :
    ‖dirichletComplexDifference g μ hμ O t (dirichletComplexResolvent g μ hμ O f) -
      (dirichletComplexResolvent g μ hμ O - 1) (dirichletComplexResolvent g μ hμ O f)‖ ≤
        t * ‖f‖ := by
  have h := (ContinuousLinearMap.le_opNorm
    ((dirichletComplexDifference g μ hμ O t - (dirichletComplexResolvent g μ hμ O - 1)) *
      dirichletComplexResolvent g μ hμ O) f).trans
    (mul_le_mul_of_nonneg_right (dirichletComplexDifference_weighted_error g μ hμ O ht)
      (norm_nonneg f))
  simpa only [mul_apply_eq_comp, sub_apply] using h

theorem dirichletComplexDifference_tendsto_zero (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (hO : IsOpen O) (f : Lp ℂ 2 (μ.restrict O)) :
    Tendsto (fun t : ℝ => dirichletComplexDifference g μ hμ O t f) (𝓝[>] 0)
      (𝓝 ((dirichletComplexResolvent g μ hμ O - 1) f)) := by
  let B := dirichletComplexResolvent g μ hμ O
  have hBn : ‖B - 1‖ ≤ 2 := by
    have hsub := norm_sub_le B 1
    have hB := dirichletComplexResolvent_opNorm_le g μ hμ O
    have hI : ‖(1 : Lp ℂ 2 (μ.restrict O) →L[ℂ] Lp ℂ 2 (μ.restrict O))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    linarith only [hsub, hB, hI]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨v, hv⟩ := (dirichletComplexResolvent_denseRange g μ hμ O hO).exists_dist_lt f
    (show 0 < ε / 8 by positivity)
  rw [dist_eq_norm] at hv
  let δ := ε / (2 * (‖v‖ + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hevent] with t ht htδ
  have ht₀ : 0 < t := ht
  have hsmall : t * ‖v‖ < ε / 2 := by
    calc
      t * ‖v‖ ≤ t * (‖v‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) ht₀.le
      _ < δ * (‖v‖ + 1) := mul_lt_mul_of_pos_right htδ (by positivity)
      _ = ε / 2 := by dsimp [δ]; field_simp
  rw [dist_eq_norm]
  have heq : dirichletComplexDifference g μ hμ O t f - (B - 1) f =
      dirichletComplexDifference g μ hμ O t (f - B v) +
        (dirichletComplexDifference g μ hμ O t (B v) - (B - 1) (B v)) +
          (B - 1) (B v - f) := by
    simp only [map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖dirichletComplexDifference g μ hμ O t (f - B v)‖ +
        ‖dirichletComplexDifference g μ hμ O t (B v) - (B - 1) (B v)‖ +
          ‖(B - 1) (B v - f)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ‖f - B v‖ + t * ‖v‖ + 2 * ‖B v - f‖ := by
      gcongr
      · calc
          _ ≤ ‖dirichletComplexDifference g μ hμ O t‖ * ‖f - B v‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖f - B v‖ := mul_le_mul_of_nonneg_right
            (dirichletComplexDifference_opNorm_le g μ hμ O ht₀) (norm_nonneg (f - B v))
          _ = ‖f - B v‖ := one_mul _
      · exact dirichletComplexDifference_range_bound g μ hμ O ht₀ v
      · exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right hBn (norm_nonneg (B v - f)))
    _ < ε := by
      rw [norm_sub_rev (B v) f]
      change ‖f - B v‖ < ε / 8 at hv
      linarith only [hv, hsmall, hε]

end Yau.Proofs.F03Aux
