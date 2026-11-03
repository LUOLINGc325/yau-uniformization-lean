import Yau.Proofs.F03DirichletGeneratorStrong

/-! Both directions of the initial generator criterion for the actual supported heat. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletComplexHeat_resolvent_commute (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    {t : ℝ} (ht : 0 < t) :
    dirichletComplexHeat g μ hμ O t * dirichletComplexResolvent g μ hμ O =
      dirichletComplexResolvent g μ hμ O * dirichletComplexHeat g μ hμ O t := by
  rw [dirichletComplexHeat_of_pos g μ hμ O ht]
  exact ((Commute.refl (dirichletComplexResolvent g μ hμ O)).cfc_real
    (scalarHeatMultiplier t)).eq

theorem dirichletComplexDifference_apply (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t)
    (f : Lp ℂ 2 (μ.restrict O)) :
    dirichletComplexDifference g μ hμ O t f = t⁻¹ •
      (dirichletComplexHeat g μ hμ O t (dirichletComplexResolvent g μ hμ O f) -
        dirichletComplexResolvent g μ hμ O f) := by
  rw [dirichletComplexDifference_eq g μ hμ O ht]
  rfl

theorem dirichletComplexDifference_reverse (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {t : ℝ} (ht : 0 < t)
    (f : Lp ℂ 2 (μ.restrict O)) :
    dirichletComplexResolvent g μ hμ O
      (t⁻¹ • (dirichletComplexHeat g μ hμ O t f - f)) =
        dirichletComplexDifference g μ hμ O t f := by
  let B := dirichletComplexResolvent g μ hμ O
  have hsmul := (B.restrictScalars ℝ).map_smul t⁻¹ (dirichletComplexHeat g μ hμ O t f - f)
  change B (t⁻¹ • (dirichletComplexHeat g μ hμ O t f - f)) =
    t⁻¹ • B (dirichletComplexHeat g μ hμ O t f - f) at hsmul
  rw [hsmul, map_sub, dirichletComplexDifference_apply g μ hμ O ht]
  have hc := congrArg (fun A : Lp ℂ 2 (μ.restrict O) →L[ℂ] Lp ℂ 2 (μ.restrict O) => A f)
    (dirichletComplexHeat_resolvent_commute g μ hμ O ht)
  change dirichletComplexHeat g μ hμ O t (B f) = B (dirichletComplexHeat g μ hμ O t f) at hc
  rw [← hc]

theorem dirichletComplex_generator_iff (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (f w : Lp ℂ 2 (μ.restrict O)) :
    f = dirichletComplexResolvent g μ hμ O (f + w) ↔
      Tendsto (fun t : ℝ => t⁻¹ • (dirichletComplexHeat g μ hμ O t f - f) + w)
        (𝓝[>] 0) (𝓝 0) := by
  let B := dirichletComplexResolvent g μ hμ O
  constructor
  · intro hf
    have hl := (dirichletComplexDifference_tendsto_zero g μ hμ O hO (f + w)).add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => w) (𝓝[>] 0) (𝓝 w))
    have hzero : (B - 1) (f + w) + w = 0 := by
      simp only [sub_apply, one_apply_eq_self]
      rw [← hf]
      abel
    change Tendsto (fun t => dirichletComplexDifference g μ hμ O t (f + w) + w)
      (𝓝[>] 0) (𝓝 ((B - 1) (f + w) + w)) at hl
    rw [hzero] at hl
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [dirichletComplexDifference_apply g μ hμ O (show 0 < t from ht), ← hf]
  · intro hlim
    have hBlim := (B.continuous.tendsto 0).comp hlim
    simp only [map_zero] at hBlim
    have hBlim' : Tendsto (fun t => dirichletComplexDifference g μ hμ O t f + B w)
        (𝓝[>] 0) (𝓝 0) := by
      apply hBlim.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Function.comp_def, map_add]
      rw [dirichletComplexDifference_reverse g μ hμ O (show 0 < t from ht)]
    have hl := (dirichletComplexDifference_tendsto_zero g μ hμ O hO f).add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => B w) (𝓝[>] 0) (𝓝 (B w)))
    have heq : (B - 1) f + B w = 0 := tendsto_nhds_unique hl hBlim'
    have hsub : B (f + w) - f = 0 := by
      rw [map_add]
      calc
        B f + B w - f = (B - 1) f + B w := by
          simp only [sub_apply, one_apply_eq_self]
          abel
        _ = 0 := heq
    exact (sub_eq_zero.mp hsub).symm

end Yau.Proofs.F03Aux
