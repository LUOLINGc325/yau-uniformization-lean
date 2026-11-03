import Yau.Proofs.C02NormalDifferentialSmooth

/-! The actual connection in the transported frame, expressed in a fixed
valid target chart. Its definition never divides by the normal differential. -/

noncomputable section
open Set
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem chartChristoffelBilin_smooth (g : SmoothMetric M) (c : M.Carrier) :
    ContDiffOn ℝ ∞ (chartChristoffelBilin g.form c) (chartTarget c) := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  simp_rw [chartChristoffelBilin_apply]
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.smul_const
  apply ContDiffOn.sum
  intro a ha
  apply ContDiffOn.sum
  intro b hb
  exact ((christoffel_contDiffOn g c i a b).mul
    (contDiffOn_const (c := realCoord u a))).mul (contDiffOn_const (c := realCoord v b))

def normalConnectionInChart (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  let Q := normalParallelCoefficients g p U hU c x
  let R := normalParallelCoefficientInverse g p U hU c x
  let dQ := fderiv ℝ (normalParallelCoefficients g p U hU c) x
  let dy := fderiv ℝ (normalCoordinateMap g p U c) x
  let Γ := chartChristoffelBilin g.form c (normalCoordinateMap g p U c x)
  (ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) (ComplexVector n) R).comp
    (dQ + ((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n)
      (ComplexVector n)).flip Q).comp (Γ.comp dy))

theorem normalConnectionInChart_apply (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x u z : ComplexVector n) :
    normalConnectionInChart g p U hU c x u z =
      normalParallelCoefficientInverse g p U hU c x
        (fderiv ℝ (normalParallelCoefficients g p U hU c) x u z +
          chartChristoffelBilin g.form c (normalCoordinateMap g p U c x)
            (fderiv ℝ (normalCoordinateMap g p U c) x u)
            (normalParallelCoefficients g p U hU c x z)) := rfl

theorem normalConnectionInChart_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (c : M.Carrier) :
    ContDiffOn ℝ ∞ (normalConnectionInChart g p U hU c)
      ((normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source) := by
  letI := manifold_realSmooth M
  let O := (normalRealMap g p U) ⁻¹' (chartAt (ComplexVector n) c).source
  have hO : IsOpen O :=
    (chartAt (ComplexVector n) c).open_source.preimage (normalRealMap_smooth g p U hU).continuous
  have hQ := normalParallelCoefficients_smooth g p U hU c
  have hR := normalParallelCoefficientInverse_smooth g p U hU c
  have hy := normalCoordinateMap_smooth g p U hU c
  have hDQ : ContDiffOn ℝ ∞ (fderiv ℝ (normalParallelCoefficients g p U hU c)) O :=
    hQ.fderiv_of_isOpen hO (by simp)
  have hDy : ContDiffOn ℝ ∞ (fderiv ℝ (normalCoordinateMap g p U c)) O :=
    hy.fderiv_of_isOpen hO (by simp)
  have hΓ : ContDiffOn ℝ ∞ (fun x =>
      chartChristoffelBilin g.form c (normalCoordinateMap g p U c x)) O := by
    apply (chartChristoffelBilin_smooth g c).comp hy
    intro x hx
    have hx' : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source := hx
    exact (extChartAt (ComplexModel n) c).map_source
      (by simpa only [extChartAt_source] using hx')
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro z
  have hu : ContDiffOn ℝ ∞ (fun _ : ComplexVector n => u) O := contDiffOn_const
  have hz : ContDiffOn ℝ ∞ (fun _ : ComplexVector n => z) O := contDiffOn_const
  have hSum : ContDiffOn ℝ ∞ (fun x =>
      fderiv ℝ (normalParallelCoefficients g p U hU c) x u z +
        chartChristoffelBilin g.form c (normalCoordinateMap g p U c x)
          (fderiv ℝ (normalCoordinateMap g p U c) x u)
          (normalParallelCoefficients g p U hU c x z)) O :=
    ((hDQ.clm_apply hu).clm_apply hz).add
      ((hΓ.clm_apply (hDy.clm_apply hu)).clm_apply (hQ.clm_apply hz))
  simpa only [normalConnectionInChart_apply] using hR.clm_apply hSum

end Yau.Blueprint.C02Proof
