import Yau.Proofs.C02ConnectionCoefficients
import Yau.Proofs.C02ParallelChartChange
import Yau.Proofs.C02GaugeProductDerivative

/-! The connection of the actual radial frame is independent of the auxiliary
target chart. The second derivatives of a chart change cancel by the genuine
Levi--Civita transformation rule. -/

noncomputable section
open Set Filter
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalConnectionInChart_reconstruct (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x u z : ComplexVector n)
    (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    normalParallelCoefficients g p U hU c x (normalConnectionInChart g p U hU c x u z) =
      fderiv ℝ (normalParallelCoefficients g p U hU c) x u z +
        chartChristoffelBilin g.form c (normalCoordinateMap g p U c x)
          (fderiv ℝ (normalCoordinateMap g p U c) x u)
          (normalParallelCoefficients g p U hU c x z) := by
  rw [normalConnectionInChart_apply]
  have hRight := (normalParallelCoefficient_inverse_identities g p U hU c x hx).1
  exact congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L
    (fderiv ℝ (normalParallelCoefficients g p U hU c) x u z +
      chartChristoffelBilin g.form c (normalCoordinateMap g p U c x)
        (fderiv ℝ (normalCoordinateMap g p U c) x u)
        (normalParallelCoefficients g p U hU c x z))) hRight

theorem normalConnectionInChart_chartChange (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (a b : M.Carrier) (x : ComplexVector n)
    (ha : normalRealMap g p U x ∈ (chartAt (ComplexVector n) a).source)
    (hb : normalRealMap g p U x ∈ (chartAt (ComplexVector n) b).source) :
    normalConnectionInChart g p U hU a x = normalConnectionInChart g p U hU b x := by
  letI := manifold_realSmooth M
  let ya := normalCoordinateMap g p U a
  let yb := normalCoordinateMap g p U b
  let Qa := normalParallelCoefficients g p U hU a
  let Qb := normalParallelCoefficients g p U hU b
  let ψ := realChartChange a b
  let J := fderiv ℝ ψ (ya x)
  have hf := (normalRealMap_smooth g p U hU).continuous
  have hna := hf.continuousAt.preimage_mem_nhds ((chartAt (ComplexVector n) a).open_source.mem_nhds ha)
  have hnb := hf.continuousAt.preimage_mem_nhds ((chartAt (ComplexVector n) b).open_source.mem_nhds hb)
  have ha' : normalRealMap g p U x ∈ (extChartAt (ComplexModel n) a).source := by
    simpa only [extChartAt_source] using ha
  have hz : ya x ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source ha'
  have hinv : chartInv a (ya x) = normalRealMap g p U x :=
    (extChartAt (ComplexModel n) a).left_inv ha'
  have hb' : chartInv a (ya x) ∈ (extChartAt (ComplexModel n) b).source := by
    rw [hinv]
    simpa only [extChartAt_source] using hb
  have hψ := realChartChange_contDiffAt a b hz hb'
  have hy : DifferentiableAt ℝ ya x :=
    ((normalCoordinateMap_smooth g p U hU a).contDiffAt hna).differentiableAt (by simp)
  have hQa : DifferentiableAt ℝ Qa x :=
    ((normalParallelCoefficients_smooth g p U hU a).contDiffAt hna).differentiableAt (by simp)
  have heqy : yb =ᶠ[𝓝 x] (fun v => ψ (ya v)) := by
    filter_upwards [hna] with v hv
    exact (normalCoordinateMap_chartChange g p U a b v hv).symm
  have heqQ : Qb =ᶠ[𝓝 x] (fun v => (fderiv ℝ ψ (ya v)).comp (Qa v)) := by
    filter_upwards [hna, hnb] with v hva hvb
    exact (normalParallelCoefficients_chartChange g p U hU a b v hva hvb).symm
  have hdyProd : HasFDerivAt (fun v => ψ (ya v)) (J.comp (fderiv ℝ ya x)) x :=
    (hψ.differentiableAt (by simp)).hasFDerivAt.comp x hy.hasFDerivAt
  have hdy : fderiv ℝ yb x = J.comp (fderiv ℝ ya x) := heqy.fderiv_eq.trans hdyProd.fderiv
  have hQchange : J.comp (Qa x) = Qb x := normalParallelCoefficients_chartChange g p U hU a b x ha hb
  have hDψ : ContDiffAt ℝ ∞ (fderiv ℝ ψ) (ya x) := hψ.fderiv_right (by simp)
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro z
  have hDQ := transformed_frame_fderiv hy
    (hDψ.differentiableAt (by simp)) hQa heqQ u z
  have hΓ := chartChristoffelBilin_change g a b hz hb' (fderiv ℝ ya x u) (Qa x z)
  have hQz : J (Qa x z) = Qb x z := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L z) hQchange
  have hdyu : J (fderiv ℝ ya x u) = fderiv ℝ yb x u :=
    (congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L u) hdy).symm
  change J (chartChristoffelBilin g.form a (ya x) (fderiv ℝ ya x u) (Qa x z)) =
    fderiv ℝ (fderiv ℝ ψ) (ya x) (fderiv ℝ ya x u) (Qa x z) +
      chartChristoffelBilin g.form b (ψ (ya x)) (J (fderiv ℝ ya x u)) (J (Qa x z)) at hΓ
  have hy0 : yb x = ψ (ya x) := heqy.self_of_nhds
  rw [← hy0, hQz, hdyu] at hΓ
  apply (normalParallelCoefficients_isInvertible g p U hU b x hb).bijective.injective
  calc
    Qb x (normalConnectionInChart g p U hU a x u z) =
        J (Qa x (normalConnectionInChart g p U hU a x u z)) :=
      congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n =>
        L (normalConnectionInChart g p U hU a x u z)) hQchange.symm
    _ = J (fderiv ℝ Qa x u z + chartChristoffelBilin g.form a (ya x)
        (fderiv ℝ ya x u) (Qa x z)) := by rw [normalConnectionInChart_reconstruct g p U hU a x u z ha]
    _ = J (fderiv ℝ Qa x u z) + (fderiv ℝ (fderiv ℝ ψ) (ya x)
        (fderiv ℝ ya x u) (Qa x z) + chartChristoffelBilin g.form b (yb x)
          (fderiv ℝ yb x u) (Qb x z)) := by rw [map_add, hΓ]
    _ = fderiv ℝ Qb x u z + chartChristoffelBilin g.form b (yb x)
        (fderiv ℝ yb x u) (Qb x z) := by rw [← add_assoc, ← hDQ]
    _ = Qb x (normalConnectionInChart g p U hU b x u z) :=
      (normalConnectionInChart_reconstruct g p U hU b x u z hb).symm

end Yau.Blueprint.C02Proof
