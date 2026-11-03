import Yau.Proofs.F04ClosedTimeDerivative
import Yau.Proofs.F04AdjointLocal

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem chart_spatial_derivativeWithin_Icc {S : ℝ} (_hS : 0 < S)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v (Icc 0 S))
    (c : M.Carrier) {p : ComplexVector n × ℝ} (hp : p ∈ chartTarget c ×ˢ Icc 0 S)
    (i : RIdx n) :
    rDeriv (inChart c (fun x => v x p.2)) p.1 i =
      fderivWithin ℝ (fun q : ComplexVector n × ℝ => v (chartInv c q.1) q.2)
        (chartTarget c ×ˢ Icc 0 S) p (realVec i, 0) := by
  have hF := ((hv c).differentiableOn (by simp) p hp).hasFDerivWithinAt
  have hmap : HasFDerivAt (fun z : ComplexVector n => (z, p.2))
      ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod (0 : ComplexVector n →L[ℝ] ℝ)) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have hmaps : MapsTo (fun z : ComplexVector n => (z, p.2)) (chartTarget c)
      (chartTarget c ×ˢ Icc 0 S) := fun _ hz => ⟨hz, hp.2⟩
  have hd := (hF.comp p.1 hmap.hasFDerivWithinAt hmaps).hasFDerivAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hp.1)
  have he := congrArg (fun L => L (realVec i)) hd.fderiv
  change fderiv ℝ (fun z => v (chartInv c z) p.2) p.1 (realVec i) = _
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply] using he

theorem chart_spatial_derivative_continuousOn {S : ℝ} (hS : 0 < S)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v (Icc 0 S))
    (c : M.Carrier) (i : RIdx n) :
    ContinuousOn (fun p : ComplexVector n × ℝ =>
      rDeriv (inChart c (fun x => v x p.2)) p.1 i) (chartTarget c ×ˢ Icc 0 S) := by
  have huniq := (isOpen_extChartAt_target (I := ComplexModel n) c).uniqueDiffOn.prod
    (uniqueDiffOn_Icc hS)
  have hF := (hv c).continuousOn_fderivWithin huniq (by simp)
  apply (hF.clm_apply continuousOn_const).congr
  intro p hp
  exact chart_spatial_derivativeWithin_Icc hS hv c hp i

/-- The actual scalar gradient pairing of two smooth physical profiles is
jointly continuous up to both time faces, with the original fixed metric. -/
theorem smoothSpaceTime_gradientPair_continuousOn
    (g : HermitianField M) (hg : MetricSmooth g) {S : ℝ} (hS : 0 < S)
    {u v : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Icc 0 S))
    (hv : SmoothSpaceTime v (Icc 0 S)) :
    ContinuousOn (fun p : M.Carrier × ℝ =>
      scalarGradientPair g (fun x => u x p.2) (fun x => v x p.2) p.1) (univ ×ˢ Icc 0 S) := by
  apply chartwise_continuousOn (M := M) (I := Icc 0 S)
    (v := fun x t => scalarGradientPair g (fun y => u y t) (fun y => v y t) x)
  intro c
  have hi (i j : RIdx n) : ContinuousOn (fun p : ComplexVector n × ℝ =>
      (realMetricFn g c p.1)⁻¹ i j) (chartTarget c ×ˢ Icc 0 S) :=
    (Adjoint.realMetricFn_inverse_contDiffOn g hg c i j).continuousOn.comp
      continuousOn_fst (fun _ hp => hp.1)
  have hsum : ContinuousOn (fun p : ComplexVector n × ℝ => ∑ i, ∑ j,
      (realMetricFn g c p.1)⁻¹ i j * rDeriv (inChart c (fun x => u x p.2)) p.1 i *
        rDeriv (inChart c (fun x => v x p.2)) p.1 j) (chartTarget c ×ˢ Icc 0 S) := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact ((hi i j).mul (chart_spatial_derivative_continuousOn hS hu c i)).mul
      (chart_spatial_derivative_continuousOn hS hv c j)
  apply hsum.congr
  intro p hp
  have hus : SmoothFn (fun x => u x p.2) := fun a => (hu a).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz, hp.2⟩)
  have hvs : SmoothFn (fun x => v x p.2) := fun a => (hv a).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz, hp.2⟩)
  dsimp only
  rw [scalarGradientPair_eq_chart g hus hvs c hp.1, chartGradientPair_eq_sum]

end Yau.F04Proof
