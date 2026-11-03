import Yau.Proofs.F04ChartContinuity

open Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem chart_time_derivative {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
    (hI : IsOpen I) {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceC1Time v I)
    (x : M.Carrier) {p : ComplexVector n × ℝ} (hp : p ∈ chartTarget x ×ˢ I) :
    deriv (v (chartInv x p.1)) p.2 =
      fderiv ℝ (fun q : ComplexVector n × ℝ => v (chartInv x q.1) q.2) p (0, 1) := by
  have hF := ((hv.2 x).contDiffAt
    (((isOpen_extChartAt_target (I := ComplexModel n) x).prod hI).mem_nhds hp)).differentiableAt
    (by norm_num)
  have hmap : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (hF.hasFDerivAt.comp_hasDerivAt p.2 hmap).deriv

theorem smoothSpaceC1Time_timeDerivative_continuousOn {n : ℕ} {M : ComplexManifold n}
    {I : Set ℝ} (hI : IsOpen I) {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceC1Time v I) :
    ContinuousOn (fun p : M.Carrier × ℝ => deriv (v p.1) p.2) (univ ×ˢ I) := by
  apply chartwise_continuousOn (M := M) (I := I) (v := fun x t => deriv (v x) t)
  intro x
  have hF := (hv.2 x).continuousOn_fderiv_of_isOpen
    ((isOpen_extChartAt_target (I := ComplexModel n) x).prod hI) le_rfl
  apply (hF.clm_apply continuousOn_const).congr
  intro p hp
  exact chart_time_derivative hI hv x hp

theorem smoothSpaceC1Time_hasDerivAt {n : ℕ} {M : ComplexManifold n} {I : Set ℝ}
    (hI : IsOpen I) {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceC1Time v I)
    (x : M.Carrier) {t : ℝ} (ht : t ∈ I) : HasDerivAt (v x) (deriv (v x) t) t := by
  have hp : (chartPt x x, t) ∈ chartTarget x ×ˢ I := ⟨mem_extChartAt_target x, ht⟩
  have hF := ((hv.2 x).contDiffAt
    (((isOpen_extChartAt_target (I := ComplexModel n) x).prod hI).mem_nhds hp)).differentiableAt
    (by norm_num)
  have hmap : HasDerivAt (fun s : ℝ => (chartPt x x, s)) (0, 1) t :=
    (hasDerivAt_const t (chartPt x x)).prodMk (hasDerivAt_id t)
  have hd := hF.hasFDerivAt.comp_hasDerivAt t hmap
  have hcz := LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hd' : DifferentiableAt ℝ (v x) t := by
    simpa only [Function.comp_def, hcz] using hd.differentiableAt
  exact hd'.hasDerivAt

end Yau.F04Proof
