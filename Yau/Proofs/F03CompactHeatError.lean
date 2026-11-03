import Yau.Proofs.F03CompactHeatInitialRate
import Yau.Proofs.F03C2Laplacian

/-! The actual compact-source error is smooth, and every Laplacian power is O(t). -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem smoothFn_of_smoothSpaceTime {u : M.Carrier → ℝ → ℝ}
    {I : Set ℝ} (hu : SmoothSpaceTime u I) {t : ℝ} (ht : t ∈ I) :
    SmoothFn (fun x => u x t) := by
  intro a
  exact (hu a).comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz,ht⟩)

theorem wholeCompactHeat_smooth (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) : SmoothSpaceTime (wholeCompactHeat g hK μ hμ k) (Ioi 0) := by
  intro a
  simpa [wholeCompactHeat] using dirichletClassicalHeat_smooth g hK μ hμ univ isOpen_univ
    (l2Restriction μ univ (scalarEnergyDomainL2 g μ hμ k)) a

theorem smoothFn_laplacian_power (g : SmoothMetric M) {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (m : ℕ) : SmoothFn ((laplacian g.form)^[m] u) := by
  induction m with
  | zero => exact hu
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact smoothFn_laplacian g ih

theorem laplacian_sub_smooth (g : SmoothMetric M) {u v : M.Carrier → ℝ}
    (hu : SmoothFn u) (hv : SmoothFn v) :
    laplacian g.form (fun y => u y-v y)=(fun x => laplacian g.form u x-laplacian g.form v x) := by
  funext x
  have hU : ContDiffAt ℝ 2 (inChart x u) (chartPt x x) :=
    (contDiffAt_inChart hu x (mem_extChartAt_target x)).of_le (by simp)
  have hV : ContDiffAt ℝ 2 (inChart x v) (chartPt x x) :=
    (contDiffAt_inChart hv x (mem_extChartAt_target x)).of_le (by simp)
  simpa only [one_mul,neg_one_mul,sub_eq_add_neg] using
    laplacian_c2_linear_combination g.form u v x hU hV 1 (-1)

theorem laplacian_power_sub_smooth (g : SmoothMetric M) {u v : M.Carrier → ℝ}
    (hu : SmoothFn u) (hv : SmoothFn v) (m : ℕ) :
    (laplacian g.form)^[m] (fun y => u y-v y)=
      (fun x => ((laplacian g.form)^[m] u) x-((laplacian g.form)^[m] v) x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply',ih,
      laplacian_sub_smooth g (smoothFn_laplacian_power g hu m) (smoothFn_laplacian_power g hv m)]
    simp only [Function.iterate_succ_apply']

theorem wholeCompactHeat_error_power_rate
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (m : ℕ) :
    ∃ K : ℝ,0 < K ∧ ∀ t,0 < t →
      SmoothFn (fun y => wholeCompactHeat g hK μ hμ k y t-k y) ∧
      ∀ x,|((laplacian g.form)^[m] (fun y => wholeCompactHeat g hK μ hμ k y t-k y)) x| ≤ t*K := by
  obtain ⟨K,hK0,hBound⟩ := wholeCompactHeat_laplacian_power_initial_rate g hK μ hμ k m
  refine ⟨K,hK0,fun t ht => ?_⟩
  have hU := smoothFn_of_smoothSpaceTime (wholeCompactHeat_smooth g hK μ hμ k) ht
  refine ⟨smoothFn_sub hU k.2.1,fun x => ?_⟩
  rw [laplacian_power_sub_smooth g hU k.2.1 m]
  exact hBound t ht x

end Yau.Proofs.F03Aux
