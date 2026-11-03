import Yau.Proofs.F01AFiniteScalarJetBounds
import Yau.Proofs.F01ScalarCurvatureChart
import Yau.Proofs.F01ScalarTimeMaximum
import Yau.Proofs.F01ChartGramSmooth
import Yau.Proofs.F01AGlobalMatrixTwoJets
import Yau.Proofs.F01RelativeScalarSandwich
import Yau.Proofs.F01ComparisonTraceBound
import Yau.Proofs.F01LogDetRatioSmooth

/-! The boundedness inlet of the scalar maximum principle is an actual
finite-jet consequence. The qualitative scalar bound is allowed to depend
on the fixed solution; the maximum-principle cap is its initial bound. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem actual_scalar_bound_of_uniform_chart_matrix_jets
    (g : HermitianField M) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) {I : Set ℝ} {ell R : ℝ}
    (hell : 0 < ell) (hR : 0 ≤ R)
    (hh : ∀ t ∈ I, MetricSmooth (h t))
    (hlo : ∀ x t, t ∈ I →
      (pullbackMatrix (h t) (A.chart x) 0 - (ell : ℂ) • 1).PosSemidef)
    (hjet : ∀ x t, t ∈ I → ∀ k : Fin 3,
      ‖iteratedFDeriv ℝ k.val (fun z => pullbackMatrix (h t) (A.chart x) z) 0‖ ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ x t, t ∈ I → |scalarCurvature (h t) x| ≤ B := by
  obtain ⟨B, hB, hb⟩ := finite_negative_scalar_uniform_bound (n := n) hell hR
  refine ⟨B, hB, ?_⟩
  intro x t ht
  have hz : (0 : Space n) ∈ (A.chart x).source :=
    A.closedBall_source x (mem_closedBall_self A.radius_pos.le)
  have hH : ContDiffAt ℝ ∞ (fun z => pullbackMatrix (h t) (A.chart x) z) 0 :=
    (matrix_contDiffOn_of_entries (fun i j => pullbackMatrix_entry_contDiffOn
      (h t) (hh t ht) (A.chart x) (A.differentiable x) i j)).contDiffAt
        ((A.chart x).open_source.mem_nhds hz)
  have heq := scalarCurvature_holomorphic_chart (h t) (hh t ht) (A.chart x)
    (A.differentiable x) (A.inverse_differentiable x) hz
  rw [A.center x] at heq
  rw [← heq]
  exact hb _ 0 hH (hlo x t ht) (hjet x t ht)

theorem actual_logdet_time_bounded_of_uniform_chart_matrix_jets
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {T ell R : ℝ} (hT : 0 < T) (hell : 0 < ell) (hR : 0 ≤ R)
    (hh : MetricFamilySmooth h (Icc 0 T)) (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s)
    (hlo : ∀ x t, t ∈ Icc 0 T →
      (pullbackMatrix (h t) (A.chart x) 0 - (ell : ℂ) • 1).PosSemidef)
    (hjet : ∀ x t, t ∈ Icc 0 T → ∀ k : Fin 3,
      ‖iteratedFDeriv ℝ k.val (fun z => pullbackMatrix (h t) (A.chart x) z) 0‖ ≤ R) :
    ∃ Bpt : ℝ, 0 < Bpt ∧ ∀ x t, t ∈ Icc 0 T →
      flowLogDetTime g h (Icc 0 T) x t ≤ Bpt := by
  obtain ⟨Bpt, hBpt, hb⟩ := actual_scalar_bound_of_uniform_chart_matrix_jets g A h hell hR
    (fun t ht => metricFamilySmooth_slice hh ht) hlo hjet
  refine ⟨Bpt, hBpt, ?_⟩
  intro x t ht
  have hd := (closed_slab_logdet_evolution_and_heat g hg h U hT hh hU hpot hpde x ht).1
  change derivWithin (flowLogDetRatio g h x) (Icc 0 T) t ≤ Bpt
  rw [hd.derivWithin ((uniqueDiffOn_Icc hT) t ht)]
  exact (neg_le_abs _).trans (hb x t ht)

theorem exists_initial_backward_chart_scale (A : BoundedChartFamily g)
    {T : ℝ} (hT : 0 < T) :
    ∃ ρ : ℝ, 0 < ρ ∧ 4 * ρ ≤ A.radius ∧ 4 * ρ ≤ 1 ∧ (4 * ρ) ^ 2 ≤ T := by
  let ρ : ℝ := min (A.radius / 4) (min (1 / 4) (Real.sqrt T / 4))
  have hρ : 0 < ρ := lt_min (div_pos A.radius_pos (by norm_num))
    (lt_min (by norm_num) (div_pos (Real.sqrt_pos.mpr hT) (by norm_num)))
  have hR : ρ ≤ A.radius / 4 := min_le_left _ _
  have hOne : ρ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hSqrt : ρ ≤ Real.sqrt T / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, hρ, by linarith, by linarith, ?_⟩
  nlinarith [Real.sq_sqrt hT.le, Real.sqrt_nonneg T]

set_option maxHeartbeats 1000000 in
theorem native_scalar_time_globally_bounded
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {T C : ℝ} (hT : 0 < T) (hC : 1 ≤ C)
    (hh : MetricFamilySmooth h (Icc 0 T)) (hU : SmoothSpaceTime U (Icc 0 T))
    (hh0 : h 0 = g) (hU0 : ∀ x, U x 0 = 0)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s)
    (hflow : ∀ x s, s ∈ Icc 0 T →
      (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) :
    ∃ Bpt : ℝ, 0 < Bpt ∧ ∀ x t, t ∈ Icc 0 T →
      flowLogDetTime g h (Icc 0 T) x t ≤ Bpt := by
  obtain ⟨ρ, hρ, hρr, hρ1, hρT⟩ := exists_initial_backward_chart_scale A hT
  obtain ⟨R, hR, hjet⟩ := native_global_matrix_two_jet_bound g hg A h U hT hC
    hρ hρr hρ1 hρT hh hU hh0 hU0 hpot hpde hflow
  have hCp : 0 < C := zero_lt_one.trans_le hC
  let ell : ℝ := C⁻¹ * (A.bound 0)⁻¹
  have hell : 0 < ell := mul_pos (inv_pos.mpr hCp) (inv_pos.mpr (A.bound_pos 0))
  apply actual_logdet_time_bounded_of_uniform_chart_matrix_jets g hg A h U hT hell hR.le
    hh hU hpot hpde ?_ hjet
  intro x t ht
  have hz : (0 : Space n) ∈ ball 0 A.radius := mem_ball_self A.radius_pos
  have hbg := A.comparison x 0 hz
  have hnative := hflow ((A.chart x) 0) t ht
  have horders := relative_scalar_matrix_sandwich
    (ell := (A.bound 0)⁻¹) (upper := A.bound 0)
    (inv_nonneg.mpr hCp.le) hCp.le
    (by simpa only [Complex.ofReal_inv] using hbg.1) hbg.2
    (metric_lower_order_in_chart g (h t) (A.chart x) 0 hnative.1)
    (metric_upper_order_in_chart g (h t) (A.chart x) 0 hnative.2)
  simpa only [ell, Complex.ofReal_inv] using horders.1

theorem native_scalar_cap_and_potential_upper
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {T C a : ℝ} (hT : 0 < T) (hC : 1 ≤ C)
    (hh : MetricFamilySmooth h (Icc 0 T)) (hU : SmoothSpaceTime U (Icc 0 T))
    (hh0 : h 0 = g) (hU0 : ∀ x, U x 0 = 0)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio g h x s) (Icc 0 T) s)
    (hflow : ∀ x s, s ∈ Icc 0 T →
      (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef)
    (hinit : ∀ x, -scalarCurvature g x ≤ a)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (hf0 : ∀ x, 0 ≤ f x)
    (hproper : ∀ b : ℝ, IsCompact {x | f x ≤ b})
    {B : ℝ} (hB : 0 ≤ B) (hlevi : ∀ x, ((B : ℂ) • gMat g x - levi f x).PosSemidef) :
    ∀ x t, t ∈ Icc 0 T →
      flowLogDetTime g h (Icc 0 T) x t ≤ a ∧
      flowLogDetRatio g h x t ≤ a * t ∧ U x t ≤ a * t ^ 2 / 2 := by
  obtain ⟨Bpt, _, hbound⟩ := native_scalar_time_globally_bounded g hg A h U hT hC
    hh hU hh0 hU0 hpot hpde hflow
  have hcap := bounded_scalar_time_jet_upper g hg h U hT hh hU hh0 hpot hpde hinit hbound
    f hf hf0 hproper (fun x t ht => laplacian_bound_from_metric_comparison g (h t) f x
      (zero_lt_one.trans_le hC) hB (hflow x t ht).1 (hlevi x))
  have hd (x : M.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (flowLogDetRatio g h x) (flowLogDetTime g h (Icc 0 T) x t) (Icc 0 T) t := by
    have hh := (closed_slab_logdet_evolution_and_heat g hg h U hT hh hU hpot hpde x ht).1
    simpa only [flowLogDetTime, hh.derivWithin ((uniqueDiffOn_Icc hT) t ht)] using hh
  have hPU := uniform_closed_time_potential_bounds hT.le (flowLogDetRatio_initial g h hh0) hU0 hd hpde hcap
  exact fun x t ht => ⟨hcap x t ht, hPU x t ht⟩

end Yau.NodeProofs.F01Aux
