import Yau.Proofs.P04CanonicalSeriesBudgets
import Yau.Proofs.P04BufferedSeriesSmooth
import Yau.Proofs.P04MajorantCharts
import Yau.Proofs.P04LogSumSquares
import Yau.Proofs.P04SeriesBounds

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff BigOperators Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The SAME constructed positive canonical norm series gives an actual
smooth Ricci majorant with the original three-halves distance growth. -/
theorem canonical_family_ricci_majorant (g : SmoothMetric M) (o : M.Carrier)
    (S : ℕ → CanonicalSection M) (hS : ∀ i, IsHolomorphicCanonical (S i))
    (hne : ∀ x : M.Carrier, ∃ i, S i x ≠ 0) (C : ℕ → ℝ)
    (hGrowth : ∀ i x, canonicalNormSq g.form (S i) x ≤ Real.exp (C i*(1+distFrom g.form o x))) :
    ∃ Ξ : M.Carrier → ℝ, SmoothFn Ξ ∧
      (∀ x, Yau.Blueprint.HermLE (ricci g.form x) (levi Ξ x)) ∧
      ∃ D : ℝ, ∀ x, Ξ x ≤ D*(1+distFrom g.form o x ^ ((3 : ℝ)/2)) := by
  classical
  obtain ⟨a,ρ,β,hdata,hcover⟩ := exists_countable_buffered_charts (M := M)
  have hρ (j : ℕ) := (hdata j).1
  have ht (j : ℕ) := (hdata j).2.1
  have hβ (j : ℕ) := (hdata j).2.2.1
  have hcβ (j : ℕ) := (hdata j).2.2.2.1
  have hsβ (j : ℕ) : tsupport (β j) ⊆ chartTarget (a j) :=
    pole_cutoff_support_in_chart (a j) (hρ j) (ht j) (hdata j).2.2.2.2.1
  have hone (j : ℕ) := (hdata j).2.2.2.2.2
  choose B hB using fun i => exponential_linear_le_three_halves (C i)
  obtain ⟨c,hc,hmodels⟩ := exists_canonical_coefficients_with_all_jets g S hS a β hβ hcβ hsβ B
  let E : M.Carrier → ℝ := fun x => Real.exp (1+distFrom g.form o x ^ ((3 : ℝ)/2))
  let A : M.Carrier → ℝ := fun x => ∑' i, c i*canonicalNormSq g.form (S i) x
  have hr (x : M.Carrier) : 0 ≤ distFrom g.form o x := g.induced_distance_nonneg o x
  have hseries (x : M.Carrier) : Summable (fun i => c i*canonicalNormSq g.form (S i) x) ∧ A x ≤ 2*E x := by
    apply weighted_series_of_exponential_bounds
      (fun i => canonicalNormSq_nonneg g.form (S i) x) (fun i => (hc i).1.le) (Real.exp_pos _).le
    · exact fun i => (hGrowth i x).trans (hB i _ (hr x))
    · exact fun i => (hc i).2
  have hp (x : M.Carrier) : 0 < A x := by
    obtain ⟨i,hi⟩ := hne x
    have hnorm : 0 < canonicalNormSq g.form (S i) x := by
      apply lt_of_le_of_ne' (canonicalNormSq_nonneg g.form (S i) x)
      intro hz
      exact hi ((canonicalNormSq_eq_zero_iff g.form (S i) x).mp hz)
    exact weighted_tsum_pos (fun i => canonicalNormSq_nonneg g.form (S i) x)
      (fun i => (hc i).1) (hseries x).1 ⟨i,hnorm⟩
  have hA : SmoothFn A := smoothFn_tsum_of_buffered_charts a ρ β hone hcover hρ
    (fun i => canonicalNormSq g.form (S i)) c (fun j => (hmodels j).1.1)
  refine ⟨fun x => Real.log (A x),positive_log_smooth hA hp,?_,1+Real.log 2,?_⟩
  · intro x
    obtain ⟨j,hx,hinner⟩ := hcover x
    let U : Set (ComplexVector n) := Metric.ball (chartPt (a j) (a j)) (ρ j)
    have hU : IsOpen U := Metric.isOpen_ball
    have hUt : U ⊆ chartTarget (a j) :=
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
        (by linarith [hρ j] : ρ j ≤ 2*ρ j))).trans (ht j)
    let F : ComplexVector n → ℝ := fun z => ∑' i, c i*(β j z*‖canonicalCoeff (S i) (a j) z‖^2)
    have hF : ContDiff ℝ ∞ F := (hmodels j).2.1
    have hFvalue (z : ComplexVector n) (hz : z ∈ U) :
        F z=(hMat g.form (a j) z).det.re*inChart (a j) A z := by
      have hD := L18Aux.hMat_det_re_pos g.form (a j) (hUt hz)
      calc
        _ = ∑' i, (hMat g.form (a j) z).det.re*(c i*canonicalNormSq g.form (S i) (chartInv (a j) z)) := by
          apply tsum_congr
          intro i
          rw [hone j z (Metric.ball_subset_closedBall hz),one_mul]
          have H := canonicalNormSq_inChart g.form (S i) (a j) (hUt hz)
          change canonicalNormSq g.form (S i) (chartInv (a j) z)=_ at H
          rw [H]
          field_simp
        _ = _ := tsum_mul_left
    have hFpos (z : ComplexVector n) (hz : z ∈ U) : 0 < F z := by
      rw [hFvalue z hz]
      exact mul_pos (L18Aux.hMat_det_re_pos g.form (a j) (hUt hz)) (hp _)
    have hjets (q : ℕ) (_hq : q ≤ 2) (z : ComplexVector n) (hz : z ∈ U) :
        Tendsto (fun N => iteratedFDeriv ℝ q
          (fun w => ∑ i ∈ Finset.range N, c i*‖canonicalCoeff (S i) (a j) w‖^2) z)
          atTop (𝓝 (iteratedFDeriv ℝ q F z)) := by
      have hjet := (hmodels j).2.2 q z
      apply hjet.congr'
      exact Eventually.of_forall (fun N => by
        have heq : (fun w => ∑ i ∈ Finset.range N, c i*(β j w*‖canonicalCoeff (S i) (a j) w‖^2)) =ᶠ[𝓝 z]
            (fun w => ∑ i ∈ Finset.range N, c i*‖canonicalCoeff (S i) (a j) w‖^2) := by
          filter_upwards [hU.mem_nhds hz] with w hw
          simp only [hone j w (Metric.ball_subset_closedBall hw),one_mul]
        exact (heq.iteratedFDeriv ℝ q).eq_of_nhds)
    have hpsh := levi_log_sumSquares_posSemidef U hU
      (fun i => canonicalCoeff (S i) (a j)) c (fun i => (hS i (a j)).mono hUt)
      (fun i => (hc i).1.le) F (hF.of_le (by simp)).contDiffOn hFpos hjets
    have hz : chartPt (a j) x ∈ U := Metric.ball_subset_ball
      (by linarith [hρ j] : ρ j/2 ≤ ρ j) hinner
    apply ricci_le_levi_log_of_containing_chart g hA hp x (a j) hx
    have heq : (fun z => Real.log ((hMat g.form (a j) z).det.re*inChart (a j) A z)) =ᶠ[𝓝 (chartPt (a j) x)]
        (fun z => Real.log (F z)) := by
      filter_upwards [hU.mem_nhds hz] with z hzt
      rw [hFvalue z hzt]
    rw [L22Aux.leviC_congr_of_eventuallyEq heq]
    exact hpsh _ hz
  · exact fun x => log_le_three_halves (hp x) (hr x) (hseries x).2

end Yau.Proofs.P04Aux
