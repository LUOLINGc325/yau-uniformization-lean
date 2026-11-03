import Yau.Proofs.C01PathIntegratedHarnack

/-! The full original integrated Harnack clause follows from genuine
near shortest smooth paths for the actual initial-time metric.  No
completeness or minimizing geodesic assumption enters the argument. -/

noncomputable section

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_scalar_integrated_distance_harnack
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x y : Pt X) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    scalarCurvature (h a) x ≤ scalarCurvature (h b) y * (b / a) *
      Real.exp (inducedDistance (h a) x y ^ 2 / (b - a)) := by
  letI := manifold_realSmooth X.manifold
  let d := inducedDistance (h a) x y
  have hg := localizedFlow_metricSmooth_nonneg hflow a ha.le
  have hd : 0 ≤ d := inducedDistance_nonneg (h a) hg x y
  have hb : 0 < b := ha.trans hab
  have hcoef : 0 ≤ scalarCurvature (h b) y * (b / a) :=
    mul_nonneg (localizedFlow_scalar_nonneg hflow y b hb.le) (div_pos hb ha).le
  have happrox (ε : ℝ) (hε : 0 < ε) :
      scalarCurvature (h a) x ≤ scalarCurvature (h b) y * (b / a) *
        Real.exp ((d + 2 * ε) ^ 2 / (b - a)) := by
    obtain ⟨f, hx, hy, hf, hv, hlen⟩ := exists_smooth_nearMinimizingPath (h a) hg x y ε hε
    let γ := piecewiseC1Curve_of_contMDiff hf
    let L := curveLength (h a) γ
    have hL : 0 ≤ L := curveLength_nonneg (h a) γ
    have hlen' : L < d + ε := hlen
    have hγc (s : ℝ) (_hs : s ∈ Set.Icc (0 : ℝ) 1) : ContinuousAt γ.toFun s :=
      hf.continuous.continuousAt
    have hγd (s : ℝ) (_hs : s ∈ Set.Icc (0 : ℝ) 1) : DifferentiableAt ℝ
        (fun u : ℝ => extChartAt (ComplexModel n) (γ s) (γ u)) s :=
      (contDiffAt_chart_of_contMDiff hf s).differentiableAt (by norm_num)
    have hp := localizedFlow_path_integrated_harnack hflow hjoint γ a b ε ha hab hε hv hγc hγd
    change scalarCurvature (h a) (f 0) ≤ scalarCurvature (h b) (f 1) * (b / a) *
      Real.exp ((L + ε) * L / (b - a)) at hp
    rw [hx, hy] at hp
    have hprod : (L + ε) * L ≤ (d + 2 * ε) ^ 2 := by
      have h₁ : L + ε ≤ d + 2 * ε := by linarith
      have h₂ : L ≤ d + 2 * ε := by linarith
      have h₃ : 0 ≤ d + 2 * ε := by positivity
      simpa only [pow_two] using mul_le_mul h₁ h₂ hL h₃
    have he : Real.exp ((L + ε) * L / (b - a)) ≤ Real.exp ((d + 2 * ε) ^ 2 / (b - a)) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hprod (sub_pos.mpr hab).le)
    exact hp.trans (mul_le_mul_of_nonneg_left he hcoef)
  have hc : ContinuousAt
      (fun ε : ℝ => scalarCurvature (h b) y * (b / a) * Real.exp ((d + 2 * ε) ^ 2 / (b - a))) 0 := by
    fun_prop
  have hlim : Tendsto
      (fun ε : ℝ => scalarCurvature (h b) y * (b / a) * Real.exp ((d + 2 * ε) ^ 2 / (b - a)))
      (𝓝[>] (0 : ℝ)) (𝓝 (scalarCurvature (h b) y * (b / a) * Real.exp (d ^ 2 / (b - a)))) := by
    simpa only [mul_zero, add_zero] using! hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact happrox ε hε

theorem localizedFlow_integrated_harnack
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h) :
    ∃ C : ℝ, ∀ x y t t', 0 < t → t < t' →
      scalarCurvature (h t) x ≤ scalarCurvature (h t') y * (t' / t) *
        Real.exp (C * distFrom (h t) x y ^ 2 / (t' - t)) := by
  refine ⟨1, ?_⟩
  intro x y t t' ht htt'
  simpa only [one_mul, distFrom] using
    localizedFlow_scalar_integrated_distance_harnack hflow hjoint x y t t' ht htt'

end Yau.NodeProofs.C01Aux
