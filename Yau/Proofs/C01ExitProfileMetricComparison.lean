import Yau.Proofs.C01FirstExitPaths

/-! Confined first-exit segments transfer local metric comparison to
comparison of the true boundary-distance minima. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem exit_profile_upper_of_compact_metric_upper
    (g : SmoothMetric M) (k₀ k₁ : HermitianField M) (hk₀ : MetricSmooth k₀) (hk₁ : MetricSmooth k₁)
    (o : M.Carrier) (L : ℝ) (hL : 0 < L) (ell : ℝ) (hell : 0 ≤ ell)
    (hmetric : ∀ x : M.Carrier, inducedDistance g.form o x ≤ L → ∀ v : TangentVector M x,
      2 * hermitianNormSq (k₁ x) v ≤ ell ^ 2 * (2 * hermitianNormSq (k₀ x) v)) :
    exitDistanceProfile g k₁ o L ≤ ell * exitDistanceProfile g k₀ o L := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup k₀ z
  obtain ⟨y, hy, heq, _⟩ := exitDistanceProfile_attained g k₀ hk₀ o L hL.le
  have happrox (δ : ℝ) (hδ : 0 < δ) :
      exitDistanceProfile g k₁ o L ≤ ell * (exitDistanceProfile g k₀ o L + δ) := by
    obtain ⟨f, hf₀, hf₁, hf, _, hlen⟩ := exists_smooth_nearMinimizingPath k₀ hk₀ o y δ hδ
    obtain ⟨u, hu, hhit, hconfined⟩ := exists_confined_first_exit g o L hL f
      hf.continuous.continuousOn hf₀ (by rw [hf₁]; exact hy.ge)
    let γ := integrableCurve_of_contMDiff k₀ hk₀ hf
    have hE : ENNReal.ofReal (exitDistanceProfile g k₁ o L) ≤
        ENNReal.ofReal ell * ENNReal.ofReal (curveLength k₀ γ.1) := by
      calc
        _ ≤ actualPathELength k₁ f 0 u :=
          exit_profile_le_actualPathELength_at_hit g k₁ hk₁ o L hL.le f hf hf₀ u hu.1.le hhit
        _ ≤ ENNReal.ofReal ell * actualPathELength k₀ f 0 u :=
          actualPathELength_upper_of_speedSq_upper k₀ k₁ _ ell hell hmetric f hconfined
        _ ≤ ENNReal.ofReal ell * actualPathELength k₀ f 0 1 := by
          exact mul_le_mul_of_nonneg_left (Manifold.pathELength_mono le_rfl hu.2) zero_le
        _ = _ := by rw [show actualPathELength k₀ f 0 1 = ENNReal.ofReal (curveLength k₀ γ.1)
          from (curveLength_eq_pathELength k₀ γ).symm]
    rw [← ENNReal.ofReal_mul hell] at hE
    have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hell (curveLength_nonneg k₀ γ.1))).mp hE
    rw [← heq] at hlen
    exact hreal.trans (mul_le_mul_of_nonneg_left hlen.le hell)
  have hc : ContinuousAt (fun δ : ℝ => ell * (exitDistanceProfile g k₀ o L + δ)) 0 := by fun_prop
  have hlim : Tendsto (fun δ : ℝ => ell * (exitDistanceProfile g k₀ o L + δ))
      (𝓝[>] 0) (𝓝 (ell * exitDistanceProfile g k₀ o L)) := by
    simpa only [add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact happrox δ hδ

theorem exit_profile_lower_of_compact_metric_lower
    (g : SmoothMetric M) (k₀ k₁ : HermitianField M) (hk₀ : MetricSmooth k₀) (hk₁ : MetricSmooth k₁)
    (o : M.Carrier) (L : ℝ) (hL : 0 < L) (ell : ℝ) (hell : 0 ≤ ell)
    (hmetric : ∀ x : M.Carrier, inducedDistance g.form o x ≤ L → ∀ v : TangentVector M x,
      ell ^ 2 * (2 * hermitianNormSq (k₀ x) v) ≤ 2 * hermitianNormSq (k₁ x) v) :
    ell * exitDistanceProfile g k₀ o L ≤ exitDistanceProfile g k₁ o L := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup k₁ z
  obtain ⟨y, hy, heq, _⟩ := exitDistanceProfile_attained g k₁ hk₁ o L hL.le
  apply le_of_forall_pos_lt_add
  intro δ hδ
  obtain ⟨f, hf₀, hf₁, hf, _, hlen⟩ := exists_smooth_nearMinimizingPath k₁ hk₁ o y δ hδ
  obtain ⟨u, hu, hhit, hconfined⟩ := exists_confined_first_exit g o L hL f
    hf.continuous.continuousOn hf₀ (by rw [hf₁]; exact hy.ge)
  let γ := integrableCurve_of_contMDiff k₁ hk₁ hf
  have hE : ENNReal.ofReal ell * ENNReal.ofReal (exitDistanceProfile g k₀ o L) ≤
      ENNReal.ofReal (curveLength k₁ γ.1) := by
    calc
      _ ≤ ENNReal.ofReal ell * actualPathELength k₀ f 0 u :=
        mul_le_mul_of_nonneg_left
          (exit_profile_le_actualPathELength_at_hit g k₀ hk₀ o L hL.le f hf hf₀ u hu.1.le hhit) zero_le
      _ ≤ actualPathELength k₁ f 0 u :=
        actualPathELength_lower_of_speedSq_lower k₀ k₁ _ ell hell hmetric f hconfined
      _ ≤ actualPathELength k₁ f 0 1 := Manifold.pathELength_mono le_rfl hu.2
      _ = _ := (curveLength_eq_pathELength k₁ γ).symm
  rw [← ENNReal.ofReal_mul hell] at hE
  have hreal := (ENNReal.ofReal_le_ofReal_iff (curveLength_nonneg k₁ γ.1)).mp hE
  rw [← heq] at hlen
  exact hreal.trans_lt hlen

end Yau.NodeProofs.C01Aux
