import Yau.Proofs.C03SourceEnergy
import Yau.Proofs.C03EnergyParallelJets

/-! The endpoint term of the genuine energy variation is the integral of
the covariant derivative pairing along the actual source geodesic. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem source_geodesic_velocity_equation (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (γ : ℝ → ComplexVector n) (J : Set ℝ) (hγ : FieldGeodesicOn k γ J)
    (t : ℝ) (ht : t ∈ J) :
    HasDerivAt (deriv γ)
      (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (deriv γ t)) t := by
  have hsrc : γ t ∈ (chartAt (ComplexVector n) (0 : ComplexVector n)).source := by
    rw [euclidean_chartSource hn]
    trivial
  have H0 := hγ.2 (0 : ComplexVector n) t ht
    (by simpa only [extChartAt_source] using hsrc)
  have H := (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt t H0
  convert! H using 1 <;>
    simp only [Function.comp_def, geoChartState, euclidean_chartPt,
      chartGeodesicSpray, chartGeodesicAcceleration_eq]
  rfl

theorem source_geodesic_pairing_boundary (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (γ T A : ℝ → ComplexVector n)
    (hγ : ContDiff ℝ 1 γ) (hT : ContDiff ℝ 1 T) (hA : ContDiff ℝ 1 A)
    (hγT : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (T t) t)
    (hgeo : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt T
      (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (T t) (T t)) t) :
    (∫ t in Icc (0 : ℝ) 1, realMetricInChart k (0 : ComplexVector n) (γ t) (T t)
      (deriv A t + chartChristoffelBilin k (0 : ComplexVector n) (γ t) (T t) (A t))) =
      realMetricInChart k (0 : ComplexVector n) (γ 1) (T 1) (A 1) -
        realMetricInChart k (0 : ComplexVector n) (γ 0) (T 0) (A 0) := by
  have hG : Continuous (realMetricInChart k (0 : ComplexVector n)) := by
    apply continuousOn_univ.mp
    simpa only [euclidean_chartTarget hn] using
      (realMetricInChart_smooth k hk (0 : ComplexVector n)).continuousOn
  have hΓ : Continuous (chartChristoffelBilin k (0 : ComplexVector n)) := by
    apply continuousOn_univ.mp
    simpa only [euclidean_chartTarget hn] using
      (chartChristoffelBilin_contDiffOn k hk (0 : ComplexVector n)).continuousOn
  have hAd : Continuous (deriv A) := (show ContDiff ℝ 0 (deriv A) from hA.deriv').continuous
  have hc : Continuous (fun t => realMetricInChart k (0 : ComplexVector n) (γ t) (T t)
      (deriv A t + chartChristoffelBilin k (0 : ComplexVector n) (γ t) (T t) (A t))) :=
    ((hG.comp hγ.continuous).clm_apply hT.continuous).clm_apply
      (hAd.add (((hΓ.comp hγ.continuous).clm_apply hT.continuous).clm_apply hA.continuous))
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :=
    chartGeodesic_pairing_hasDerivAt k hk (0 : ComplexVector n)
      (by rw [euclidean_chartTarget hn]; trivial)
      (hγT t (by simpa only [uIcc_of_le zero_le_one] using ht))
      (hgeo t (by simpa only [uIcc_of_le zero_le_one] using ht))
      ((hA.differentiable (by norm_num) t).hasDerivAt)
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] at H
  exact H

end Yau.Proofs.C03Aux
