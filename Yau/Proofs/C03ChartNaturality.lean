import Yau.Proofs.C03GlobalGeometry
import Yau.Proofs.C03PullbackNaturality

/-! The canonical cutoff extension has the original pullback geometry
throughout the open inner ball. No global Kähler property is asserted. -/

noncomputable section
open Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux
open Yau.NodeProofs.P02Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem chartExtendedField_pullback (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r)
    (z : (ComplexEuclideanManifold n hn).Carrier)
    (hz : z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4))
    (u v : TangentVector (ComplexEuclideanManifold n hn) z) :
    (chartExtendedField hn X Φ r hr hΦ z).toFun u v =
      (X.metric.form (Φ z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v) := by
  have H := congrFun (congrFun (chartExtendedField_inner hn X Φ r hr hΦ z
    (Metric.ball_subset_closedBall hz)) u) v
  simpa only [localPullbackProduct, pullbackHermitian, ContinuousLinearMap.coe_coe] using H

theorem chartExtendedField_local_geometry (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) :
    (∀ z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4), ∀ u v,
      chartChristoffelBilin (chartExtendedField hn X Φ r hr hΦ) (0 : ComplexVector n) z
        u (Complex.I • v) = Complex.I •
          chartChristoffelBilin (chartExtendedField hn X Φ r hr hΦ) (0 : ComplexVector n) z u v) ∧
    (∀ z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4), ∀ u v,
      chartChristoffelBilin (chartExtendedField hn X Φ r hr hΦ) (0 : ComplexVector n) z
        (Complex.I • u) (Complex.I • v) =
          -chartChristoffelBilin (chartExtendedField hn X Φ r hr hΦ) (0 : ComplexVector n) z u v) ∧
    ∀ z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4), ∀ T W : ComplexVector n,
      T ≠ 0 → W ≠ 0 → 0 < coordinateBisectional
        (chartExtendedField hn X Φ r hr hΦ) (0 : ComplexVector n) z T W := by
  let k := chartExtendedField hn X Φ r hr hΦ
  have ks : MetricSmooth k := chartExtendedField_metricSmooth hn X Φ r hr hΦ
  have hs : MetricSmooth X.metric.form := metricSmooth_of_smoothMetric X.metric
  let O := Metric.ball (0 : ComplexVector n) (3 * r / 4)
  have hO : IsOpen O := Metric.isOpen_ball
  have hsub : O ⊆ Metric.ball (0 : ComplexVector n) r :=
    Metric.ball_subset_ball (by linarith)
  have hΦO : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ O := hΦ.1.mono hsub
  have hbij : ∀ z ∈ O, Function.Bijective (mfderiv (ComplexModel n) (ComplexModel n) Φ z) :=
    fun z hz => hΦ.2 z (hsub hz)
  have heq : ∀ (z : (ComplexEuclideanManifold n hn).Carrier), z ∈ O →
      ∀ u v : TangentVector (ComplexEuclideanManifold n hn) z,
      (k z).toFun u v = (X.metric.form (Φ z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v) :=
    fun z hz u v => chartExtendedField_pullback hn X Φ r hr hΦ z hz u v
  refine ⟨?_, ?_, ?_⟩
  · intro z hz u v
    exact PullbackNaturality.chartChristoffel_pullback_I_right hn k ks X.metric.form hs
      hO hΦO hbij heq X.kahler_metric hz u v
  · intro z hz u v
    exact PullbackNaturality.chartChristoffel_pullback_I_I hn k ks X.metric.form hs
      hO hΦO hbij heq X.kahler_metric hz u v
  · intro z hz T W hT hW
    have H := PullbackNaturality.paired_energy_curvature_neg hn k ks X.metric.form hs
      hO hΦO hbij heq X.positive_bisectional_curvature hz hT hW
    have HC := connectionCurvature_bisectional_sign k ks (0 : ComplexVector n)
      (z := z) (by rw [PullbackNaturality.source_chartTarget hn]; trivial) T W
    linarith

end Yau.Proofs.C03Aux
