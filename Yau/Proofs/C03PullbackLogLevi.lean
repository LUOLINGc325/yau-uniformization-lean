import Yau.Proofs.C03ChartLogDual
import Yau.Proofs.C03ChartNaturality
import Yau.Proofs.C03TargetCurvature
import Yau.Proofs.C03ChernGauge

/-! Actual target Chern curvature gives the log-dual Levi lower bound
for the original chart. The global cutoff field is used only locally. -/

noncomputable section
open Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L22Aux
open Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem chartLogDual_leviC_lower_of_target (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) (ξ : ComplexVector n) (hξ : ξ ≠ 0)
    (z : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4))
    (κ : ℝ)
    (hcurv : ∀ u v : TangentVector X.manifold (Φ z),
      κ * hermitianNormSq (X.metric.form (Φ z)) u *
          hermitianNormSq (X.metric.form (Φ z)) v ≤
        bisectionalForm X.metric.form (Φ z)
          (tangentCoords (Φ z) (Φ z) u) (tangentCoords (Φ z) (Φ z) v)) :
    HermLE ((κ : ℂ) • gMat (chartExtendedField hn X Φ r hr hΦ) z)
      (leviC (chartLogDual hn X Φ r hr hΦ ξ) z) := by
  let k := chartExtendedField hn X Φ r hr hΦ
  let H : ComplexVector n → Herm n := fun w => gMat k w
  have ks : MetricSmooth k := chartExtendedField_metricSmooth hn X Φ r hr hΦ
  have hs : MetricSmooth X.metric.form := metricSmooth_of_smoothMetric X.metric
  let O := Metric.ball (0 : ComplexVector n) (3 * r / 4)
  have hO : IsOpen O := Metric.isOpen_ball
  have hsub : O ⊆ Metric.ball (0 : ComplexVector n) r := Metric.ball_subset_ball (by linarith)
  have hΦO : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ O := hΦ.1.mono hsub
  have hbij : ∀ w ∈ O, Function.Bijective (mfderiv (ComplexModel n) (ComplexModel n) Φ w) :=
    fun w hw => hΦ.2 w (hsub hw)
  have heq : ∀ (w : (ComplexEuclideanManifold n hn).Carrier), w ∈ O →
      ∀ u v : TangentVector (ComplexEuclideanManifold n hn) w,
      (k w).toFun u v = (X.metric.form (Φ w)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ w u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ w v) :=
    fun w hw u v => chartExtendedField_pullback hn X Φ r hr hΦ w hw u v
  have hPos (w : ComplexVector n) : (H w).PosDef :=
    chartExtendedField_gMat_posDef hn X Φ r hr hΦ w
  have hH (i j : Fin n) : ContDiffOn ℝ ∞ (fun w => H w i j) univ :=
    (chartExtendedField_gMat_contDiff hn X Φ r hr hΦ i j).contDiffOn
  change HermLE ((κ : ℂ) • H z) (leviC (LogDual.logDual H ξ) z)
  apply LogDual.logDual_leviC_lower isOpen_univ H (fun w => (hPos w).isHermitian)
    hH (fun w _ => hPos w) ξ hξ z (mem_univ z) κ
  intro a
  have hR : LogDual.computedResidual H z ξ a =
      bisectionalForm X.metric.form (Φ z)
        (tangentCoords (Φ z) (Φ z) (mfderiv (ComplexModel n) (ComplexModel n) Φ z
          (WithLp.toLp 2 (star (WithLp.ofLp (matrixFiberMap (gMat k z)⁻¹ᵀ ξ))))))
        (tangentCoords (Φ z) (Φ z) (mfderiv (ComplexModel n) (ComplexModel n) Φ z a)) :=
    ChernGauge.computedResidual_pullback hn k ks X.metric.form hs hO hΦO hbij heq hz ξ a
  have HU := ChernGauge.target_raised_norm_eq_dual hn k X.metric.form Φ z (heq z hz) ξ
  have HA := ChernGauge.target_norm_eq_source_quadratic hn k X.metric.form Φ z (heq z hz) a
  rw [hR]
  change κ * dualNormMat (gMat k z) ξ * ellipsoidQuadratic (gMat k z) a ≤ _
  rw [← HU, ← HA]
  exact hcurv _ _

theorem chartLogDual_leviC_posSemidef (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) (ξ : ComplexVector n) (hξ : ξ ≠ 0)
    (z : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4)) :
    (leviC (chartLogDual hn X Φ r hr hΦ ξ) z).PosSemidef := by
  obtain ⟨κ, hκ, hbound⟩ := compact_chern_bisectional_lower_bound X {Φ z} isCompact_singleton
  have hcurv (u v : TangentVector X.manifold (Φ z)) :
      0 * hermitianNormSq (X.metric.form (Φ z)) u * hermitianNormSq (X.metric.form (Φ z)) v ≤
        bisectionalForm X.metric.form (Φ z)
          (tangentCoords (Φ z) (Φ z) u) (tangentCoords (Φ z) (Φ z) v) := by
    simp only [zero_mul]
    exact (mul_nonneg (mul_nonneg hκ.le (hermitianNormSq_nonneg _ _))
      (hermitianNormSq_nonneg _ _)).trans (hbound (Φ z) (mem_singleton _) u v)
  have H := chartLogDual_leviC_lower_of_target hn X Φ r hr hΦ ξ hξ z hz 0 hcurv
  simpa only [Complex.ofReal_zero, zero_smul, HermLE, sub_zero] using H

end Yau.Proofs.C03Aux
