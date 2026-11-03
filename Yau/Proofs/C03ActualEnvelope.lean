import Yau.Proofs.C03PullbackLogLevi
import Yau.Proofs.C03ChartSupports
import Yau.Proofs.C03LeviLower
import Yau.Proofs.C03EnvelopeSmoothing

/-! The original chart produces the actual continuous psh envelope and
one fixed smooth regularization, with the uniform quantitative constants. -/

noncomputable section
open Filter Set Metric
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L22Aux
open Yau.NodeProofs.E01Aux
open EnvelopeSmoothing
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def chartLogBound (c : ℝ) (ξ : ComplexVector n) : ℝ :=
  max 0 (-Real.log (min c 1)) + 2 * Real.log (1 + ‖ξ‖)

theorem chartLogBound_nonneg (c : ℝ) (ξ : ComplexVector n) : 0 ≤ chartLogBound c ξ :=
  add_nonneg (le_max_left _ _) (mul_nonneg (by norm_num)
    (Real.log_nonneg (by linarith [norm_nonneg ξ])))

def chartLogEnvelope (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) (ξ : ComplexVector n) (ρ : ℝ) :
    ComplexVector n → ℝ :=
  chartEnvelope hn X Φ r hr hΦ (chartLogDual hn X Φ r hr hΦ ξ) ρ

theorem exists_actual_envelope_smoothing (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r c ρ R : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hρ : 0 < ρ) (hR : 0 < R) (hRr : R < r / 2)
    (hΦ : IsLocalBiholomorphism Φ r)
    (hlo : ∀ z ∈ ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z))
    (hsmall : Real.sqrt ((min c 1)⁻¹) * ρ < r / 4)
    (ξ : ComplexVector n) (hξ : ξ ≠ 0)
    (hunit : dualNormMat (pullbackMat X.metric.form Φ 0) ξ = 1)
    (K : Set X.manifold.Carrier) (κ : ℝ) (hκ : 0 < κ)
    (htarget : ∀ y ∈ K, ∀ u v : TangentVector X.manifold y,
      κ * hermitianNormSq (X.metric.form y) u * hermitianNormSq (X.metric.form y) v ≤
        bisectionalForm X.metric.form y (tangentCoords y y u) (tangentCoords y y v))
    (S T : Set (ComplexVector n)) (hS : IsOpen S) (hSO : S ⊆ ball 0 (r / 2))
    (hT : IsCompact T) (hTS : T ⊆ S) (hTD : T ⊆ ball 0 R)
    (hnear : ∀ z ∈ S, inducedDistance (chartExtendedField hn X Φ r hr hΦ)
      z (0 : ComplexVector n) ≤ ρ)
    (himage : ∀ z ∈ S, ∀ y ∈ ball (0 : ComplexVector n) (3 * r / 4),
      inducedDistance (chartExtendedField hn X Φ r hr hΦ) z y ≤ ρ → Φ y ∈ K) :
    IsPshOn (fun z => (chartLogEnvelope hn X Φ r hr hΦ ξ ρ z : EReal)) (ball 0 (r / 2)) ∧
      ∃ g : ComplexVector n → ℝ, ContDiff ℝ ∞ g ∧
        (∀ z ∈ ball 0 R, (leviC g z).PosSemidef ∧ g z ≤ chartLogBound c ξ) ∧
        ∀ z ∈ T, 0 ≤ g z ∧ HermLE (((κ / 2 : ℝ) : ℂ) •
          gMat (chartExtendedField hn X Φ r hr hΦ) z) (leviC g z) := by
  let k := chartExtendedField hn X Φ r hr hΦ
  let ψ := chartLogDual hn X Φ r hr hΦ ξ
  let f := chartLogEnvelope hn X Φ r hr hΦ ξ ρ
  have ks : MetricSmooth k := chartExtendedField_metricSmooth hn X Φ r hr hΦ
  have hcompact (p : (ComplexEuclideanManifold n hn).Carrier) (a : ℝ) :
      IsCompact {x | inducedDistance k p x ≤ a} :=
    chartExtendedField_compact_sublevels hn X Φ r c hr hc hΦ hlo p a
  have hψ : ContDiff ℝ ∞ ψ := chartLogDual_contDiff hn X Φ r hr hΦ ξ hξ
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  have hfc : Continuous f := chartEnvelope_continuous hn X Φ r c ρ hr hc hρ hΦ hlo ψ hψ.continuous
  have hsupport : PlanarLowerSupports f (ball 0 (r / 2)) (fun _ _ => 0) := by
    intro z hz V
    have H := chartEnvelope_planar_lower_support hn X Φ r c ρ hr hc hρ hΦ hlo hsmall
      ψ hψ2 0 z V hz (fun y hy _ W => by
        have HP := chartLogDual_leviC_posSemidef hn X Φ r hr hΦ ξ hξ y hy
        simpa only [zero_mul] using (leviC_posSemidef_iff hψ2.contDiffAt).mp HP W)
    simpa only [mul_zero, zero_mul, f, chartLogEnvelope, ψ] using H
  have hstrict : PlanarLowerSupports f S
      (fun z V => 4 * κ * matrixQuadratic (gMat k z) V) := by
    intro z hz V
    exact chartEnvelope_planar_lower_support hn X Φ r c ρ hr hc hρ hΦ hlo hsmall
      ψ hψ2 κ z V (hSO hz) (fun y hy hzy W =>
        complexLeviQuadratic_ge_of_HermLE ψ y W hψ2.contDiffAt _ κ
          (chartLogDual_leviC_lower_of_target hn X Φ r hr hΦ ξ hξ y hy κ
            (htarget (Φ y) (himage z hz y hy hzy))))
  have hnonneg : ∀ z ∈ S, 0 ≤ f z := by
    intro z hz
    exact fieldBallMaximum_nonneg_of_near k ks hcompact ψ hψ.continuous ρ hρ.le
      (0 : ComplexVector n) (le_of_eq (chartLogDual_zero hn X Φ r hr hΦ ξ hunit).symm)
      z (hnear z hz)
  have hupper : ∀ z ∈ ball (0 : ComplexVector n) (r / 2), f z ≤ chartLogBound c ξ := by
    intro z _
    exact fieldBallMaximum_le k ks hcompact ψ hψ.continuous ρ hρ.le (chartLogBound c ξ)
      (chartLogDual_le hn X Φ r c hr hc hΦ hlo ξ hξ) z
  exact exists_smooth_envelope_on_ball (r / 2) R hR hRr f hfc.continuousOn hsupport
    S T hS hSO hT hTS hTD (fun z => gMat k z)
    (fun i j => (chartExtendedField_gMat_contDiff hn X Φ r hr hΦ i j).continuous)
    (chartExtendedField_gMat_posDef hn X Φ r hr hΦ) κ hκ hstrict hnonneg
    (chartLogBound c ξ) hupper

end Yau.Proofs.C03Aux
