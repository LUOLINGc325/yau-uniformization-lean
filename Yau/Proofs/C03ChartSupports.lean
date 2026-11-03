import Yau.Proofs.C03BallSupports
import Yau.Proofs.C03ChartNaturality
import Yau.Proofs.C03BallBounds

/-! The original chart and its canonical extension supply the actual
continuous moving envelope and its planar lower supports. -/

noncomputable section
open Filter Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux L22Aux
open Yau.NodeProofs.P02Aux Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def chartEnvelope (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) (ψ : ComplexVector n → ℝ) (ρ : ℝ) :
    ComplexVector n → ℝ :=
  fieldBallMaximum (chartExtendedField hn X Φ r hr hΦ) ψ ρ

theorem chartEnvelope_continuous (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r c ρ : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hρ : 0 < ρ) (hΦ : IsLocalBiholomorphism Φ r)
    (hlo : ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z))
    (ψ : ComplexVector n → ℝ) (hψ : Continuous ψ) :
    Continuous (chartEnvelope hn X Φ r hr hΦ ψ ρ) :=
  fieldBallMaximum_continuous _ (chartExtendedField_metricSmooth hn X Φ r hr hΦ)
    (chartExtendedField_compact_sublevels hn X Φ r c hr hc hΦ hlo) ψ hψ ρ hρ

theorem chartEnvelope_planar_lower_support (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r c ρ : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hρ : 0 < ρ) (hΦ : IsLocalBiholomorphism Φ r)
    (hlo : ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z))
    (hsmall : Real.sqrt ((min c 1)⁻¹) * ρ < r / 4)
    (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ 2 ψ) (κ : ℝ)
    (z V : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (r / 2))
    (hLevi : ∀ y ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4),
      inducedDistance (chartExtendedField hn X Φ r hr hΦ) z y ≤ ρ → ∀ W,
        κ * ellipsoidQuadratic (gMat (chartExtendedField hn X Φ r hr hΦ) y) W ≤
          complexLeviQuadratic ψ y W) :
    ∃ s : ℂ → ℝ, ContDiffAt ℝ 2 s 0 ∧ s 0 = chartEnvelope hn X Φ r hr hΦ ψ ρ z ∧
      (∀ᶠ a : ℂ in 𝓝 0, s a ≤ chartEnvelope hn X Φ r hr hΦ ψ ρ (z + a • V)) ∧
      4 * κ * ellipsoidQuadratic (gMat (chartExtendedField hn X Φ r hr hΦ) z) V ≤
        planarTrace s 0 := by
  obtain ⟨hI, hII, hcurv⟩ := chartExtendedField_local_geometry hn X Φ r hr hΦ
  exact exists_ball_lower_support hn _ (chartExtendedField_metricSmooth hn X Φ r hr hΦ)
    (min c 1) (lt_min hc zero_lt_one) (chartExtendedField_lower hn X Φ r c hr hΦ hlo)
    r ρ hρ hsmall hI (fun y hy V => hII y hy V V) hcurv ψ hψ κ z V hz hLevi

end Yau.Proofs.C03Aux
