import Yau.Proofs.C03ShortParallelData
import Yau.Proofs.C03ChartNaturality
import Yau.Proofs.C03CurveLengthPackage

/-! The actual short source minimizer is packaged as an admissible
integrable curve, without changing its speed, endpoints or confinement. -/

noncomputable section
open Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem exists_short_chart_minimizing_curve (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r c R : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hΦ : IsLocalBiholomorphism Φ r)
    (hlo : ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z))
    (hsmall : Real.sqrt ((min c 1)⁻¹) * R < r / 4)
    (z y : ComplexVector n) (hz : z ∈ Metric.ball (0 : ComplexVector n) (r / 2))
    (hzy : inducedDistance (chartExtendedField hn X Φ r hr hΦ) z y ≤ R) :
    ∃ δ : IntegrableCurve (chartExtendedField hn X Φ r hr hΦ) z y,
      (∀ t ∈ Icc (0 : ℝ) 1, δ.1 t ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4)) ∧
      curveLength (chartExtendedField hn X Φ r hr hΦ) δ.1 =
        inducedDistance (chartExtendedField hn X Φ r hr hΦ) z y := by
  let k := chartExtendedField hn X Φ r hr hΦ
  have ks : MetricSmooth k := chartExtendedField_metricSmooth hn X Φ r hr hΦ
  obtain ⟨hI, _, _⟩ := chartExtendedField_local_geometry hn X Φ r hr hΦ
  obtain ⟨γ, W, hγ, _, hγ0, hγ1, _, himage, hspeed, _, _, _⟩ :=
    exists_short_source_parallel_data hn k ks (min c 1) (lt_min hc zero_lt_one)
      (chartExtendedField_lower hn X Φ r c hr hΦ hlo) r R hsmall hI z y 0 hz hzy
  have hγM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ :=
    (hγ.of_le (by norm_num)).contMDiff
  let δ := L23Aux.integrableCurve_of_contMDiff k ks hγM
  have hlength : curveLength k δ.1 = inducedDistance k z y :=
    integrableCurve_length_of_constant_speed k ks γ hγM (inducedDistance k z y)
      (inducedDistance_nonneg k ks z y) hspeed
  have H : ∃ β : IntegrableCurve k (γ 0) (γ 1),
      (∀ t ∈ Icc (0 : ℝ) 1, β.1 t ∈ Metric.ball (0 : ComplexVector n) (3 * r / 4)) ∧
      curveLength k β.1 = inducedDistance k z y :=
    ⟨δ, fun _ ht => himage ht, hlength⟩
  subst z
  subst y
  exact H

end Yau.Proofs.C03Aux
