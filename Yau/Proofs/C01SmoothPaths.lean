import Yau.Proofs.C01InitialBisectional
import Yau.Proofs.C01RegularizedClock

/-! Near shortest globally C1 paths and continuous actual metric speed
for a smooth Hermitian field, with no completeness assumption. -/

noncomputable section

open MeasureTheory
open scoped Manifold Topology ContDiff ENNReal

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem field_smooth_path_speed_continuous (g : HermitianField M) (hg : MetricSmooth g) :
    letI := manifold_realSmooth M
    ∀ (f : ℝ → M.Carrier) (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f),
      Continuous (curveSpeed g (piecewiseC1Curve_of_contMDiff hf)) := by
  letI := manifold_realSmooth M
  intro f hf
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g z
  convert! continuous_norm_realCurveVelocity g hg hf using 1
  ext t
  rw [underlyingRealTangent_norm,
    realCurveVelocity_chart hf.continuous.continuousAt
      ((contDiffAt_chart_of_contMDiff hf t).differentiableAt (by norm_num))]
  unfold curveSpeed
  rw [realTangentDerivative_eq_chart]
  rfl

theorem exists_smooth_nearMinimizingPath (g : HermitianField M) (hg : MetricSmooth g)
    (x y : M.Carrier) (ε : ℝ) (hε : 0 < ε) :
    letI := manifold_realSmooth M
    ∃ (f : ℝ → M.Carrier), f 0 = x ∧ f 1 = y ∧
      ∃ hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f,
        Continuous (curveSpeed g (piecewiseC1Curve_of_contMDiff hf)) ∧
          curveLength g (piecewiseC1Curve_of_contMDiff hf) < inducedDistance g x y + ε := by
  letI := manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g z
  letI := realEMetricSpace g hg
  have hpos : 0 < inducedDistance g x y + ε :=
    add_pos_of_nonneg_of_pos (inducedDistance_nonneg g hg x y) hε
  have hED : Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y <
      ENNReal.ofReal (inducedDistance g x y + ε) := by
    rw [← inducedDistance_eq_riemannianEDist g hg x y]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (lt_add_of_pos_right _ hε)
  obtain ⟨f, hx, hy, hf, hlen, _, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hED zero_lt_one
  let γ := Yau.LeafProofs.L23Aux.integrableCurve_of_contMDiff g hg hf
  have hL := curveLength_eq_pathELength g γ
  change ENNReal.ofReal (curveLength g γ.1) =
    Manifold.pathELength 𝓘(ℝ, ComplexVector n) f 0 1 at hL
  rw [← hL] at hlen
  exact ⟨f, hx, hy, hf, field_smooth_path_speed_continuous g hg f hf,
    (ENNReal.ofReal_lt_ofReal_iff hpos).mp hlen⟩

end Yau.NodeProofs.C01Aux
