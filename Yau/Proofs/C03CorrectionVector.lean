import Yau.Proofs.C03SourceEnergy

/-! The endpoint velocity and its complex rotation prescribe both real
parameters of the trace-free energy Hessian correction. -/

noncomputable section
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem realMetricInChart_I_self_zero (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget c) (v : ComplexVector n) :
    realMetricInChart h c z (Complex.I • v) v = 0 := by
  simp only [realMetricInChart_apply, underlyingRealRiemannianMetric_inner,
    realTangentEquiv_realChartVec c z (Complex.I • v) hz,
    realTangentEquiv_realChartVec c z v hz, chartVec_complex_smul]
  rw [(h (chartInv c z)).map_smul_left]
  simp [(h (chartInv c z)).self_adjoint]

def energyCorrectionVector (T : ComplexVector n) (D u v : ℝ) : ComplexVector n :=
  (u / D) • T - (v / D) • (Complex.I • T)

theorem energyCorrectionVector_pairings (h : HermitianField M) (c : M.Carrier)
    (z T : ComplexVector n) (hz : z ∈ chartTarget c) (D : ℝ) (hD : D ≠ 0)
    (hT : realMetricInChart h c z T T = D) (u v : ℝ) :
    realMetricInChart h c z T (energyCorrectionVector T D u v) = u ∧
      realMetricInChart h c z T (Complex.I • energyCorrectionVector T D u v) = v := by
  have hcross : realMetricInChart h c z T (Complex.I • T) = 0 := by
    rw [realMetricInChart_symm]
    exact realMetricInChart_I_self_zero h c z hz T
  have hIQ : Complex.I • energyCorrectionVector T D u v =
      (u / D) • (Complex.I • T) + (v / D) • T := by
    unfold energyCorrectionVector
    rw [smul_sub, smul_comm Complex.I (u / D), smul_comm Complex.I (v / D)]
    simp only [smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_one_smul,
      smul_neg, sub_neg_eq_add]
  constructor
  · simp only [energyCorrectionVector, map_sub, map_smul, smul_eq_mul, hT, hcross,
      mul_zero, sub_zero]
    exact div_mul_cancel₀ u hD
  · rw [hIQ]
    simp only [map_add, map_smul, smul_eq_mul, hT, hcross, mul_zero, zero_add]
    exact div_mul_cancel₀ v hD

end Yau.Proofs.C03Aux
