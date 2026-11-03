import Yau.Proofs.P04CompactQuadraticBounds
import Yau.Proofs.P03RealMetricLeviMatrix
import Yau.Proofs.E01Matrix

/-! Compact bounds on actual coordinate metrics, including empty unit spheres. -/
noncomputable section
open Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.Proofs.C03Aux.TargetCharts
open Yau Yau.Blueprint Yau.LeafProofs Yau.Proofs.P04Aux
open Yau.LeafProofs.L12Aux
open Yau.NodeProofs.P03Aux Yau.NodeProofs.E01Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem matrix_lower_of_quadratic (A : Herm n) (hA : A.IsHermitian) (d : ℝ)
    (h : ∀ v : ComplexVector n, d * ‖v‖ ^ 2 ≤ matrixQuadratic A v) :
    HermLE ((d : ℂ) • (1 : Herm n)) A := by
  apply matrix_sub_real_smul_posSemidef A 1 hA (by simp) d
  intro v
  have H := h (WithLp.toLp 2 v)
  have ho := ellipsoidQuadratic_one (WithLp.toLp 2 v)
  change (star v ⬝ᵥ ((1 : Herm n) *ᵥ v)).re = ‖WithLp.toLp 2 v‖ ^ 2 at ho
  rw [ho]
  exact H

theorem matrix_upper_of_quadratic (A : Herm n) (hA : A.IsHermitian) (U : ℝ)
    (h : ∀ v : ComplexVector n, matrixQuadratic A v ≤ U * ‖v‖ ^ 2) :
    HermLE A ((U : ℂ) • (1 : Herm n)) := by
  have hh : ((U : ℂ) • (1 : Herm n)).IsHermitian :=
    (Matrix.isHermitian_one).smul (by simp [IsSelfAdjoint])
  have H := matrix_sub_real_smul_posSemidef ((U : ℂ) • (1 : Herm n)) A hh hA 1
    (fun v => by
      have hb := h (WithLp.toLp 2 v)
      have he := ellipsoidQuadratic_real_smul U (1 : Herm n) (WithLp.toLp 2 v)
      rw [ellipsoidQuadratic_one] at he
      change (star v ⬝ᵥ (((U : ℂ) • (1 : Herm n)) *ᵥ v)).re =
        U * ‖WithLp.toLp 2 v‖ ^ 2 at he
      rw [one_mul, he]
      exact hb)
  simpa only [HermLE, Complex.ofReal_one, one_smul] using H

theorem compact_chart_quadratic_bounds (g : SmoothMetric M) (a : M.Carrier)
    (S : Set (ComplexVector n)) (hS : IsCompact S) (hSt : S ⊆ chartTarget a) :
    ∃ d U : ℝ, 0 < d ∧ 0 < U ∧ ∀ z ∈ S, ∀ v : ComplexVector n,
      d * ‖v‖ ^ 2 ≤ matrixQuadratic (hMat g.form a z) v ∧
      matrixQuadratic (hMat g.form a z) v ≤ U * ‖v‖ ^ 2 := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let A : S → Herm n := fun z => hMat g.form a z
  have hA : Continuous A := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuousOn_iff_continuous_restrict.mp
      ((L12Aux.hMat_contDiffOn g a i j).continuousOn.mono hSt)
  obtain ⟨d, hd, hlo⟩ := compact_posDef_uniform_lower_bound A hA
    (fun z => L12Aux.hMat_posDef g.form a z (hSt z.property))
  obtain ⟨C, hC, hup⟩ := compact_matrix_uniform_quadratic_bound A hA
  refine ⟨d, C + 1, hd, by positivity, ?_⟩
  intro z hz v
  refine ⟨hlo ⟨z, hz⟩ v, ?_⟩
  exact (le_abs_self _).trans ((hup ⟨z, hz⟩ v).trans
    (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) (sq_nonneg _)))

theorem realMetric_le_of_quadratic (g : SmoothMetric M) (a : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget a) (U : ℝ)
    (hU : ∀ v : ComplexVector n, matrixQuadratic (hMat g.form a z) v ≤ U * ‖v‖ ^ 2)
    (v : ComplexVector n) :
    realMetricInChart g.form a z v v ≤ 2 * U * ‖v‖ ^ 2 := by
  rw [realMetricInChart_eq_two_re_hMat g.form a hz]
  have hb := hU v
  change (star (WithLp.ofLp v) ⬝ᵥ (hMat g.form a z *ᵥ WithLp.ofLp v)).re ≤ _ at hb
  nlinarith

end Yau.Proofs.C03Aux.TargetCharts
