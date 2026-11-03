import Yau.Proofs.G04TraceSmooth

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def chartFormMatrix (A : RealForm M 2) (x : M.Carrier) (z : ComplexVector n) :
    Matrix (RIdx n) (RIdx n) ℝ := fun a b => formComponents A x z ![a, b]

theorem formComponents_degree_two (A : RealForm M 2) (x : M.Carrier) (z : ComplexVector n)
    (I : Fin 2 → RIdx n) : formComponents A x z I = chartFormMatrix A x z (I 0) (I 1) := by
  unfold chartFormMatrix
  congr 1
  funext r
  fin_cases r <;> rfl

theorem chartFormMatrix_apply (A : RealForm M 2) (x : M.Carrier) (z : ComplexVector n)
    (a b : RIdx n) : chartFormMatrix A x z a b = L03.chartForm A x z ![realVec a, realVec b] := by
  unfold chartFormMatrix
  rw [← L03.chartForm_apply_basis]
  congr 1
  ext r
  fin_cases r <;> rfl

theorem chartFormMatrix_skew (A : RealForm M 2) (x : M.Carrier) (z : ComplexVector n)
    (a b : RIdx n) : chartFormMatrix A x z b a = -chartFormMatrix A x z a b := by
  rw [chartFormMatrix_apply, chartFormMatrix_apply]
  exact alternating_two_swap _ _ _

theorem formInner_chart_trace (h : HermitianField M) (A B : RealForm M 2)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    formInner h A B (chartInv x z) = -(1 / 2 : ℝ) * Matrix.trace
      ((realMetricFn h x z)⁻¹ * chartFormMatrix A x z *
        (realMetricFn h x z)⁻¹ * chartFormMatrix B x z) := by
  rw [L03.formInner_chartInv_eq_tensorPairing h A B x hz]
  have he : (Nat.factorial 2 : ℝ)⁻¹ * L03.tensorCoefficientPairing
      (realMetricFn h x z)⁻¹ (formComponents A x z) (formComponents B x z) =
      (1 / 2 : ℝ) * ∑ a, ∑ b, ∑ c, ∑ d, chartFormMatrix A x z a b * chartFormMatrix B x z c d *
        (realMetricFn h x z)⁻¹ a c * (realMetricFn h x z)⁻¹ b d := by
    unfold L03.tensorCoefficientPairing
    simp only [formComponents_degree_two, L23Aux.sum_tensor_cons,
      Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.cons_zero, Fin.cons_one, Fin.cons_succ,
      Fintype.sum_unique, Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, mul_one]
    congr 1
    · norm_num
    · apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      ring
  rw [he, alternating_contraction_trace _ _ _ (L12Aux.realMetricFn_isSymm h x z).inv
    (chartFormMatrix_skew B x z)]
  ring

theorem omegaForm_chart_matrix (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    chartFormMatrix (omegaForm h) x z = -(realMetricFn h x z * L12Aux.jMatrix n) := by
  ext a b
  change formComponents (omegaForm h) x z ![a,b] = _
  rw [omegaForm_components]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.neg_apply, L12Aux.mul_jMatrix]
  have he := L12Aux.kahlerFormFn_jIndex_right h x z a (L12Aux.jIndex n b)
  rw [L12Aux.jIndex_involutive, L12Aux.jSign_jIndex] at he
  simpa only [neg_mul] using he

theorem symmetric_trace_KJ (G K : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.IsSymm) :
    Matrix.trace (G * K * L12Aux.jMatrix n) =
      ∑ a, ∑ b, G a b * L12Aux.jSign b * K a (L12Aux.jIndex n b) := by
  rw [Matrix.mul_assoc]
  change (∑ a, ∑ b, G a b * (K * L12Aux.jMatrix n) b a) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hG.apply a b, L12Aux.mul_jMatrix]
  ring

theorem trace_in_chart (h : HermitianField M) (A : RealForm M 2) (hA : RealOneOne A)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    inChart x (formTrace h A) z = (1 / 2 : ℝ) * ∑ a, ∑ b,
      (realMetricFn h x z)⁻¹ a b * L12Aux.jSign b * chartFormMatrix A x z a (L12Aux.jIndex n b) := by
  change formTrace h A (chartInv x z) = _
  rw [formTrace_eq_inner_omega h A hA, formInner_chart_trace h A (omegaForm h) x hz,
    omegaForm_chart_matrix]
  have hunit : IsUnit (realMetricFn h x z).det :=
    isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef h x z hz).det_pos.ne'
  have hp : (realMetricFn h x z)⁻¹ * chartFormMatrix A x z * (realMetricFn h x z)⁻¹ *
      -(realMetricFn h x z * L12Aux.jMatrix n) =
      -((realMetricFn h x z)⁻¹ * chartFormMatrix A x z * L12Aux.jMatrix n) := by
    calc
      _ = -((realMetricFn h x z)⁻¹ * chartFormMatrix A x z *
        ((realMetricFn h x z)⁻¹ * realMetricFn h x z) * L12Aux.jMatrix n) := by noncomm_ring
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
  rw [hp, Matrix.trace_neg, symmetric_trace_KJ _ _ (L12Aux.realMetricFn_isSymm h x z).inv]
  ring

end Yau.NodeProofs.G04Aux
