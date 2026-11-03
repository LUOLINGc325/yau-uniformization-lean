import Yau.Proofs.P06WeitzenbockHermitian
import Yau.Proofs.P06WeitzenbockQuadratic

noncomputable section
open scoped Matrix ComplexOrder Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau G01Aux G04Aux Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem coefficientPairing_two_matrix (H K L : Matrix (RIdx n) (RIdx n) ℝ) :
    L03.tensorCoefficientPairing H (fun I : Fin 2 → RIdx n => K (I 0) (I 1))
      (fun I => L (I 0) (I 1)) =
      ∑ a, ∑ b, ∑ c, ∑ d, K a b * L c d * H a c * H b d := by
  simp only [L03.tensorCoefficientPairing, L23Aux.sum_tensor_cons, Fin.prod_univ_succ,
    Fin.prod_univ_zero, Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Fintype.sum_unique, mul_one]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem coefficientPairing_two_trace (H K L : Matrix (RIdx n) (RIdx n) ℝ)
    (hH : H.IsSymm) (hL : ∀ a b, L b a = -L a b) :
    L03.tensorCoefficientPairing H (fun I : Fin 2 → RIdx n => K (I 0) (I 1))
      (fun I => L (I 0) (I 1)) = -Matrix.trace (H * K * H * L) := by
  rw [coefficientPairing_two_matrix, alternating_contraction_trace H K L hH hL]

theorem raw_form_pairing (H Q B : Matrix (Fin n) (Fin n) ℂ) :
    -(1 / 2 : ℝ) * Matrix.trace
      (((1 / 2 : ℝ) • rawReal H) * ((-2 : ℝ) • (rawReal Q * L12Aux.jMatrix n)) *
        ((1 / 2 : ℝ) • rawReal H) * ((-2 : ℝ) • (rawReal B * L12Aux.jMatrix n))) =
      (Matrix.trace (H * Q * H * B)).re := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num only [show (1 / 2 : ℝ) * (-2) * (1 / 2) * (-2) = 1 by norm_num, one_smul]
  have he : rawReal H * (rawReal Q * L12Aux.jMatrix n) *
      rawReal H * (rawReal B * L12Aux.jMatrix n) = -rawReal (H * Q * H * B) := by
    calc
      _ = rawReal H * rawReal Q * (L12Aux.jMatrix n * rawReal H) *
          rawReal B * L12Aux.jMatrix n := by noncomm_ring
      _ = rawReal H * rawReal Q * (rawReal H * L12Aux.jMatrix n) *
          rawReal B * L12Aux.jMatrix n := by rw [rawReal_commute_J]
      _ = rawReal H * rawReal Q * rawReal H *
          (L12Aux.jMatrix n * rawReal B) * L12Aux.jMatrix n := by noncomm_ring
      _ = rawReal H * rawReal Q * rawReal H *
          (rawReal B * L12Aux.jMatrix n) * L12Aux.jMatrix n := by rw [rawReal_commute_J]
      _ = -(rawReal H * rawReal Q * rawReal H * rawReal B) := by
        simp only [Matrix.mul_assoc, L12Aux.jMatrix_sq, Matrix.mul_neg, Matrix.mul_one]
      _ = _ := by simp only [rawReal_mul]
  rw [he, Matrix.trace_neg, rawReal_trace]
  ring

theorem curvaturePair_eq_hermitian_trace_of_symmetries
    (g : SmoothMetric M) (hk : IsKahler g) (A B : RealForm M 2)
    (hA : RealOneOne A) (hB : RealOneOne B) (x : M.Carrier)
    (hstar : ∀ i j k l, star (chernCurvature g.form x i j k l) =
      chernCurvature g.form x j i l k)
    (hpair : ∀ i j k l, chernCurvature g.form x i j k l =
      chernCurvature g.form x k l i j) :
    curvaturePair g.form A B x =
      (Matrix.trace ((gMat g.form x)⁻¹ * hermitianCurvatureReaction g.form A x *
        (gMat g.form x)⁻¹ * formHermitianMatrix B x)).re := by
  have hQ := curvatureTwoMatrix_eq_raw_reaction_of_symmetries g hk A hA x hstar hpair
  have hQc : curvatureTwoComponents g.form A x (chartPt x x) = fun I =>
      ((-2 : ℝ) • (rawReal (hermitianCurvatureReaction g.form A x) * L12Aux.jMatrix n)) (I 0) (I 1) := by
    funext I
    have hI : I = ![I 0,I 1] := by funext i; fin_cases i <;> rfl
    have he := congrArg (fun K : Matrix (RIdx n) (RIdx n) ℝ => K (I 0) (I 1)) hQ
    simpa only [← hI] using he
  have hBc : formComponents B x (chartPt x x) = fun I => realFormMatrix B x (I 0) (I 1) := by
    funext I
    exact formComponents_center_pair B x I
  rw [curvaturePair, chartCurvaturePair, hBc, hQc, L03.tensorCoefficientPairing_transpose,
    (L12Aux.realMetricFn_isSymm g.form x (chartPt x x)).inv,
    coefficientPairing_two_trace _ _ _
      (L12Aux.realMetricFn_isSymm g.form x (chartPt x x)).inv (realFormMatrix_skew B x)]
  rw [G01Aux.realMetricFn_inverse_eq g.form x (chartPt x x) (mem_extChartAt_target x),
    realFormMatrix_eq_raw B hB x]
  simpa only [gMat, mul_neg, neg_mul] using
    (raw_form_pairing ((gMat g.form x)⁻¹) (hermitianCurvatureReaction g.form A x)
      (formHermitianMatrix B x))

end Yau.NodeProofs.P06Weitzenbock
