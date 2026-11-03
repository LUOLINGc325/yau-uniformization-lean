import Yau.Witness.CigarField

/-! Direct Levi-Civita curvature of the cigar real metric. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Witness.Cigar

set_option backward.isDefEq.respectTransparency false

open Yau.LeafProofs.L12Aux

theorem cigar_hasFDerivAt_coord (z : V) (a : RIdx 1) :
    HasFDerivAt (fun w : V => realCoord w a) (realCoordCLM a) z := by
  convert! (realCoordCLM a).hasFDerivAt (x := z) using 1
  funext w
  exact (realCoordCLM_apply a w).symm

theorem cigar_hasFDerivAt_denom (z : V) :
    HasFDerivAt cigarDenom
      ((2 * realCoord z (0, 0)) • realCoordCLM (0, 0) +
        (2 * realCoord z (0, 1)) • realCoordCLM (0, 1)) z := by
  have h := ((cigar_hasFDerivAt_coord z (0, 0)).pow 2).const_add 1
  have h' := h.add ((cigar_hasFDerivAt_coord z (0, 1)).pow 2)
  convert! h' using 1
  · funext w
    simp [cigarDenom, cigar_norm_sq_coordinates, realCoord]
    ring
  · simp [nsmul_eq_mul]

theorem cigar_rDeriv_denom (z : V) (a : RIdx 1) :
    rDeriv cigarDenom z a = 2 * realCoord z a := by
  unfold rDeriv
  rw [(cigar_hasFDerivAt_denom z).fderiv]
  rcases a with ⟨i, a⟩
  fin_cases i <;> fin_cases a <;>
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      realCoordCLM_apply, realCoord_realVec]

theorem cigar_rDeriv_inv_denom (z : V) (a : RIdx 1) :
    rDeriv (fun w : V => (cigarDenom w)⁻¹) z a =
      -2 * realCoord z a / cigarDenom z ^ 2 := by
  have h := (hasDerivAt_inv (cigarDenom_pos z).ne').comp_hasFDerivAt z
    (cigar_hasFDerivAt_denom z)
  change HasFDerivAt (fun w : V => (cigarDenom w)⁻¹) _ z at h
  unfold rDeriv
  rw [h.fderiv, ← (cigar_hasFDerivAt_denom z).fderiv]
  change -(cigarDenom z ^ 2)⁻¹ * rDeriv cigarDenom z a = _
  rw [cigar_rDeriv_denom]
  ring

theorem cigar_rDeriv_coord_div_denom (z : V) (a b : RIdx 1) :
    rDeriv (fun w : V => realCoord w b / cigarDenom w) z a =
      (if a = b then 1 else 0) / cigarDenom z -
        2 * realCoord z a * realCoord z b / cigarDenom z ^ 2 := by
  have hq := (hasDerivAt_inv (cigarDenom_pos z).ne').comp_hasFDerivAt z
    (cigar_hasFDerivAt_denom z)
  change HasFDerivAt (fun w : V => (cigarDenom w)⁻¹) _ z at hq
  have h := (cigar_hasFDerivAt_coord z b).fun_mul hq
  change fderiv ℝ (fun w : V => realCoord w b * (cigarDenom w)⁻¹) z (realVec a) = _
  rw [h.fderiv, ← (cigar_hasFDerivAt_denom z).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, realCoordCLM_apply, realCoord_realVec]
  change realCoord z b * (-(cigarDenom z ^ 2)⁻¹ * rDeriv cigarDenom z a) +
    (cigarDenom z)⁻¹ * (if a = b then 1 else 0) = _
  rw [cigar_rDeriv_denom]
  ring

theorem cigar_realMetricFn_inv (x : cigarPlane.Carrier) (z : V) (a b : RIdx 1) :
    (realMetricFn cigarField x z)⁻¹ a b = if a = b then cigarDenom z else 0 := by
  have hG : realMetricFn cigarField x z =
      Matrix.diagonal (fun _ : RIdx 1 => (cigarDenom z)⁻¹) := by
    ext i j
    simp [cigar_realMetricFn, Matrix.diagonal_apply]
  have hInv : (Matrix.diagonal (fun _ : RIdx 1 => (cigarDenom z)⁻¹))⁻¹ =
      Matrix.diagonal (fun _ : RIdx 1 => cigarDenom z) := by
    apply Matrix.inv_eq_left_inv
    simp [Matrix.diagonal_mul_diagonal, (cigarDenom_pos z).ne']
  rw [hG, hInv]
  simp [Matrix.diagonal_apply]

theorem cigar_rDeriv_realMetricFn (x : cigarPlane.Carrier) (z : V)
    (d a b : RIdx 1) :
    rDeriv (fun w => realMetricFn cigarField x w a b) z d =
      if a = b then -2 * realCoord z d / cigarDenom z ^ 2 else 0 := by
  by_cases hab : a = b
  · simpa only [cigar_realMetricFn, hab, ↓reduceIte] using cigar_rDeriv_inv_denom z d
  · simp [cigar_realMetricFn, hab, rDeriv]

theorem cigar_christoffel (x : cigarPlane.Carrier) (z : V) (c a b : RIdx 1) :
    christoffel cigarField x z c a b =
      -((if c = b then realCoord z a else 0) +
        (if c = a then realCoord z b else 0) -
        (if a = b then realCoord z c else 0)) / cigarDenom z := by
  unfold christoffel
  simp_rw [cigar_realMetricFn_inv, cigar_rDeriv_realMetricFn]
  rcases c with ⟨i, c⟩
  rcases a with ⟨j, a⟩
  rcases b with ⟨k, b⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases c <;> fin_cases a <;> fin_cases b <;>
      simp [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  all_goals field_simp [(cigarDenom_pos z).ne'] <;> ring

theorem cigar_rDeriv_neg_coord_div_denom (z : V) (a b : RIdx 1) :
    rDeriv (fun w : V => -(realCoord w b / cigarDenom w)) z a =
      -((if a = b then 1 else 0) / cigarDenom z -
        2 * realCoord z a * realCoord z b / cigarDenom z ^ 2) := by
  simp only [neg_div, rDeriv, fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  exact congrArg Neg.neg (cigar_rDeriv_coord_div_denom z a b)

theorem cigar_rDeriv_christoffel (x : cigarPlane.Carrier) (z : V)
    (d c a b : RIdx 1) :
    rDeriv (fun w => christoffel cigarField x w c a b) z d =
      -((if c = b then
          (if d = a then 1 else 0) / cigarDenom z -
            2 * realCoord z d * realCoord z a / cigarDenom z ^ 2 else 0) +
        (if c = a then
          (if d = b then 1 else 0) / cigarDenom z -
            2 * realCoord z d * realCoord z b / cigarDenom z ^ 2 else 0) -
        (if a = b then
          (if d = c then 1 else 0) / cigarDenom z -
            2 * realCoord z d * realCoord z c / cigarDenom z ^ 2 else 0)) := by
  rcases d with ⟨h, d⟩
  rcases c with ⟨i, c⟩
  rcases a with ⟨j, a⟩
  rcases b with ⟨k, b⟩
  fin_cases h <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases d <;> fin_cases c <;> fin_cases a <;> fin_cases b <;>
      simp [cigar_christoffel, neg_div, cigar_rDeriv_coord_div_denom,
        cigar_rDeriv_neg_coord_div_denom]

theorem cigar_riemannCoeff (x : cigarPlane.Carrier) (z : V) (i j k l : RIdx 1) :
    riemannCoeff cigarField x z i j k l =
      (2 / cigarDenom z ^ 2) *
        ((if j = k then 1 else 0) * (if l = i then 1 else 0) -
          (if i = k then 1 else 0) * (if l = j then 1 else 0)) := by
  unfold riemannCoeff
  simp_rw [cigar_rDeriv_christoffel, cigar_christoffel]
  have hq : cigarDenom z = 1 + realCoord z (0, 0) ^ 2 + realCoord z (0, 1) ^ 2 := by
    simp [cigarDenom, cigar_norm_sq_coordinates, realCoord, add_assoc]
  rcases i with ⟨a, i⟩
  rcases j with ⟨b, j⟩
  rcases k with ⟨c, k⟩
  rcases l with ⟨d, l⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  all_goals field_simp [(cigarDenom_pos z).ne'] <;> nlinarith [hq]

theorem cigar_real_inner_coordinates (u v : V) :
    inner ℝ u v = realCoord u (0, 0) * realCoord v (0, 0) +
      realCoord u (0, 1) * realCoord v (0, 1) := by
  simp [PiLp.inner_apply, Fin.sum_univ_one, real_inner_eq_re_inner ℂ,
    realCoord, RCLike.inner_apply, Complex.mul_re]
  ring

theorem cigar_paperRm (z : cigarPlane.Carrier)
    (u v s t : TangentVector cigarPlane z) :
    paperRm cigarField z u v s t =
      (2 / cigarDenom z ^ 3) *
        (inner ℝ (cigarModelVec z v) (cigarModelVec z s) *
          inner ℝ (cigarModelVec z u) (cigarModelVec z t) -
          inner ℝ (cigarModelVec z u) (cigarModelVec z s) *
          inner ℝ (cigarModelVec z v) (cigarModelVec z t)) := by
  simp only [paperRm, cigar_chartPt, cigar_tangentCoords,
    cigar_realMetricFn, cigar_riemannCoeff, cigar_real_inner_coordinates]
  simp [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem cigar_complex_line_gram (u v : V) :
    inner ℝ u v ^ 2 + inner ℝ u (Complex.I • v) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  simp [cigar_real_inner_coordinates, cigar_norm_sq_coordinates, realCoord,
    PiLp.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im]
  ring

theorem cigarModelVec_smul (z : cigarPlane.Carrier) (a : ℂ)
    (u : TangentVector cigarPlane z) :
    cigarModelVec z (a • u) = a • cigarModelVec z u := by
  exact (tangentSpaceCastModel (ComplexModel 1) z).map_smul a u

theorem cigar_paperBisectionalNumerator (z : cigarPlane.Carrier)
    (u v : TangentVector cigarPlane z) :
    paperBisectionalNumerator cigarField z u v =
      2 * ‖cigarModelVec z u‖ ^ 2 * ‖cigarModelVec z v‖ ^ 2 / cigarDenom z ^ 3 := by
  unfold paperBisectionalNumerator paperComplexStructure
  rw [cigar_paperRm, cigar_paperRm, cigarModelVec_smul]
  simp only [real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  rw [real_inner_comm (cigarModelVec z u) (cigarModelVec z v),
    real_inner_comm (cigarModelVec z u) (Complex.I • cigarModelVec z v)]
  have hGram := cigar_complex_line_gram (cigarModelVec z u) (cigarModelVec z v)
  linear_combination -(2 / cigarDenom z ^ 3) * hGram

theorem cigarModelVec_ne_zero (z : cigarPlane.Carrier)
    {u : TangentVector cigarPlane z} (hu : u ≠ 0) : cigarModelVec z u ≠ 0 := by
  intro h
  apply hu
  apply (tangentSpaceCastModel (ComplexModel 1) z).injective
  simpa only [map_zero] using h

theorem cigar_paperPositive : PaperPositiveBisectional cigarField := by
  intro z u v hu hv
  change 0 < paperBisectionalNumerator cigarField z u v
  rw [cigar_paperBisectionalNumerator]
  exact div_pos
    (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr (cigarModelVec_ne_zero z hu))))
      (sq_pos_of_pos (norm_pos_iff.mpr (cigarModelVec_ne_zero z hv))))
    (pow_pos (cigarDenom_pos z) 3)

theorem cigar_paperHBC (z : cigarPlane.Carrier)
    (u v : TangentVector cigarPlane z) (hu : u ≠ 0) (hv : v ≠ 0) :
    paperHolomorphicBisectionalCurvature cigarField z u v = 2 / cigarDenom z := by
  unfold paperHolomorphicBisectionalCurvature
  rw [cigar_paperBisectionalNumerator, cigar_hermitianNormSq, cigar_hermitianNormSq]
  have hq := (cigarDenom_pos z).ne'
  have hu' := norm_ne_zero_iff.mpr (cigarModelVec_ne_zero z hu)
  have hv' := norm_ne_zero_iff.mpr (cigarModelVec_ne_zero z hv)
  field_simp [hq, hu', hv']

theorem cigar_gaussian_sectional_quotient (z : cigarPlane.Carrier) :
    let e₀ := (tangentSpaceCastModel (ComplexModel 1) z).symm (realVec (0, 0))
    let e₁ := (tangentSpaceCastModel (ComplexModel 1) z).symm (realVec (0, 1))
    paperRm cigarField z e₀ e₁ e₁ e₀ /
      (realMetricFn cigarField z z (0, 0) (0, 0) *
        realMetricFn cigarField z z (0, 1) (0, 1) -
        realMetricFn cigarField z z (0, 0) (0, 1) ^ 2) = 2 / cigarDenom z := by
  dsimp only
  rw [cigar_paperRm]
  have hnorm (a : RIdx 1) : ‖realVec a‖ = 1 := by
    rcases a with ⟨i, a⟩
    fin_cases i <;> fin_cases a <;> simp [realVec, norm_smul, PiLp.norm_single]
  simp [cigarModelVec, cigar_realMetricFn, cigar_real_inner_coordinates,
    realCoord_realVec, hnorm] <;>
    field_simp [(cigarDenom_pos z).ne'] <;> ring

end Yau.Witness.Cigar
