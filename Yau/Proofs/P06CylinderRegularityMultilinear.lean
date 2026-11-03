import Yau.LeafProofs.L16MixedSobolev

/-! Coordinate estimates imply the literal full Fréchet operator norm,
including on the default max-norm product used by the original contract. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff BigOperators

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.LeafProofs.L16Aux

theorem multilinear_basis_expansion {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : Basis ι ℝ E) {m : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F) (v : Fin m → E) :
    T v = ∑ w : Fin m → ι, (∏ j, b.repr (v j) (w j)) • T (fun j => b (w j)) := by
  classical
  conv_lhs => rw [show v = (fun j => ∑ i, b.repr (v j) i • b i) by
    funext j; exact (b.sum_repr (v j)).symm]
  change T.toMultilinearMap (fun j => ∑ i, b.repr (v j) i • b i) = _
  rw [T.toMultilinearMap.map_sum]
  simp_rw [T.toMultilinearMap.map_smul_univ]
  rfl

theorem multilinear_norm_le_basis_sum {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : Basis ι ℝ E) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ v i, |b.repr v i| ≤ K * ‖v‖) {m : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F) :
    ‖T‖ ≤ K^m * ∑ w : Fin m → ι, ‖T (fun j => b (w j))‖ := by
  classical
  apply T.opNorm_le_bound (mul_nonneg (pow_nonneg hK _)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _))
  intro v
  rw [multilinear_basis_expansion b T v]
  calc
    _ ≤ ∑ w : Fin m → ι,
        ‖(∏ j, b.repr (v j) (w j)) • T (fun j => b (w j))‖ := norm_sum_le _ _
    _ ≤ ∑ w : Fin m → ι, (K^m * ∏ j, ‖v j‖) * ‖T (fun j => b (w j))‖ := by
      apply Finset.sum_le_sum
      intro w _
      rw [norm_smul, norm_prod]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        _ ≤ ∏ j : Fin m, K * ‖v j‖ := by
          apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro j _
          simpa only [Real.norm_eq_abs] using hb (v j) (w j)
        _ = _ := by rw [Finset.prod_mul_distrib]; simp
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem multilinear_pi_norm_le_sum {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin m => ι → ℝ) F) :
    ‖T‖ ≤ ∑ w : Fin m → ι, ‖T (fun j => Pi.single (w j) 1)‖ := by
  have h := multilinear_norm_le_basis_sum (Pi.basisFun ℝ ι) (K := 1) (by norm_num)
    (fun v i => by simpa only [Pi.basisFun_repr, one_mul, Real.norm_eq_abs] using norm_le_pi_norm v i) T
  simpa only [one_pow, one_mul, Pi.basisFun_apply] using h

theorem multilinear_pi_norm_sq_le_sum {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin m => ι → ℝ) F) :
    ‖T‖^2 ≤ (Fintype.card (Fin m → ι) : ℝ) *
      ∑ w : Fin m → ι, ‖T (fun j => Pi.single (w j) 1)‖^2 := by
  have h := multilinear_pi_norm_le_sum T
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin m → ι => (1 : ℝ)) (fun w => ‖T (fun j => Pi.single (w j) 1)‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hCS
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans hCS

theorem coordinateWordDerivative_append {D : ℕ} (f : (Fin D → ℝ) → ℝ)
    (v w : List (Fin D)) :
    coordinateWordDerivative (coordinateWordDerivative f w) v =
      coordinateWordDerivative f (v ++ w) := by
  induction v with
  | nil => rfl
  | cons i v ih => simp only [coordinateWordDerivative, List.cons_append, ih]

theorem coordinateWordDerivative_ofFn {D m : ℕ} {f : (Fin D → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (w : Fin m → Fin D) (x : Fin D → ℝ) :
    coordinateWordDerivative f (List.ofFn w) x =
      iteratedFDeriv ℝ m f x (fun j => Pi.single (w j) 1) := by
  induction m generalizing x with
  | zero => simp only [List.ofFn_zero, coordinateWordDerivative_nil, iteratedFDeriv_zero_apply]
  | succ m ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (coordinateWordDerivative f (List.ofFn (Fin.tail w))) x
      (Pi.single (w 0) 1) = _
    have hFun : coordinateWordDerivative f (List.ofFn (Fin.tail w)) =
        fun y => iteratedFDeriv ℝ m f y (fun j => Pi.single (Fin.tail w j) 1) :=
      funext (fun y => ih (Fin.tail w) y)
    rw [hFun]
    have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ m f) x := hf.contDiffAt.differentiableAt_iteratedFDeriv
      (m := m) (by exact_mod_cast ENat.natCast_lt_top m)
    exact (hD.iteratedFDeriv_succ_apply_left' (m := fun j => Pi.single (w j) 1)).symm

/-- Mixed Sobolev controls the full operator norm on a finite max-norm
coordinate space. Only words of length at most m+D occur on its right. -/
theorem iteratedFDeriv_sq_le_mixed_word_energy {D m : ℕ}
    {f : (Fin D → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (x : Fin D → ℝ) :
    ‖iteratedFDeriv ℝ m f x‖^2 ≤ (Fintype.card (Fin m → Fin D) : ℝ) *
      ∑ w : Fin m → Fin D, ∑ s : Finset (Fin D),
        ∫ y, (coordinateWordDerivative f (s.sort (· ≤ ·) ++ List.ofFn w) y)^2 := by
  have hNorm := multilinear_pi_norm_sq_le_sum (iteratedFDeriv ℝ m f x)
  refine hNorm.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  apply Finset.sum_le_sum
  intro w _
  have hS := sq_le_sum_integral_sq_mixedDerivative
    (contDiff_coordinateWordDerivative hf (List.ofFn w))
    (hasCompactSupport_coordinateWordDerivative hcf (List.ofFn w)) x
  rw [coordinateWordDerivative_ofFn hf] at hS
  simpa only [Real.norm_eq_abs, sq_abs, mixedDerivative,
    coordinateWordDerivative_append] using hS

theorem iteratedFDeriv_norm_le_coordinate_norm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {D m : ℕ}
    (e : E ≃L[ℝ] (Fin D → ℝ)) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (p : E) :
    ‖iteratedFDeriv ℝ m f p‖ ≤
      ‖iteratedFDeriv ℝ m (f ∘ e.symm) (e p)‖ * ‖e.toContinuousLinearMap‖^m := by
  have hfc : ContDiff ℝ ∞ (f ∘ e.symm) := hf.comp e.symm.contDiff
  have hComp := e.toContinuousLinearMap.iteratedFDeriv_comp_right hfc p (i := m) (by simp)
  have hFun : (f ∘ e.symm) ∘ e.toContinuousLinearMap = f := by
    funext q
    simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, e.symm_apply_apply]
  rw [hFun] at hComp
  rw [hComp]
  simpa only [ContinuousLinearEquiv.coe_coe, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ m (f ∘ e.symm) (e p)).norm_compContinuousLinearMap_le
      (fun _ : Fin m => e.toContinuousLinearMap)

theorem iteratedFDeriv_sq_le_coordinate_mixed_energy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {D m : ℕ}
    (e : E ≃L[ℝ] (Fin D → ℝ)) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (p : E) :
    ‖iteratedFDeriv ℝ m f p‖^2 ≤
      ‖e.toContinuousLinearMap‖^(2*m) * (Fintype.card (Fin m → Fin D) : ℝ) *
        ∑ w : Fin m → Fin D, ∑ s : Finset (Fin D), ∫ y,
          (coordinateWordDerivative (f ∘ e.symm) (s.sort (· ≤ ·) ++ List.ofFn w) y)^2 := by
  have h1 := iteratedFDeriv_norm_le_coordinate_norm (m := m) e hf p
  have h2 := iteratedFDeriv_sq_le_mixed_word_energy (m := m)
    (hf.comp e.symm.contDiff) (hcf.comp_homeomorph e.symm.toHomeomorph) (e p)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hmul := mul_le_mul_of_nonneg_right h2 (sq_nonneg (‖e.toContinuousLinearMap‖^m))
  rw [mul_pow] at hsq
  have hpow : (‖e.toContinuousLinearMap‖^m)^2 = ‖e.toContinuousLinearMap‖^(2*m) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hpow] at hsq hmul
  nlinarith

end Yau.NodeProofs.P06Aux.CylinderReg
