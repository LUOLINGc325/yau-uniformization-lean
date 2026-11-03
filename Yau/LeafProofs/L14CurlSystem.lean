import Yau.LeafProofs.L14WeightedLocalSystem

noncomputable section
open scoped Topology ContDiff
open MeasureTheory Filter Module
open Yau

namespace Yau.LeafProofs.L14Aux

def barDirectionalCoefficient {n : ℕ} (i : Fin n) (p : RIdx n) : ℂ :=
  if p.1 = i then (if p.2 = 0 then 1 / 2 else Complex.I / 2) else 0

theorem sum_barDirectionalCoefficient {n : ℕ} (i : Fin n) (D : RIdx n → ℂ) :
    (∑ p : RIdx n, barDirectionalCoefficient i p * D p) =
      (1 / 2 : ℂ) * (D (i, 0) + Complex.I * D (i, 1)) := by
  classical
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, barDirectionalCoefficient]
  simp only [ite_true, Fin.isValue, one_ne_zero, ite_false, ite_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ]
  ring

theorem sum_barDirectional_fderiv {n : ℕ} (i : Fin n) (f : ComplexVector n → ℂ) (z : ComplexVector n) :
    (∑ p : RIdx n, barDirectionalCoefficient i p * fderiv ℝ f z (realVec p)) =
      wirtBar f z (stdVec i) := by
  rw [sum_barDirectionalCoefficient]
  simp only [wirtBar, realVec, stdVec, ite_true, one_smul]
  norm_num

theorem sum_barDirectional_ofReal_fderiv {n : ℕ} (i : Fin n) (ψ : ComplexVector n → ℝ)
    (z : ComplexVector n) (hψ : DifferentiableAt ℝ ψ z) :
    (∑ p : RIdx n, barDirectionalCoefficient i p * (fderiv ℝ ψ z (realVec p) : ℂ)) =
      wirtBar (fun w => Complex.ofReal (ψ w)) z (stdVec i) := by
  have he := (Complex.ofRealCLM.hasFDerivAt.comp z hψ.hasFDerivAt).fderiv
  change fderiv ℝ (fun w => Complex.ofReal (ψ w)) z = Complex.ofRealCLM.comp (fderiv ℝ ψ z) at he
  rw [← sum_barDirectional_fderiv, he]
  rfl

theorem sum_ite_barDirectionalCoefficient {n : ℕ} (P : Prop) [Decidable P]
    (i : Fin n) (D : RIdx n → ℂ) :
    (∑ p : RIdx n, (if P then barDirectionalCoefficient i p else 0) * D p) =
      if P then ∑ p : RIdx n, barDirectionalCoefficient i p * D p else 0 := by
  by_cases h : P <;> simp only [h, ite_true, ite_false, zero_mul, Finset.sum_const_zero]

def curlFirstOrderDerivative {n r : ℕ} (k : (Fin n × Fin n) × Fin r)
    (c : Fin n × Fin r) (p : RIdx n) (_z : ComplexVector n) : ℂ :=
  (if c = (k.1.2, k.2) then barDirectionalCoefficient k.1.1 p else 0) -
    (if c = (k.1.1, k.2) then barDirectionalCoefficient k.1.2 p else 0)

def curlFirstOrderValue {n r : ℕ} (_k : (Fin n × Fin n) × Fin r)
    (_c : Fin n × Fin r) (_z : ComplexVector n) : ℂ := 0

theorem curlFirstOrder_formal_test_row {n r : ℕ} (k : (Fin n × Fin n) × Fin r)
    (c : Fin n × Fin r) (ψ : ComplexVector n → ℝ) (z : ComplexVector n)
    (hψ : DifferentiableAt ℝ ψ z) :
    (-(∑ p : RIdx n,
      (curlFirstOrderDerivative k c p z * (fderiv ℝ ψ z (realVec p) : ℂ) +
        fderiv ℝ (curlFirstOrderDerivative k c p) z (realVec p) * (ψ z : ℂ))) +
      curlFirstOrderValue k c z * (ψ z : ℂ)) =
    -(if c = (k.1.2, k.2) then wirtBar (fun w => Complex.ofReal (ψ w)) z (stdVec k.1.1) else 0) +
      (if c = (k.1.1, k.2) then wirtBar (fun w => Complex.ofReal (ψ w)) z (stdVec k.1.2) else 0) := by
  classical
  have hd (p : RIdx n) : fderiv ℝ (curlFirstOrderDerivative k c p) z (realVec p) = 0 := by
    unfold curlFirstOrderDerivative
    simp
  simp only [hd, mul_zero, zero_mul, add_zero, curlFirstOrderValue]
  simp only [curlFirstOrderDerivative, sub_mul, Finset.sum_sub_distrib,
    sum_ite_barDirectionalCoefficient, sum_barDirectional_ofReal_fderiv _ ψ z hψ]
  ring

theorem curlFirstOrder_apply {n r : ℕ} (F : ComplexVector n → (Fin n × Fin r) → ℂ)
    (z : ComplexVector n) (k : (Fin n × Fin n) × Fin r) :
    complexFirstOrderSystemApply realVec curlFirstOrderDerivative curlFirstOrderValue F z k =
      wirtBar (fun w => F w (k.1.2, k.2)) z (stdVec k.1.1) -
      wirtBar (fun w => F w (k.1.1, k.2)) z (stdVec k.1.2) := by
  classical
  have hterm (c : Fin n × Fin r) :
      (∑ p : RIdx n, curlFirstOrderDerivative k c p z * fderiv ℝ (fun w => F w c) z (realVec p)) =
      (if c = (k.1.2, k.2) then wirtBar (fun w => F w c) z (stdVec k.1.1) else 0) -
      (if c = (k.1.1, k.2) then wirtBar (fun w => F w c) z (stdVec k.1.2) else 0) := by
    simp only [curlFirstOrderDerivative, sub_mul, Finset.sum_sub_distrib,
      sum_ite_barDirectionalCoefficient, sum_barDirectional_fderiv]
  simp only [complexFirstOrderSystemApply, curlFirstOrderValue, zero_mul, add_zero, hterm,
    Finset.sum_sub_distrib]
  simp

end Yau.LeafProofs.L14Aux
