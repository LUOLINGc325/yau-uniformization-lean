import Yau.LeafProofs.L14LocalSystem

noncomputable section
open scoped Topology ContDiff
open MeasureTheory Filter Module
open Yau

namespace Yau.LeafProofs.L14Aux

def wirtRealCoefficient (d : Fin 2) : ℂ := if d = 0 then 1 / 2 else -(Complex.I / 2)

theorem wirt_eq_real_directions {n : ℕ} (f : ComplexVector n → ℂ) (z : ComplexVector n) (i : Fin n) :
    wirt f z (stdVec i) =
      wirtRealCoefficient 0 * fderiv ℝ f z (realVec (i, 0)) +
      wirtRealCoefficient 1 * fderiv ℝ f z (realVec (i, 1)) := by
  simp only [wirt, wirtRealCoefficient, realVec, stdVec, ite_true, one_smul]
  norm_num
  ring

theorem wirt_ofReal_eq_real_directions {n : ℕ} (ψ : ComplexVector n → ℝ)
    (z : ComplexVector n) (hψ : DifferentiableAt ℝ ψ z) (i : Fin n) :
    wirt (fun w => Complex.ofReal (ψ w)) z (stdVec i) =
      wirtRealCoefficient 0 * (fderiv ℝ ψ z (realVec (i, 0)) : ℂ) +
      wirtRealCoefficient 1 * (fderiv ℝ ψ z (realVec (i, 1)) : ℂ) := by
  rw [wirt_eq_real_directions]
  have he := (Complex.ofRealCLM.hasFDerivAt.comp z hψ.hasFDerivAt).fderiv
  change fderiv ℝ (fun w => Complex.ofReal (ψ w)) z = Complex.ofRealCLM.comp (fderiv ℝ ψ z) at he
  rw [he]
  rfl

def wirtDivergenceDerivative {n : ℕ} {α β : Type*}
    (C : β → α → Fin n → ComplexVector n → ℂ) : β → α → RIdx n → ComplexVector n → ℂ :=
  fun r c p z => -wirtRealCoefficient p.2 * C r c p.1 z

def wirtDivergenceValue {n : ℕ} {α β : Type*}
    (C : β → α → Fin n → ComplexVector n → ℂ) : β → α → ComplexVector n → ℂ :=
  fun r c z => -∑ i, wirt (C r c i) z (stdVec i)

theorem sum_wirtRealCoefficient_fderiv {n : ℕ} (C : Fin n → ComplexVector n → ℂ) (z : ComplexVector n) :
    (∑ p : RIdx n, wirtRealCoefficient p.2 * fderiv ℝ (C p.1) z (realVec p)) =
      ∑ i, wirt (C i) z (stdVec i) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two, wirt_eq_real_directions]

theorem wirtDivergenceDerivative_fderiv {n : ℕ} {α β : Type*}
    (C : β → α → Fin n → ComplexVector n → ℂ) (r : β) (c : α)
    (p : RIdx n) (z v : ComplexVector n)
    (hC : DifferentiableAt ℝ (C r c p.1) z) :
    fderiv ℝ (wirtDivergenceDerivative C r c p) z v =
      -wirtRealCoefficient p.2 * fderiv ℝ (C r c p.1) z v := by
  have he := (hC.hasFDerivAt.const_mul (-wirtRealCoefficient p.2)).fderiv
  exact congrArg (fun L : ComplexVector n →L[ℝ] ℂ => L v) he

theorem wirtDivergence_formal_test_row {n : ℕ} {α β : Type*}
    (C : β → α → Fin n → ComplexVector n → ℂ) (r : β) (c : α)
    (z : ComplexVector n) (hC : ∀ i, DifferentiableAt ℝ (C r c i) z)
    (ψ : ComplexVector n → ℝ) (hψ : DifferentiableAt ℝ ψ z) :
    (-(∑ p : RIdx n, (wirtDivergenceDerivative C r c p z * (fderiv ℝ ψ z (realVec p) : ℂ) +
      fderiv ℝ (wirtDivergenceDerivative C r c p) z (realVec p) * (ψ z : ℂ))) +
      wirtDivergenceValue C r c z * (ψ z : ℂ)) =
    ∑ i, C r c i z * wirt (fun w => Complex.ofReal (ψ w)) z (stdVec i) := by
  have hDa : (∑ p : RIdx n, fderiv ℝ (wirtDivergenceDerivative C r c p) z (realVec p)) =
      -∑ i, wirt (C r c i) z (stdVec i) := by
    simp_rw [wirtDivergenceDerivative_fderiv C r c _ z _ (hC _), neg_mul, Finset.sum_neg_distrib]
    rw [sum_wirtRealCoefficient_fderiv]
  have hA : (∑ p : RIdx n, wirtDivergenceDerivative C r c p z * (fderiv ℝ ψ z (realVec p) : ℂ)) =
      -(∑ i, C r c i z * wirt (fun w => Complex.ofReal (ψ w)) z (stdVec i)) := by
    rw [Fintype.sum_prod_type]
    simp only [wirtDivergenceDerivative, Fin.sum_univ_two, wirt_ofReal_eq_real_directions ψ z hψ,
      Finset.sum_neg_distrib]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hDa, hA]
  simp only [wirtDivergenceValue]
  ring


theorem wirtDivergence_system_apply {n : ℕ} {α β : Type*} [Fintype α]
    (C : β → α → Fin n → ComplexVector n → ℂ) (F : ComplexVector n → α → ℂ)
    (z : ComplexVector n) (r : β)
    (hC : ∀ c i, DifferentiableAt ℝ (C r c i) z)
    (hF : ∀ c, DifferentiableAt ℝ (fun w => F w c) z) :
    complexFirstOrderSystemApply realVec (wirtDivergenceDerivative C) (wirtDivergenceValue C) F z r =
      -∑ i, wirt (fun w => ∑ c, C r c i w * F w c) z (stdVec i) := by
  have hprincipal (c : α) : (∑ p : RIdx n, wirtDivergenceDerivative C r c p z *
      fderiv ℝ (fun w => F w c) z (realVec p)) =
      -(∑ i, C r c i z * wirt (fun w => F w c) z (stdVec i)) := by
    rw [Fintype.sum_prod_type]
    simp only [wirtDivergenceDerivative, Fin.sum_univ_two, wirt_eq_real_directions,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrow (i : Fin n) : wirt (fun w => ∑ c, C r c i w * F w c) z (stdVec i) =
      ∑ c, (wirt (C r c i) z (stdVec i) * F z c +
        C r c i z * wirt (fun w => F w c) z (stdVec i)) := by
    rw [wirt_sum_fun Finset.univ (fun c w => C r c i w * F w c) z (stdVec i)
      (fun c _ => (hC c i).mul (hF c))]
    exact Finset.sum_congr rfl (fun c _ => wirt_mul_rule _ _ z (stdVec i) (hC c i) (hF c))
  simp_rw [complexFirstOrderSystemApply, hprincipal, wirtDivergenceValue, hrow,
    neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro c _
  ring

end Yau.LeafProofs.L14Aux
