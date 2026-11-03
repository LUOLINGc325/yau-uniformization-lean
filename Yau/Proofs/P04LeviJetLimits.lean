import Yau.Proofs.P04LeviLogChain
import Mathlib.Analysis.Matrix.Order

noncomputable section
open Filter
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem leviC_entry_eq_hessian {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (i j : Fin n) :
    leviC f z i j =
      (((1/4 : ℝ)*(fderiv ℝ (fderiv ℝ f) z (stdVec j) (stdVec i)+
        fderiv ℝ (fderiv ℝ f) z (Complex.I • stdVec j) (Complex.I • stdVec i)) : ℝ) : ℂ)+
      Complex.I*(((1/4 : ℝ)*(fderiv ℝ (fderiv ℝ f) z (stdVec j) (Complex.I • stdVec i)-
        fderiv ℝ (fderiv ℝ f) z (Complex.I • stdVec j) (stdVec i)) : ℝ) : ℂ) := by
  have HH := L18Aux.leviMatrix_entry_re_im hf stdVec i j
  apply Complex.ext
  · simpa only [leviC,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,zero_mul,one_mul,sub_zero,add_zero] using HH.1
  · simpa only [leviC,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
      Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add] using HH.2

theorem iteratedJet_eval_tendsto {F : ℕ → ComplexVector n → ℝ} {f : ComplexVector n → ℝ}
    {z : ComplexVector n} {q : ℕ}
    (h : Tendsto (fun N => iteratedFDeriv ℝ q (F N) z) atTop (𝓝 (iteratedFDeriv ℝ q f z)))
    (v : Fin q → ComplexVector n) :
    Tendsto (fun N => iteratedFDeriv ℝ q (F N) z v) atTop (𝓝 (iteratedFDeriv ℝ q f z v)) := by
  have hc : Continuous (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin q => ComplexVector n) ℝ => L v) := by
    fun_prop
  exact (hc.tendsto _).comp h

theorem leviC_tendsto_of_second_jets {F : ℕ → ComplexVector n → ℝ} {f : ComplexVector n → ℝ}
    {z : ComplexVector n} (hF : ∀ N, ContDiffAt ℝ 2 (F N) z) (hf : ContDiffAt ℝ 2 f z)
    (hjets : Tendsto (fun N => iteratedFDeriv ℝ 2 (F N) z) atTop (𝓝 (iteratedFDeriv ℝ 2 f z))) :
    Tendsto (fun N => leviC (F N) z) atTop (𝓝 (leviC f z)) := by
  have hH (v w : ComplexVector n) :
      Tendsto (fun N => fderiv ℝ (fderiv ℝ (F N)) z v w) atTop
        (𝓝 (fderiv ℝ (fderiv ℝ f) z v w)) := by
    simpa only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using
      iteratedJet_eval_tendsto hjets (![v,w] : Fin 2 → ComplexVector n)
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simp_rw [leviC_entry_eq_hessian (hF _) i j,leviC_entry_eq_hessian hf i j]
  exact (((Complex.continuous_ofReal.tendsto _).comp
    (((hH _ _).add (hH _ _)).const_mul (1/4 : ℝ))).add
    (((Complex.continuous_ofReal.tendsto _).comp
      (((hH _ _).sub (hH _ _)).const_mul (1/4 : ℝ))).const_mul Complex.I))

theorem gradientGram_tendsto_of_first_jets {F : ℕ → ComplexVector n → ℝ}
    {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hF : ∀ N, DifferentiableAt ℝ (F N) z) (hf : DifferentiableAt ℝ f z)
    (hjets : Tendsto (fun N => iteratedFDeriv ℝ 1 (F N) z) atTop (𝓝 (iteratedFDeriv ℝ 1 f z))) :
    Tendsto (fun N => gradientGram (F N) z) atTop (𝓝 (gradientGram f z)) := by
  have hD (v : ComplexVector n) :
      Tendsto (fun N => fderiv ℝ (F N) z v) atTop (𝓝 (fderiv ℝ f z v)) := by
    simpa only [iteratedFDeriv_one_apply] using
      iteratedJet_eval_tendsto hjets (fun _ : Fin 1 => v)
  have hw (v : ComplexVector n) :
      Tendsto (fun N => wirt (fun y => (F N y : ℂ)) z v) atTop
        (𝓝 (wirt (fun y => (f y : ℂ)) z v)) := by
    simp_rw [wirt_ofReal_formula (hF _) v,wirt_ofReal_formula hf v]
    simpa only [Function.comp_def,Complex.ofReal_mul] using
      (((Complex.continuous_ofReal.tendsto _).comp ((hD v).const_mul (1/2 : ℝ))).sub
      (((Complex.continuous_ofReal.tendsto _).comp
        ((hD (Complex.I • v)).const_mul (1/2 : ℝ))).const_mul Complex.I))
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact (hw (stdVec i)).star.mul (hw (stdVec j))

/-- The actual positive matrix cone is closed under the supplied value,
first, and second derivative limits of the same finite functions. -/
theorem levi_numerator_posSemidef_of_jets {F : ℕ → ComplexVector n → ℝ}
    {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hF : ∀ N, ContDiffAt ℝ 2 (F N) z) (hf : ContDiffAt ℝ 2 f z)
    (hjets : ∀ q ≤ 2, Tendsto (fun N => iteratedFDeriv ℝ q (F N) z) atTop
      (𝓝 (iteratedFDeriv ℝ q f z)))
    (hnum : ∀ N, ((F N z : ℂ) • leviC (F N) z-gradientGram (F N) z).PosSemidef) :
    ((f z : ℂ) • leviC f z-gradientGram f z).PosSemidef := by
  have hval : Tendsto (fun N => F N z) atTop (𝓝 (f z)) := by
    simpa only [iteratedFDeriv_zero_apply] using
      iteratedJet_eval_tendsto (hjets 0 (by omega)) (Fin.elim0 : Fin 0 → ComplexVector n)
  have hL := leviC_tendsto_of_second_jets hF hf (hjets 2 le_rfl)
  have hG := gradientGram_tendsto_of_first_jets
    (fun N => (hF N).differentiableAt (by norm_num))
    (hf.differentiableAt (by norm_num)) (hjets 1 (by omega))
  have H := (((Complex.continuous_ofReal.tendsto _).comp hval).smul hL).sub hG
  exact Matrix.posSemidef_is_closed.mem_of_tendsto H (Filter.Eventually.of_forall hnum)

end Yau.Proofs.P04Aux
