import Yau.Proofs.Y05FiniteJets
import Yau.Proofs.Y05CompositionEstimates

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau MvPolynomial Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open scoped ContDiff BigOperators

variable {n : ℕ}

theorem norm_scalarEval_le_coeffNorm (P : MvPolynomial (Fin n) ℂ)
    (z : ComplexVector n) (hz : ‖z‖ ≤ 1) : ‖scalarEval P z‖ ≤ polynomialCoeffNorm P := by
  classical
  have hcoord (i : Fin n) : ‖z i‖ ≤ 1 := (PiLp.norm_apply_le z i).trans hz
  have hmono (a : Fin n →₀ ℕ) (c : ℂ) : ‖scalarEval (monomial a c) z‖ ≤ ‖c‖ := by
    simp only [scalarEval, eval_monomial, norm_mul, norm_prod, norm_pow]
    apply (mul_le_mul_of_nonneg_left _ (norm_nonneg c)).trans_eq (mul_one _)
    change ‖∏ i ∈ a.support, z i ^ a i‖ ≤ 1
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
    intro i hi
    simpa only [norm_pow] using pow_le_one₀ (norm_nonneg _) (hcoord i) (n := a i)
  have heq : scalarEval P z = ∑ a ∈ P.support, scalarEval (monomial a (P.coeff a)) z := by
    unfold scalarEval
    rw [← map_sum, support_sum_monomial_coeff]
  rw [heq]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hmono a (P.coeff a))

def polynomialJetConstant (d : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (d + 1), (2 * ((m : ℝ) + 1)) ^ m

theorem polynomial_jet_norm_le (P : MvPolynomial (Fin n) ℂ) {d m : ℕ} (hm : m ≤ d) :
    ‖iteratedFDeriv ℂ m (scalarEval P) 0‖ ≤ polynomialJetConstant d * polynomialCoeffNorm P := by
  have hC : ContDiffOn ℂ ∞ (scalarEval P) (Metric.ball 0 1) :=
    (Yau.Proofs.Y01Aux.polyEval_contDiff P).contDiffOn
  have H := U02AnalyticAux.norm_iteratedFDeriv_center_le (by norm_num : (0 : ℝ) < 1)
    (polynomialCoeffNorm_nonneg P) hC
    (fun z hz => norm_scalarEval_le_coeffNorm P z (by
      have := Metric.mem_ball.mp hz; simpa only [dist_zero_right] using this.le)) m
  simp only [div_one] at H
  have hc : (2 * ((m : ℝ) + 1)) ^ m ≤ polynomialJetConstant d :=
    Finset.single_le_sum (s := Finset.range (d + 1))
      (f := fun j : ℕ => (2 * ((j : ℝ) + 1)) ^ j) (fun j _ => by positivity)
      (Finset.mem_range.mpr (by omega))
  exact H.trans ((mul_le_mul_of_nonneg_left hc (polynomialCoeffNorm_nonneg P)).trans_eq
    (mul_comm _ _))

def exponentialJetConstant (d : ℕ) : ℝ :=
  1 + ∑ m ∈ Finset.range (d + 1), ‖iteratedFDeriv ℂ m Complex.exp 0‖

/-- The finite exponential jet has polynomial coefficient growth in the
input polynomial, despite the untruncated exponential having exponential growth. -/
theorem exists_exponential_polynomial (L : MvPolynomial (Fin n) ℂ) (hL : L.coeff 0 = 0)
    (d : ℕ) : ∃ E : MvPolynomial (Fin n) ℂ,
      E.totalDegree ≤ d ∧ E.coeff 0 = 1 ∧
      ScalarJetEq (scalarEval E) (fun z => Complex.exp (scalarEval L z)) d ∧
      polynomialCoeffNorm E ≤ scalarTaylorConstant n d * compositionJetConstant d *
        exponentialJetConstant d * (1 + polynomialJetConstant d * polynomialCoeffNorm L) ^ d := by
  have hLc : ContDiff ℂ ∞ (scalarEval L) := Yau.Proofs.Y01Aux.polyEval_contDiff L
  have hLa : AnalyticAt ℂ (scalarEval L) 0 :=
    U02AnalyticAux.analyticOnNhd_of_complex_contDiffOn_infty isOpen_univ hLc.contDiffOn 0
      (Set.mem_univ _)
  have hL0 : scalarEval L 0 = 0 := by simpa [scalarEval, constantCoeff] using hL
  have hExp : AnalyticAt ℂ (fun z => Complex.exp (scalarEval L z)) 0 :=
    U02AnalyticAux.analyticOnNhd_of_complex_contDiffOn_infty isOpen_univ
      (Complex.contDiff_exp.comp hLc).contDiffOn 0 (Set.mem_univ _)
  let E := taylorPolynomial
    (U02AnalyticAux.complexTaylorSeries (fun z => Complex.exp (scalarEval L z)) 0) d
  have hjet : ScalarJetEq (scalarEval E) (fun z => Complex.exp (scalarEval L z)) d :=
    scalarJetEq_taylorPolynomial (canonical_series_of_analyticAt hExp) d
  refine ⟨E, taylorPolynomial_degree _ _, ?_, hjet, ?_⟩
  · rw [coefficient_zero_of_scalarJetEq hjet, hL0, Complex.exp_zero]
  · apply (coefficientNorm_canonical_taylor _ d).trans
    have hD : 1 ≤ 1 + polynomialJetConstant d * polynomialCoeffNorm L := by
      have hK : 0 ≤ polynomialJetConstant d := Finset.sum_nonneg fun m _ => by positivity
      nlinarith [polynomialCoeffNorm_nonneg L]
    have hG : 0 ≤ exponentialJetConstant d := by unfold exponentialJetConstant; positivity
    have hg (m : ℕ) (hm : m ≤ d) :
        ‖iteratedFDeriv ℂ m Complex.exp 0‖ ≤ exponentialJetConstant d := by
      apply (Finset.single_le_sum (s := Finset.range (d + 1))
        (f := fun j : ℕ => ‖iteratedFDeriv ℂ j Complex.exp 0‖)
        (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))).trans
      unfold exponentialJetConstant
      linarith
    have hf (m : ℕ) (_hm : 1 ≤ m) (hm : m ≤ d) :
        ‖iteratedFDeriv ℂ m (scalarEval L) 0‖ ≤
          1 + polynomialJetConstant d * polynomialCoeffNorm L := by
      have H := polynomial_jet_norm_le L hm
      linarith
    have hb := finiteJetNorm_comp_uniform_le
      (hLc.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
      (Complex.contDiff_exp.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
      hL0 hD hG hg hf
    exact (mul_le_mul_of_nonneg_left hb (Finset.sum_nonneg fun m _ => by positivity)).trans_eq
      (by unfold scalarTaylorConstant; ring)

end Yau.Proofs.Y05Aux
