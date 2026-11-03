import Yau.Proofs.Y05Multilinear

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment MvPolynomial
open scoped ContDiff

variable {n : ℕ}

def taylorPolynomial (p : FormalMultilinearSeries ℂ (ComplexVector n) ℂ) (d : ℕ) :
    MvPolynomial (Fin n) ℂ :=
  ∑ m ∈ Finset.range (d + 1), diagonalPolynomial (p m)

def truncatedSeries (p : FormalMultilinearSeries ℂ (ComplexVector n) ℂ) (d : ℕ) :
    FormalMultilinearSeries ℂ (ComplexVector n) ℂ :=
  fun m => if m ≤ d then p m else 0

theorem scalarEval_taylorPolynomial
    (p : FormalMultilinearSeries ℂ (ComplexVector n) ℂ) (d : ℕ) (z : ComplexVector n) :
    scalarEval (taylorPolynomial p d) z = ∑ m ∈ Finset.range (d + 1), p m (fun _ => z) := by
  simp only [taylorPolynomial, scalarEval, map_sum]
  exact Finset.sum_congr rfl (fun m _ => scalarEval_diagonalPolynomial (p m) z)

theorem taylorPolynomial_degree
    (p : FormalMultilinearSeries ℂ (ComplexVector n) ℂ) (d : ℕ) :
    (taylorPolynomial p d).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro m hm
  exact (diagonalPolynomial_degree (p m)).trans
    (by have H := Finset.mem_range.mp hm; omega)

theorem hasFiniteFPowerSeries_taylorPolynomial
    (p : FormalMultilinearSeries ℂ (ComplexVector n) ℂ) (d : ℕ) :
    HasFiniteFPowerSeriesOnBall (scalarEval (taylorPolynomial p d)) (truncatedSeries p d)
      0 (d + 1) ⊤ := by
  apply HasFiniteFPowerSeriesOnBall.mk'
  · intro m hm
    simp only [truncatedSeries, if_neg (by omega : ¬m ≤ d)]
  · exact ENNReal.zero_lt_top
  · intro z _
    rw [zero_add, scalarEval_taylorPolynomial]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [truncatedSeries, if_pos (by have H := Finset.mem_range.mp hm; omega : m ≤ d)]

/-- The coordinate polynomial agrees with the genuine Fréchet jet, rather
than merely with a list of chosen coefficients. -/
theorem scalarJetEq_taylorPolynomial {f : ComplexVector n → ℂ}
    {p : FormalMultilinearSeries ℂ (ComplexVector n) ℂ}
    (hf : HasFPowerSeriesAt f p 0) (d : ℕ) :
    ScalarJetEq (scalarEval (taylorPolynomial p d)) f d := by
  obtain ⟨r, hr⟩ := hf
  intro m hm
  ext v
  have H := (hasFiniteFPowerSeries_taylorPolynomial p d).toHasFPowerSeriesOnBall
    |>.iteratedFDeriv_eq_sum_of_completeSpace v
  simp only [truncatedSeries, if_pos hm] at H
  exact H.trans (hr.iteratedFDeriv_eq_sum_of_completeSpace v).symm

theorem exists_scalar_taylor {f : ComplexVector n → ℂ} (hf : AnalyticAt ℂ f 0) (d : ℕ) :
    ∃ P : MvPolynomial (Fin n) ℂ,
      P.totalDegree ≤ d ∧ ScalarJetEq (scalarEval P) f d := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨taylorPolynomial p d, taylorPolynomial_degree p d, scalarJetEq_taylorPolynomial hp d⟩

theorem coefficient_zero_of_scalarJetEq {P : MvPolynomial (Fin n) ℂ}
    {f : ComplexVector n → ℂ} {d : ℕ} (h : ScalarJetEq (scalarEval P) f d) :
    P.coeff 0 = f 0 := by
  have H := congrArg (fun L => L (fun i : Fin 0 => Fin.elim0 i)) (h 0 (Nat.zero_le d))
  simpa [iteratedFDeriv_zero_apply, scalarEval, MvPolynomial.constantCoeff] using H

end Yau.Proofs.Y05Aux
