import Yau.Proofs.Y01JumpBounds
import Yau.Proofs.Y01CorrectionBounds
import Yau.Proofs.Y01CoherentBounds

/-! Uniform coefficient bounds for the actual finite primary coordinate
polynomials, derived from the original volume and correction outputs. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n d : ℕ}

theorem coordinate_coeffNorm_sqrt_bounds
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {Qclock : ℕ → ℝ} {N j₀ : ℕ} {M hm scale K eps : ℝ}
    (hhm : 0 < hm) (hgrid : GridLayout Qclock N M hm j₀)
    {L : Changes n} {C c : ℝ} (hc : 0 < c)
    (hL : ∀ k, Regular Qclock N M (macroAt Qclock N M hm j₀ k) →
      ChangeAt (diagonal F tk E) (weight Qclock N M hm scale K eps j₀ (rate F tk E))
        (macroAt Qclock N M hm j₀) (macroClock hm) C c L k)
    {r : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell Evol : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n}
    (hVol : CoherentVolume F tk (gridClock Qclock N M hm j₀) d r last logs B ell Evol A Ainv V)
    {Fhat : ℕ → ComplexVector n → ComplexVector n} {Djet Jjet : ℕ → Herm n}
    {wjet : ℕ → Fin n → ℝ} {active : ℕ → Prop} {Dstar : ℕ} {Cq : ℝ} {qsol : JetData n}
    (hd : 1 ≤ d)
    (hQ : RegularJetSolution Fhat Djet Jjet wjet active d Dstar
      (gridClock Qclock N M hm j₀) Cq qsol) :
    let s := gridClock Qclock N M hm j₀
    let reg := fun k => Regular Qclock N M (macroAt Qclock N M hm j₀ k)
    let T := primaryDerivative reg E L
    ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ k,
      (coordinateJet d (A k) (qsol.correction k) (T k)).coeffNorm ≤ Real.exp (Ch * Real.sqrt (s k)) ∧
      (inverseCoordinateJet d (Ainv k) (qsol.inverseJet k) (T k)).coeffNorm ≤ Real.exp (Ch * Real.sqrt (s k)) := by
  let s := gridClock Qclock N M hm j₀
  let reg := fun k => Regular Qclock N M (macroAt Qclock N M hm j₀ k)
  let T := primaryDerivative reg E L
  have hs k : 1 ≤ s k := gridClock_one_le hhm.le hgrid k
  obtain ⟨CA, hCA, hAbound⟩ := hVol.2.2.2.2
  have hA k : (A k).coeffNorm ≤ (1 + s k) ^ CA := by
    have hell : 0 ≤ ∑ β ∈ (ell k).support, ‖(ell k).coeff β‖ :=
      Finset.sum_nonneg (fun β hβ => norm_nonneg _)
    have h := hAbound k
    rw [abs_of_nonneg (by linarith [hs k] : 0 ≤ s k)] at h
    linarith [coeffNorm_nonneg (Ainv k)]
  have hI k : (Ainv k).coeffNorm ≤ (1 + s k) ^ CA := by
    have hell : 0 ≤ ∑ β ∈ (ell k).support, ‖(ell k).coeff β‖ :=
      Finset.sum_nonneg (fun β hβ => norm_nonneg _)
    have h := hAbound k
    rw [abs_of_nonneg (by linarith [hs k] : 0 ≤ s k)] at h
    linarith [coeffNorm_nonneg (A k)]
  have hAenv : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, (A k).coeffNorm ≤ Real.exp (C * Real.sqrt (s k)) :=
    ⟨4 * |CA|, by positivity, fun k => (hA k).trans (polynomial_le_sqrt_envelope (hs k))⟩
  have hIenv : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, (Ainv k).coeffNorm ≤ Real.exp (C * Real.sqrt (s k)) :=
    ⟨4 * |CA|, by positivity, fun k => (hI k).trans (polynomial_le_sqrt_envelope (hs k))⟩
  obtain ⟨p, hp, hT⟩ := primaryDerivative_polynomial_bounds (F := F) (tk := tk) (E := E)
    (Q := Qclock) (N := N) (j₀ := j₀) (M := M) (hm := hm) (scale := scale) (K := K)
    (eps := eps) (L := L) (C := C) (c := c) hE hhm hgrid hc hL
  let CL := (n : ℝ) ^ 2 + 4 * |p|
  have hCL : 0 ≤ CL := by dsimp [CL]; positivity
  have hLinear k : (linearPoly (T k)).coeffNorm ≤ Real.exp (CL * Real.sqrt (s k)) := by
    have hTk : matOpNorm (T k) ≤ (1 + s k) ^ p := by
      linarith [hT k, matOpNorm_nonneg_own (T k)⁻¹]
    have hcoeff := (linearPoly_coeffNorm_le_matOpNorm (T k)).trans
      (mul_le_mul_of_nonneg_left hTk (sq_nonneg (n : ℝ)))
    exact hcoeff.trans (mul_sqrt_envelope (sq_nonneg (n : ℝ))
      (Real.rpow_nonneg (by linarith [hs k]) _)
      (constant_le_sqrt_envelope (sq_nonneg (n : ℝ)) (hs k))
      (polynomial_le_sqrt_envelope (hs k)))
  have hLinearInv k : (linearPoly (T k)⁻¹).coeffNorm ≤ Real.exp (CL * Real.sqrt (s k)) := by
    have hTk : matOpNorm (T k)⁻¹ ≤ (1 + s k) ^ p := by
      linarith [hT k, matOpNorm_nonneg_own (T k)]
    have hcoeff := (linearPoly_coeffNorm_le_matOpNorm (T k)⁻¹).trans
      (mul_le_mul_of_nonneg_left hTk (sq_nonneg (n : ℝ)))
    exact hcoeff.trans (mul_sqrt_envelope (sq_nonneg (n : ℝ))
      (Real.rpow_nonneg (by linarith [hs k]) _)
      (constant_le_sqrt_envelope (sq_nonneg (n : ℝ)) (hs k))
      (polynomial_le_sqrt_envelope (hs k)))
  obtain ⟨Ccorr, hCcorr, hCorr⟩ := all_correction_sqrt_bounds hQ hs
  have hCenv : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, (qsol.correction k).coeffNorm ≤ Real.exp (C * Real.sqrt (s k)) := by
    refine ⟨Ccorr, hCcorr, ?_⟩
    intro k
    linarith [hCorr k, coeffNorm_nonneg (qsol.inverseJet k)]
  have hCIenv : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, (qsol.inverseJet k).coeffNorm ≤ Real.exp (C * Real.sqrt (s k)) := by
    refine ⟨Ccorr, hCcorr, ?_⟩
    intro k
    linarith [hCorr k, coeffNorm_nonneg (qsol.correction k)]
  have hData k := correction_data_of_regularJetSolution hd hQ k
  have hAiDegree k : (Ainv k).degree ≤ d := by
    obtain ⟨hellDegree, hellZero, hellSum, hellJet, hEDegree, hEJet, hAdef, hAzero, hAizero,
      hAlinear, hADegree, hAiDegree, hAleft, hAright, hVDegree, hVconst, hVjet⟩ := hVol.2.2.2.1 k
    exact hAiDegree
  have hInner := exists_jetComp_sqrt_envelope hs
    (fun k => (linearPoly_degree_le (T k)).trans hd) ⟨CL, hCL, hLinear⟩ hAenv
  obtain ⟨Ch, hCh, hH⟩ := exists_jetComp_sqrt_envelope hs
    (fun k => (hData k).1.2.1) hCenv hInner
  have hInnerI := exists_jetComp_sqrt_envelope hs hAiDegree hIenv ⟨CL, hCL, hLinearInv⟩
  obtain ⟨Ci, hCi, hHI⟩ := exists_jetComp_sqrt_envelope hs
    (fun k => jetComp_degree d (Ainv k) (linearPoly (T k)⁻¹)) hInnerI hCIenv
  refine ⟨max Ch Ci, hCh.trans (le_max_left _ _), ?_⟩
  intro k
  constructor
  · exact (hH k).trans (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  · exact (hHI k).trans (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)))

end Yau.Proofs.Y01Aux
