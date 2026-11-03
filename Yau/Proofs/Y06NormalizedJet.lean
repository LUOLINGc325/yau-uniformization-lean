import Yau.Proofs.Y06GermLinearization
import Yau.Proofs.Y06VolumeInduction

/-! Construct the actual volume-normalized transition polynomial from the
original V and aligned matrices, with the same F and the same d-jet. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux Yau.Proofs.Y01Aux
open scoped ContDiff

variable {n d : ℕ}

def normalizedPolynomial (V : ℕ → PolyMap n) (E : Frames n) (L : Changes n) (k : ℕ) : PolyMap n :=
  (linearPolynomial (L.plus k * (E.finish k).conjTranspose)).comp
    ((V k).comp (linearPolynomial (E.start k * (L.minus k)⁻¹)))

theorem normalizedPolynomial_data
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) {r : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell Evol : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n}
    (hVol : CoherentVolume F tk s d r last logs B ell Evol A Ainv V)
    (hd : 1 ≤ d) (k : ℕ)
    (hF0 : F (tk k) (tk (k + 1)) 0 = 0)
    (hFdiff : DifferentiableOn ℂ (F (tk k) (tk (k + 1))) (Metric.ball 0 r))
    {L : Changes n} {w : ℕ → Fin n → ℝ} {j : ℕ → ℕ} {S : ℕ → ℝ} {C c : ℝ}
    (hL : ChangeAt (diagonal F tk E) w j S C c L k) :
    IsConstantVolumeJet (normalizedPolynomial V E L k) d ∧
      (normalizedPolynomial V E L k).linearPart = diagonal F tk E k ∧
      GermJetEq (normalizedPolynomial V E L k).eval
        (normalizedRegularTransition F tk A Ainv E L k) d := by
  let Rplus := L.plus k * (E.finish k).conjTranspose
  let Rminus := E.start k * (L.minus k)⁻¹
  let P := normalizedPolynomial V E L k
  obtain ⟨hellD, hell0, hellSum, hellJet, hED, hEJet, hAdef, hA0, hI0, hAlin,
    hAD, hID, hAleft, hAright, hVD, hVCV, hVjet⟩ := hVol.2.2.2.1 k
  obtain ⟨hNellD, hNell0, hNellSum, hNellJet, hNED, hNEJet, hNAdef, hNA0, hNI0, hNAlin,
    hNAD, hNID, hNAleft, hNAright, hNVD, hNVCV, hNVjet⟩ := hVol.2.2.2.1 (k + 1)
  have hIlin : (Ainv k).linearPart = 1 := by
    have h := jetEq_linearPart hd hAleft
    rw [comp_linearPart hA0 hI0, hAlin, Matrix.one_mul, id_linearPart] at h
    exact h
  have hFd : DifferentiableAt ℂ (F (tk k) (tk (k + 1))) 0 :=
    hFdiff.differentiableAt (Metric.ball_mem_nhds 0 hVol.1)
  have hVlin : (V k).linearPart = derivativeMatrix (F (tk k) (tk (k + 1))) := by
    have h := polynomial_sandwich_linearPart hd hFd hF0 hI0 (germJetEq_symm hVjet)
    rw [hNAlin, hIlin, Matrix.one_mul, Matrix.mul_one] at h
    exact h
  have hlin : P.linearPart = diagonal F tk E k := by
    change ((linearPoly Rplus).comp ((V k).comp (linearPoly Rminus))).linearPart = _
    rw [comp_linearPart (linearPoly_fixesZero Rplus) (comp_fixesZero hVCV.1 (linearPoly_fixesZero Rminus)),
      comp_linearPart hVCV.1 (linearPoly_fixesZero Rminus), linearPoly_linearPart, linearPoly_linearPart, hVlin]
    have heq : Rplus * (derivativeMatrix (F (tk k) (tk (k + 1))) * Rminus) =
        L.plus k * transformedDerivative F tk E k * (L.minus k)⁻¹ := by
      dsimp only [Rplus, Rminus, transformedDerivative]
      noncomm_ring
    rw [heq, (hE k).2.2.2.2.1]
    exact hL.2.2.2.1
  have hInnerD : ((V k).comp (linearPoly Rminus)).degree ≤ d := by
    apply (comp_degree_le _ _).trans
    exact (Nat.mul_le_mul hVD (linearPoly_degree_le Rminus)).trans_eq (Nat.mul_one d)
  have hPD : P.degree ≤ d := by
    apply (comp_degree_le (linearPoly Rplus) ((V k).comp (linearPoly Rminus))).trans
    exact (Nat.mul_le_mul (linearPoly_degree_le Rplus) hInnerD).trans_eq (Nat.one_mul d)
  have hInner0 := comp_fixesZero hVCV.1 (linearPoly_fixesZero Rminus)
  have hP0 : P.FixesZero := comp_fixesZero (linearPoly_fixesZero Rplus) hInner0
  have hInnerFlat := positiveJacFlat_comp hVCV.2.2.2 (positiveJacFlat_linearPolynomial Rminus d)
    (linearPoly_fixesZero Rminus)
  have hPflat : positiveJacFlat P d := positiveJacFlat_comp
    (positiveJacFlat_linearPolynomial Rplus d) hInnerFlat hInner0
  have hPCV : IsConstantVolumeJet P d := by
    refine ⟨hP0, hPD, ?_, hPflat⟩
    rw [hlin]
    simp only [diagonal, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi =>
      Complex.ofReal_ne_zero.mpr (ne_of_gt ((hE k).2.2.2.2.2.1 i).1))
  have hFsmooth : ContDiffAt ℂ d (F (tk k) (tk (k + 1))) 0 :=
    (holomorphic_ball_smooth hVol.1 hFdiff).of_le (WithTop.coe_le_coe.mpr le_top)
  have hIz := (fixesZero_iff_eval_zero _).mp hI0
  have hNz := (fixesZero_iff_eval_zero _).mp hNA0
  have hVz := (fixesZero_iff_eval_zero _).mp hVCV.1
  have hIcont : ContDiffAt ℂ d (Ainv k).eval 0 :=
    (polyMap_eval_contDiff _).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hNcont : ContDiffAt ℂ d (A (k + 1)).eval 0 :=
    (polyMap_eval_contDiff _).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hVcont : ContDiffAt ℂ d (V k).eval 0 :=
    (polyMap_eval_contDiff _).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  let f₀ := fun z => (A (k + 1)).eval (F (tk k) (tk (k + 1)) ((Ainv k).eval z))
  have hf₀ : ContDiffAt ℂ d f₀ 0 := by
    have hFat : ContDiffAt ℂ d (F (tk k) (tk (k + 1))) ((Ainv k).eval 0) := by
      simpa only [hIz] using hFsmooth
    have h₁ : ContDiffAt ℂ d (F (tk k) (tk (k + 1)) ∘ (Ainv k).eval) 0 := by
      exact hFat.comp 0 hIcont
    have hz : (F (tk k) (tk (k + 1)) ∘ (Ainv k).eval) 0 = 0 := by
      simp only [Function.comp_apply, hIz, hF0]
    have hNat : ContDiffAt ℂ d (A (k + 1)).eval
        ((F (tk k) (tk (k + 1)) ∘ (Ainv k).eval) 0) := by
      simpa only [hz] using hNcont
    exact hNat.comp 0 h₁
  have hf₀0 : f₀ 0 = 0 := by simp only [f₀, hIz, hF0, hNz]
  have h := germJetEq_linear_sandwich
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Rplus)
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Rminus) hf₀ hVcont hf₀0 hVz hVjet
  have hactual : (fun z => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Rplus
      (f₀ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Rminus z))) =
      normalizedRegularTransition F tk A Ainv E L k := rfl
  have hpoly : (fun z => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Rplus
      ((V k).eval (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Rminus z))) = P.eval := by
    funext z
    change _ = ((linearPoly Rplus).comp ((V k).comp (linearPoly Rminus))).eval z
    rw [polyMap_eval_comp, polyMap_eval_comp, linearPoly_eval, linearPoly_eval]
  exact ⟨hPCV, hlin, germJetEq_symm (germJetEq_transport hactual hpoly h)⟩

end Yau.Proofs.Y06Aux
