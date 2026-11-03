import Yau.Proofs.Y01AssembledModels
import Yau.Proofs.Y01RealizationGrowth
import Yau.Proofs.Y01JumpBounds

/-! The actual branch choice keeps the Y02 leading constant fixed before
geometry, and puts every regular or endpoint cost in one sqrt-clock error. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n d : ℕ}

theorem assembled_models_coeffNorm_bound
    {Fhat : ℕ → ComplexVector n → ComplexVector n} {Djet Jjet J : ℕ → Herm n}
    {w : ℕ → Fin n → ℝ} {active : ℕ → Prop} {Dstar : ℕ} {s Δ : ℕ → ℝ}
    {Cq Craw Cj Cb Ci : ℝ} {qsol : JetData n} {R Rinv Jet : ℕ → PolyMap n}
    (hQ : RegularJetSolution Fhat Djet Jjet w active d Dstar s Cq qsol)
    (hs : ∀ k, 1 ≤ s k) (hΔ : ∀ k, 0 ≤ Δ k) (hCj : 0 ≤ Cj)
    (hJ : ∀ k, active k → (linearPoly (J k)).coeffNorm + (linearPoly (J k)⁻¹).coeffNorm ≤
      Real.exp (Cj * Real.sqrt (s k)))
    (hJet : ∀ k, (Jet k).coeffNorm ≤ Real.exp (Cb * Real.sqrt (s k)))
    (hInv : ∀ k, matOpNorm (Jet k).linearPart⁻¹ ≤ Real.exp (Δ k / 2 + Ci * Real.sqrt (s k)))
    (hR : ∀ k, (R k).coeffNorm + (Rinv k).coeffNorm ≤
      Craw * (1 + (Jet k).coeffNorm + matOpNorm (Jet k).linearPart⁻¹) ^ Craw) :
    ∃ Cerr : ℝ, 0 ≤ Cerr ∧ ∀ k,
      (assembledModel active J qsol R k).coeffNorm +
          (assembledInverseModel active J qsol Rinv k).coeffNorm ≤
        Real.exp ((1 + |Craw|) * Δ k + Cerr * Real.sqrt (s k)) := by
  let Cq0 := max 0 Cq
  have hCq0 : 0 ≤ Cq0 := le_max_left _ _
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  let C₁ := Cj + (1 : ℝ) * (max 0 Cq0 + Real.log 2)
  let C₂ := Cq0 + (Dstar : ℝ) * (max 0 Cj + Real.log 2)
  let Creg := max C₁ C₂ + Real.log 2
  let Cbad := |Craw| * (max 0 (max Cb Ci) + 1 + Real.log 3)
  let Cerr := max Creg Cbad
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hCreg : 0 ≤ Creg := add_nonneg (hC₁.trans (le_max_left _ _)) hlog2
  have hCbad : 0 ≤ Cbad := by dsimp only [Cbad]; positivity
  refine ⟨Cerr, hCreg.trans (le_max_left _ _), ?_⟩
  intro k
  by_cases hk : active k
  · obtain ⟨hqlin, hqdegree, hqvolume, hqidegree, hqizero, hqleft, hqright, hforbidden,
      hmzero, hmlinear, hallowed, hauto, hmdegree, hmidegree, hjac, hconj, hnorm⟩ := hQ.2 k hk
    have hMn : (qsol.model k).coeffNorm ≤ Real.exp (Cq * Real.sqrt (s k)) := by
      linarith [coeffNorm_nonneg (qsol.correction k), coeffNorm_nonneg (qsol.inverseJet k),
        coeffNorm_nonneg (qsol.inverseModel k)]
    have hIn : (qsol.inverseModel k).coeffNorm ≤ Real.exp (Cq * Real.sqrt (s k)) := by
      linarith [coeffNorm_nonneg (qsol.correction k), coeffNorm_nonneg (qsol.inverseJet k),
        coeffNorm_nonneg (qsol.model k)]
    have hUp : Real.exp (Cq * Real.sqrt (s k)) ≤ Real.exp (Cq0 * Real.sqrt (s k)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
    have hJn : (linearPoly (J k)).coeffNorm ≤ Real.exp (Cj * Real.sqrt (s k)) := by
      linarith [hJ k hk, coeffNorm_nonneg (linearPoly (J k)⁻¹)]
    have hJin : (linearPoly (J k)⁻¹).coeffNorm ≤ Real.exp (Cj * Real.sqrt (s k)) := by
      linarith [hJ k hk, coeffNorm_nonneg (linearPoly (J k))]
    have hG := comp_sqrt_envelope (d := 1) (hs k) (linearPoly_degree_le (J k)) hJn (hMn.trans hUp)
    have hI := comp_sqrt_envelope (d := Dstar) (hs k) hmidegree (hIn.trans hUp) hJin
    have hG' : ((linearPoly (J k)).comp (qsol.model k)).coeffNorm ≤ Real.exp (C₁ * Real.sqrt (s k)) := by
      simpa only [C₁, Nat.cast_one] using hG
    have hI' : ((qsol.inverseModel k).comp (linearPoly (J k)⁻¹)).coeffNorm ≤ Real.exp (C₂ * Real.sqrt (s k)) := hI
    have hsum := exp_sqrt_add_bound (hs k) hG' hI'
    have hLeading : 0 ≤ (1 + |Craw|) * Δ k := mul_nonneg (by positivity) (hΔ k)
    have hMax : Creg * Real.sqrt (s k) ≤ Cerr * Real.sqrt (s k) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    have hbound : ((linearPoly (J k)).comp (qsol.model k)).coeffNorm +
        ((qsol.inverseModel k).comp (linearPoly (J k)⁻¹)).coeffNorm ≤
          Real.exp ((1 + |Craw|) * Δ k + Cerr * Real.sqrt (s k)) :=
      hsum.trans (Real.exp_le_exp.2 (by linarith))
    simpa only [assembledModel, assembledInverseModel, hk, ite_true] using hbound
  · have hraw := raw_realization_growth (C := Craw) (hs k) (hΔ k)
      (coeffNorm_nonneg (Jet k)) (matOpNorm_nonneg_own (Jet k).linearPart⁻¹) (hJet k) (hInv k)
    have hMax : Cbad * Real.sqrt (s k) ≤ Cerr * Real.sqrt (s k) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
    have hbound : (R k).coeffNorm + (Rinv k).coeffNorm ≤
        Real.exp ((1 + |Craw|) * Δ k + Cerr * Real.sqrt (s k)) := by
      apply (hR k).trans (hraw.trans (Real.exp_le_exp.2 _))
      change (1 + |Craw|) * Δ k + Cbad * Real.sqrt (s k) ≤
        (1 + |Craw|) * Δ k + Cerr * Real.sqrt (s k)
      linarith
    simpa only [assembledModel, assembledInverseModel, hk, ite_false] using hbound

end Yau.Proofs.Y01Aux
