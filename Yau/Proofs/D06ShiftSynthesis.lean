import Yau.Proofs.D06WoldBasis
import Yau.Proofs.D06HardyShift

/-! The wandering-basis synthesis map intertwines the actual Hardy shift. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {r : ℕ}

def pureShiftSynthesis (S : E →ₗᵢ[ℂ] E) (b : OrthonormalBasis (Fin r) ℂ S.rangeᗮ)
    (hpure : (⨅ k : ℕ, (S ^ k).range) = ⊥) : HardySeq r ≃ₗᵢ[ℂ] E :=
  (pureShiftHilbertBasis S b hpure).repr.symm

theorem pureShiftSynthesis_single (S : E →ₗᵢ[ℂ] E)
    (b : OrthonormalBasis (Fin r) ℂ S.rangeᗮ)
    (hpure : (⨅ k : ℕ, (S ^ k).range) = ⊥) (n : ℕ) (j : Fin r) :
    pureShiftSynthesis S b hpure (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) 1) =
      (S ^ n) (b j : E) := by
  unfold pureShiftSynthesis
  rw [HilbertBasis.repr_symm_single]
  simp only [pureShiftHilbertBasis, HilbertBasis.coe_mk, shiftedWanderingBasis]

theorem pureShiftSynthesis_single_smul (S : E →ₗᵢ[ℂ] E)
    (b : OrthonormalBasis (Fin r) ℂ S.rangeᗮ)
    (hpure : (⨅ k : ℕ, (S ^ k).range) = ⊥) (n : ℕ) (j : Fin r) (c : ℂ) :
    pureShiftSynthesis S b hpure (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) c) =
      c • (S ^ n) (b j : E) := by
  have hc : lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) c =
      c • lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) 1 := by
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [hc, map_smul, pureShiftSynthesis_single]

theorem hardyShift_single (n : ℕ) (j : Fin r) (c : ℂ) :
    hardyShift (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) c) =
      lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n + 1, j) c := by
  ext ⟨k, i⟩
  cases k with
  | zero => simp [lp.single_apply, Pi.single_apply, Prod.mk.injEq]
  | succ k => simp [lp.single_apply, Pi.single_apply, Prod.mk.injEq]

theorem pureShiftSynthesis_intertwines (S : E →ₗᵢ[ℂ] E)
    (b : OrthonormalBasis (Fin r) ℂ S.rangeᗮ)
    (hpure : (⨅ k : ℕ, (S ^ k).range) = ⊥) :
    S.toContinuousLinearMap.comp (pureShiftSynthesis S b hpure).toLinearIsometry.toContinuousLinearMap =
      (pureShiftSynthesis S b hpure).toLinearIsometry.toContinuousLinearMap.comp
        (hardyShiftLI : HardySeq r →ₗᵢ[ℂ] HardySeq r).toContinuousLinearMap := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  rintro ⟨n, j⟩
  apply ContinuousLinearMap.ext
  intro c
  change S (pureShiftSynthesis S b hpure
      (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) c)) =
    pureShiftSynthesis S b hpure (hardyShift
      (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) c))
  rw [hardyShift_single, pureShiftSynthesis_single_smul, pureShiftSynthesis_single_smul,
    map_smul, pow_succ']
  rfl

end Yau.NodeProofs.D06Aux
