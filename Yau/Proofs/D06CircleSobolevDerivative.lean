import Yau.Proofs.D06CircleProjection

/-! Actual higher Sobolev weak derivatives and the transfer of the original
Hardy coefficient orders to their fixed circle traces. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

theorem circleDerivative_sobolev (k : ℕ) {f : CircleL2} (hf : CircleSobolev (k + 1) f) :
    CircleSobolev k (circleDerivative f (circleSobolev_mono hf (by omega))) := by
  apply hf.of_nonneg_of_le (fun _ => mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))
  intro n
  rw [circleDerivative_weak f _ n, circleDerivative_coeff_norm, pow_succ (1 + (n : ℝ) ^ 2) k]
  have hp : 0 ≤ (1 + (n : ℝ) ^ 2) ^ k * ‖circleCoeff f n‖ ^ 2 := by positivity
  nlinarith only [hp]

theorem hardyTrace_circleSobolev {r : ℕ} (a : HardySeq r) (k : ℕ)
    (ha : HardySobolev k a) (i : Fin r) : CircleSobolev k (hardyTraceLp a i) := by
  let F : ℤ → ℝ := fun n => (1 + (n : ℝ) ^ 2) ^ k * ‖hardyPad a i n‖ ^ 2
  let W : ℕ × Fin r → ℝ := fun q => (1 + (q.1 : ℝ) ^ 2) ^ k * ‖a q‖ ^ 2
  have hW : Summable W := ha
  have hinj : Function.Injective (fun n : ℕ => (n, i)) := fun x y h => (Prod.mk.inj h).1
  have hs := hW.comp_injective hinj
  have hcol : Summable (fun n : ℕ => (1 + (n : ℝ) ^ 2) ^ k * ‖a (n, i)‖ ^ 2) :=
    hs.congr (fun _ => rfl)
  have hp : Summable (fun n : ℕ => F (n : ℤ)) := by
    simpa only [F, hardyPad_nat, Int.cast_natCast] using hcol
  have hm : Summable (fun n : ℕ => F (-(n + 1) : ℤ)) := by
    simpa only [F, hardyPad_negSucc, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have h : Summable F := Summable.of_nat_of_neg_add_one hp hm
  apply h.congr
  intro n
  change (1 + (n : ℝ) ^ 2) ^ k * ‖hardyPad a i n‖ ^ 2 =
    (1 + (n : ℝ) ^ 2) ^ k * ‖circleCoeff (hardyTraceLp a i) n‖ ^ 2
  rw [circleCoeff_eq_fourierCoeff, hardyTrace_fourierCoeff]
  rfl

end Yau.NodeProofs.D06Aux
