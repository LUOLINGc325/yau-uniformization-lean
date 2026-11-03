import Yau.Proofs.D06HardyEvaluationBound

/-! Actual radial coefficient dilations converge in the original Hardy norm. -/

open scoped lp Topology
open Filter

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

def hardyDilateFn (s : ℂ) (a : HardySeq r) (k : ℕ × Fin r) : ℂ := s ^ k.1 * a k

theorem hardyDilate_mem (s : ℂ) (hs : ‖s‖ ≤ 1) (a : HardySeq r) :
    Memℓp (hardyDilateFn s a) 2 := by
  apply memℓp_gen
  have hb (k : ℕ × Fin r) : ‖hardyDilateFn s a k‖ ^ 2 ≤ ‖a k‖ ^ 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    rw [hardyDilateFn, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hs)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (hardy_summable_norm_sq a).of_nonneg_of_le (fun _ => sq_nonneg _) hb

def hardyDilate (s : ℂ) (hs : ‖s‖ ≤ 1) (a : HardySeq r) : HardySeq r :=
  ⟨hardyDilateFn s a, hardyDilate_mem s hs a⟩

@[simp] theorem hardyDilate_apply (s : ℂ) (hs : ‖s‖ ≤ 1) (a : HardySeq r) (k : ℕ × Fin r) :
    hardyDilate s hs a k = s ^ k.1 * a k := rfl

theorem hardyDilate_norm_le (s : ℂ) (hs : ‖s‖ ≤ 1) (a : HardySeq r) :
    ‖hardyDilate s hs a‖ ≤ ‖a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hn (b : HardySeq r) : ‖b‖ ^ 2 = ∑' k : ℕ × Fin r, ‖b k‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (p := 2) (by norm_num) b).tsum_eq.symm
  rw [hn, hn]
  apply (hardy_summable_norm_sq (hardyDilate s hs a)).tsum_le_tsum _ (hardy_summable_norm_sq a)
  intro k
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
  rw [hardyDilate_apply, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hs)

def hardyDilateLM (s : ℂ) (hs : ‖s‖ ≤ 1) : HardySeq r →ₗ[ℂ] HardySeq r where
  toFun := hardyDilate s hs
  map_add' a b := by
    ext k
    simp only [hardyDilate_apply, lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c a := by
    ext k
    simp only [hardyDilate_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def hardyDilateCLM (s : ℂ) (hs : ‖s‖ ≤ 1) : HardySeq r →L[ℂ] HardySeq r :=
  (hardyDilateLM s hs).mkContinuous 1 (fun a => by
    change ‖hardyDilate s hs a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using hardyDilate_norm_le s hs a)

theorem hardyDilate_tendsto (s : ℕ → ℂ) (hs : ∀ n, ‖s n‖ ≤ 1)
    (hlim : Tendsto s atTop (𝓝 1)) (a : HardySeq r) :
    Tendsto (fun n => hardyDilate (s n) (hs n) a) atTop (𝓝 a) := by
  let f : ℕ → (ℕ × Fin r) → ℝ := fun n k => ‖((s n) ^ k.1 - 1) * a k‖ ^ 2
  have hb (n : ℕ) (k : ℕ × Fin r) : ‖f n k‖ ≤ 4 * ‖a k‖ ^ 2 := by
    have hp : ‖s n ^ k.1‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hs n)
    have hd : ‖s n ^ k.1 - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖s n ^ k.1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    change |‖(s n ^ k.1 - 1) * a k‖ ^ 2| ≤ 4 * ‖a k‖ ^ 2
    rw [abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg (s n ^ k.1 - 1)]) (sq_nonneg _)
  have hf (k : ℕ × Fin r) : Tendsto (fun n => f n k) atTop (𝓝 0) := by
    have h := (((hlim.pow k.1).sub (tendsto_const_nhds (x := (1 : ℂ)))).mul_const (a k)).norm.pow 2
    simpa only [f, one_pow, sub_self, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)] using h
  have hsum := tendsto_tsum_of_dominated_convergence
    ((hardy_summable_norm_sq a).mul_left 4) hf (Eventually.of_forall hb)
  have hn (n : ℕ) : ‖hardyDilate (s n) (hs n) a - a‖ ^ 2 = ∑' k, f n k := by
    have h := (lp.hasSum_norm (p := 2) (by norm_num)
      (hardyDilate (s n) (hs n) a - a)).tsum_eq.symm
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    refine h.trans (tsum_congr fun k => ?_)
    change ‖s n ^ k.1 * a k - a k‖ ^ 2 = ‖(s n ^ k.1 - 1) * a k‖ ^ 2
    congr 2
    ring
  have hsq : Tendsto (fun n => ‖hardyDilate (s n) (hs n) a - a‖ ^ 2) atTop (𝓝 0) := by
    simpa only [← hn, tsum_zero] using hsum
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h : Tendsto (fun n => Real.sqrt (‖hardyDilate (s n) (hs n) a - a‖ ^ 2))
      atTop (𝓝 (Real.sqrt 0)) := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have heq : (fun n => Real.sqrt (‖hardyDilate (s n) (hs n) a - a‖ ^ 2)) =
      fun n => ‖hardyDilate (s n) (hs n) a - a‖ := by
    funext n
    exact Real.sqrt_sq (norm_nonneg _)
  rw [heq, Real.sqrt_zero] at h
  exact h

end Yau.NodeProofs.D06Aux
