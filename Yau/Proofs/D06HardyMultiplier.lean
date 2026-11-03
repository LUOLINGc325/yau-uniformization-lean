import Yau.Proofs.D06HardyEvaluationBound
import Yau.Proofs.D06ShiftSynthesis

/-! A bounded shift-commuting Hardy operator has its actual holomorphic matrix
symbol, obtained from the images of the constant coordinate vectors. -/

open scoped lp

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

def hardySymbol (T : HardySeq r →L[ℂ] HardySeq r) (z : ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun i j => hardyEvalEntry (T (hardyConst (EuclideanSpace.single j 1))) i z

theorem hardyConst_single (j : Fin r) (c : ℂ) :
    hardyConst (EuclideanSpace.single j c) =
      lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (0, j) c := by
  ext ⟨n, i⟩
  simp only [hardyConst_apply, PiLp.single_apply, lp.single_apply, Pi.single_apply,
    Prod.mk.injEq]
  by_cases hn : n = 0 <;> by_cases hi : i = j <;> simp [hn, hi, eq_comm]

theorem hardyEval_single (n : ℕ) (j : Fin r) (c z : ℂ) :
    hardyEval (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) c) z =
      (z ^ n * c) • EuclideanSpace.single j 1 := by
  ext i
  change hardyEvalEntry (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) c) i z = _
  rw [hardyEvalEntry_eq_tsum]
  simp only [lp.single_apply, Pi.single_apply, Prod.mk.injEq, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  by_cases hi : i = j
  · subst i
    simp only [and_true, mul_ite, mul_zero, ite_true, mul_one]
    exact tsum_ite_eq n (fun k : ℕ => z ^ k * c)
  · simp [hi, Ne.symm hi]

theorem hardySymbol_const (T : HardySeq r →L[ℂ] HardySeq r) (z : ℂ) (hz : ‖z‖ < 1)
    (v : EuclideanSpace ℂ (Fin r)) :
    Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (hardySymbol T z) v = hardyEval (T (hardyConst v)) z := by
  classical
  let F := (hardyEvalCLM z hz).comp (T.comp hardyConstLI.toContinuousLinearMap)
  have hv : v = ∑ j : Fin r, v j • EuclideanSpace.single j 1 := by
    ext i
    simp [PiLp.single_apply, Pi.single_apply]
  have hF : F v = ∑ j : Fin r, v j • F (EuclideanSpace.single j 1) := by
    conv_lhs => arg 2; rw [hv]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact map_smul F (v j) _
  ext i
  have hf : hardyEvalEntry (T (hardyConst v)) i z =
      ∑ j : Fin r, v j * hardyEvalEntry (T (hardyConst (EuclideanSpace.single j 1))) i z := by
    calc
      _ = EuclideanSpace.proj i (F v) := rfl
      _ = EuclideanSpace.proj i (∑ j : Fin r, v j • F (EuclideanSpace.single j 1)) :=
        congrArg (EuclideanSpace.proj i) hF
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul]
        rfl
  change (∑ j : Fin r, hardySymbol T z i j * v j) = _
  simpa only [hardySymbol, hardyEval, mul_comm] using hf.symm

theorem hardyOperator_single (T : HardySeq r →L[ℂ] HardySeq r)
    (hT : ∀ a, T (hardyShift a) = hardyShift (T a)) (n : ℕ) (j : Fin r) (c : ℂ) :
    T (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) c) =
      c • (hardyShiftLI ^ n) (T (hardyConst (EuclideanSpace.single j 1))) := by
  induction n with
  | zero =>
    have hc : lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (0, j) c =
        c • lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (0, j) 1 := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [hc, map_smul, hardyConst_single]
    rfl
  | succ n ih =>
    rw [← hardyShift_single, hT, ih, hardyShift_smul, pow_succ']
    rfl

theorem hardyEval_shift_pow (a : HardySeq r) (n : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    hardyEval ((hardyShiftLI ^ n) a) z = z ^ n • hardyEval a z := by
  induction n with
  | zero =>
    simp only [pow_zero, one_smul]
    rfl
  | succ n ih =>
    rw [pow_succ']
    change hardyEval (hardyShift ((hardyShiftLI ^ n) a)) z = _
    rw [hardyEval_shift _ _ hz, ih, smul_smul, pow_succ']

theorem hardySymbol_multiplier (T : HardySeq r →L[ℂ] HardySeq r)
    (hT : ∀ a, T (hardyShift a) = hardyShift (T a)) (z : ℂ) (hz : ‖z‖ < 1)
    (a : HardySeq r) :
    hardyEval (T a) z = Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (hardySymbol T z) (hardyEval a z) := by
  have hCLM : (hardyEvalCLM z hz).comp T =
      (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (hardySymbol T z)).comp (hardyEvalCLM z hz) := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
    rintro ⟨n, j⟩
    apply ContinuousLinearMap.ext
    intro c
    change hardyEval (T (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) c)) z =
      Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) (hardySymbol T z)
        (hardyEval (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, j) c) z)
    rw [hardyOperator_single T hT, hardyEval_single, map_smul]
    change hardyEvalCLM z hz (c • (hardyShiftLI ^ n)
      (T (hardyConst (EuclideanSpace.single j 1)))) = _
    rw [map_smul]
    change c • hardyEval ((hardyShiftLI ^ n) (T (hardyConst (EuclideanSpace.single j 1)))) z = _
    rw [hardyEval_shift_pow _ _ _ hz, hardySymbol_const T z hz, smul_smul]
    rw [mul_comm c]
  exact DFunLike.congr_fun hCLM a

end Yau.NodeProofs.D06Aux
