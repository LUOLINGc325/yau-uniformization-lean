import Yau.Proofs.D06HardyParseval

/-! Constant Hardy vectors and the continuous zeroth-coefficient map. -/

open scoped lp

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

def hardyConst (v : EuclideanSpace ℂ (Fin r)) : HardySeq r :=
  ∑ j : Fin r, lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (0, j) (v j)

@[simp] theorem hardyConst_apply (v : EuclideanSpace ℂ (Fin r)) (n : ℕ) (j : Fin r) :
    hardyConst v (n, j) = if n = 0 then v j else 0 := by
  classical
  have hs : hardyConst v (n, j) = ∑ i : Fin r,
      lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (0, i) (v i) (n, j) :=
    map_sum (lp.evalCLM ℂ (fun _ : ℕ × Fin r => ℂ) 2 (n, j))
      (fun i : Fin r => lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (0, i) (v i)) Finset.univ
  apply hs.trans
  by_cases hn : n = 0
  · subst n
    simp [lp.single_apply, Pi.single_apply, Prod.mk.injEq]
  · simp [lp.single_apply, Pi.single_apply, Prod.mk.injEq, hn]

@[simp] theorem hardyConst_add (v w : EuclideanSpace ℂ (Fin r)) :
    hardyConst (v + w) = hardyConst v + hardyConst w := by
  ext ⟨n, j⟩
  by_cases hn : n = 0 <;> simp [hn]

@[simp] theorem hardyConst_smul (c : ℂ) (v : EuclideanSpace ℂ (Fin r)) :
    hardyConst (c • v) = c • hardyConst v := by
  ext ⟨n, j⟩
  by_cases hn : n = 0 <;> simp [hn]

theorem hardyConst_norm_sq (v : EuclideanSpace ℂ (Fin r)) :
    ‖hardyConst v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [← hardy_column_norm_sum (hardyConst v), EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  simp only [hardyConst_apply, apply_ite norm, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  exact tsum_ite_eq 0 (fun _ : ℕ => ‖v j‖ ^ 2)

def hardyConstLI : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] HardySeq r where
  toFun := hardyConst
  map_add' := hardyConst_add
  map_smul' := hardyConst_smul
  norm_map' v := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hardyConst_norm_sq v)

def hardyCoeffZero (a : HardySeq r) : EuclideanSpace ℂ (Fin r) :=
  WithLp.toLp 2 (fun j => a (0, j))

theorem hardyCoeffZero_norm_sq_le (a : HardySeq r) : ‖hardyCoeffZero a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← hardy_column_norm_sum a]
  apply Finset.sum_le_sum
  intro j _
  exact (hardy_column_summable_norm_sq a j).le_tsum 0 fun n _ => sq_nonneg _

theorem hardyCoeffZero_norm_le (a : HardySeq r) : ‖hardyCoeffZero a‖ ≤ ‖a‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hardyCoeffZero_norm_sq_le a)

def hardyCoeffZeroLM : HardySeq r →ₗ[ℂ] EuclideanSpace ℂ (Fin r) where
  toFun := hardyCoeffZero
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def hardyCoeffZeroCLM : HardySeq r →L[ℂ] EuclideanSpace ℂ (Fin r) :=
  hardyCoeffZeroLM.mkContinuous 1 (fun a => by
    change ‖hardyCoeffZero a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using hardyCoeffZero_norm_le a)

@[simp] theorem hardyCoeffZero_const (v : EuclideanSpace ℂ (Fin r)) :
    hardyCoeffZero (hardyConst v) = v := by
  ext j
  change hardyConst v (0, j) = v j
  simpa only [ite_true] using hardyConst_apply v 0 j

end Yau.NodeProofs.D06Aux
