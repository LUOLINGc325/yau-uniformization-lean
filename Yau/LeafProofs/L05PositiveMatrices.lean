import Yau.LeafProofs.L05ComplexRepresentation

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem frobenius_norm_sq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    ‖A‖^2 = ∑ i, ∑ j, (A i j)^2 := by
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow,Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs]

theorem posSemidef_entry_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) : (A i j)^2 ≤ A i i*A j j := by
  have hs : A j i = A i j := by simpa using hA.isHermitian.apply i j
  have hq := discrim_le_zero (a := A i i) (b := 2*A i j) (c := A j j) (fun t => by
    have hh := hA.dotProduct_mulVec_nonneg (Pi.single i t+Pi.single j 1)
    simp [dotProduct,Matrix.mulVec,Pi.single_apply,mul_add,add_mul,
      Finset.sum_add_distrib,hs] at hh
    nlinarith)
  unfold discrim at hq
  nlinarith

theorem posSemidef_norm_le_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : ‖A‖ ≤ Matrix.trace A := by
  have hs : ‖A‖^2 ≤ (Matrix.trace A)^2 := by
    rw [frobenius_norm_sq]
    calc
      _ ≤ ∑ i, ∑ j, A i i*A j j := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => posSemidef_entry_sq_le hA i j
      _ = _ := by simp only [← Finset.mul_sum,← Finset.sum_mul,Matrix.trace,Matrix.diag_apply]; ring
  nlinarith [norm_nonneg A,hA.trace_nonneg]

theorem trace_le_sqrt_card_mul_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Matrix.trace A ≤ Real.sqrt (Fintype.card ι)*‖A‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => A i i) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hcs
  have hd : (∑ i, (A i i)^2) ≤ ‖A‖^2 := by
    rw [frobenius_norm_sq]
    exact Finset.sum_le_sum fun i _ => Finset.single_le_sum
      (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hsq := Real.sq_sqrt hn
  have hs : (Matrix.trace A)^2 ≤ (Real.sqrt (Fintype.card ι)*‖A‖)^2 := by
    simp only [Matrix.trace,Matrix.diag_apply,mul_pow,hsq]
    simpa only [mul_comm] using hcs.trans (mul_le_mul_of_nonneg_right hd hn)
  nlinarith [mul_nonneg (Real.sqrt_nonneg (Fintype.card ι)) (norm_nonneg A)]

theorem complexHessianMap_coe {n : ℕ} (B : Sym n) :
    (complexHessianMap B : Mat n) =
      (1/4 : ℝ) • ((B : Mat n)+(complexJ n).transpose*(B : Mat n)*complexJ n) := by
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  have hB : (B : Mat n).IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr B.property
  have hJ := Matrix.isHermitian_conjTranspose_mul_mul (complexJ n) hB
  have hJT : (complexJ n).conjTranspose = (complexJ n).transpose := by
    ext i j
    simp
  rw [hJT] at hJ
  exact IsSelfAdjoint.smul (IsSelfAdjoint.all _) (hB.add hJ)

theorem complexHessianMap_add {n : ℕ} (A B : Sym n) :
    complexHessianMap (A+B) = complexHessianMap A+complexHessianMap B := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_add,complexHessianMap_coe,Matrix.mul_add,Matrix.add_mul,
    smul_add]
  abel

theorem complexHessianMap_smul {n : ℕ} (c : ℝ) (A : Sym n) :
    complexHessianMap (c • A) = c • complexHessianMap A := by
  apply Subtype.ext
  simp only [selfAdjoint.val_smul,complexHessianMap_coe,Matrix.mul_smul,Matrix.smul_mul,
    ← smul_add,smul_smul]
  congr 1
  ring

theorem complexHessianMap_posSemidef {n : ℕ} (B : Sym n)
    (hB : (B : Mat n).PosSemidef) : (complexHessianMap B : Mat n).PosSemidef := by
  rw [complexHessianMap_coe]
  have hJ := hB.conjTranspose_mul_mul_same (complexJ n)
  have hJT : (complexJ n).conjTranspose = (complexJ n).transpose := by ext i j; simp
  rw [hJT] at hJ
  exact (hB.add hJ).smul (by norm_num : (0 : ℝ) ≤ 1/4)

theorem complexJ_conjugate_norm {n : ℕ} (A : Mat n) :
    ‖(complexJ n).transpose*A*complexJ n‖ = ‖A‖ := by
  rw [Matrix.frobenius_norm_def,Matrix.frobenius_norm_def]
  congr 1
  simp only [Fintype.sum_prod_type,Fin.sum_univ_two,complexJ_conjugate_apply]
  norm_num only [Fin.reduceEq,ite_true,ite_false,one_mul,neg_one_mul,mul_one,
    mul_neg,norm_neg]
  simp only [Finset.sum_add_distrib]
  abel

theorem complexHessianMap_norm_le {n : ℕ} (B : Sym n) :
    ‖complexHessianMap B‖ ≤ ‖B‖/2 := by
  change ‖(complexHessianMap B : Mat n)‖ ≤ ‖(B : Mat n)‖/2
  rw [complexHessianMap_coe,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/4)]
  have hh := norm_add_le (B : Mat n) ((complexJ n).transpose*(B : Mat n)*complexJ n)
  rw [complexJ_conjugate_norm] at hh
  nlinarith

theorem complexHessianMap_trace {n : ℕ} (B : Sym n) :
    Matrix.trace (complexHessianMap B : Mat n) = Matrix.trace (B : Mat n)/2 := by
  rw [complexHessianMap_coe,Matrix.trace_smul,Matrix.trace_add]
  have hh : Matrix.trace ((complexJ n).transpose*(B : Mat n)*complexJ n) =
      Matrix.trace (B : Mat n) := by
    simp [Matrix.trace,Fintype.sum_prod_type,Fin.sum_univ_two,complexJ_conjugate_apply,
      Finset.sum_add_distrib,add_comm]
  rw [hh]
  simp [smul_eq_mul]
  ring

theorem complexHessianMap_norm_lower {n : ℕ} (B : Sym n)
    (hB : (B : Mat n).PosSemidef) :
    ‖B‖ ≤ 2*Real.sqrt (2*n)*‖complexHessianMap B‖ := by
  have htrace := trace_le_sqrt_card_mul_norm (complexHessianMap B : Mat n)
  rw [complexHessianMap_trace] at htrace
  have hcard : (Fintype.card (RIdx n) : ℝ) = 2*n := by simp [RIdx]; ring
  rw [hcard] at htrace
  have hnorm := posSemidef_norm_le_trace hB
  change ‖(B : Mat n)‖ ≤ _
  change _ ≤ 2*Real.sqrt (2*n)*‖(complexHessianMap B : Mat n)‖
  linarith

/-- The fixed complex projection satisfies all of the original Chu H2
hypotheses, with explicit sufficient numerical budgets. -/
theorem complexHessianMap_chuH2 {n : ℕ} {K β : ℝ}
    (hK : 0 < K) (hKhalf : (1/2 : ℝ) ≤ K) (hKdim : 2*Real.sqrt (2*n) ≤ K) :
    Yau.ParabolicCandidates.ChuH2 (n := n) (fun A _ => complexHessianMap A) K β := by
  refine ⟨?_,?_,?_,?_⟩
  · intro A p hp q hq
    simp only [sub_self,norm_zero]
    apply mul_nonneg (mul_nonneg hK.le (by positivity))
    exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (abs_nonneg _) _)
  · intro p hp A B
    exact complexHessianMap_add A B
  · intro p hp c A
    exact complexHessianMap_smul c A
  · intro A hA p hp
    refine ⟨complexHessianMap_posSemidef A hA,?_,?_⟩
    · rw [inv_mul_eq_div,div_le_iff₀ hK]
      have hh := complexHessianMap_norm_lower A hA
      nlinarith [mul_le_mul_of_nonneg_right hKdim (norm_nonneg (complexHessianMap A))]
    · have hh := complexHessianMap_norm_le A
      nlinarith [mul_le_mul_of_nonneg_right hKhalf (norm_nonneg A)]

end Yau.LeafProofs.L05Aux
