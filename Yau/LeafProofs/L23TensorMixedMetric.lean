import Yau.LeafProofs.L23TensorMetricAlgebra

/-! Positivity and operator estimates for a separate metric in each slot. -/

noncomputable section
open scoped Matrix MatrixOrder

namespace Yau.LeafProofs.L23Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def mixedTensorNormSq (H : Fin r → Matrix ι ι ℝ) (A : (Fin r → ι) → ℝ) : ℝ :=
  ∑ v : Fin r → ι, ∑ w : Fin r → ι, A v*A w*∏ j : Fin r, H j (v j) (w j)

theorem posSemidef_exists_gram_factor (H : Matrix ι ι ℝ) (hH : H.PosSemidef) :
    ∃ D : Matrix ι ι ℝ, H=D*Dᵀ := by
  let D := CFC.sqrt H
  have hD : Dᵀ=D := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,sub_zero] using
      (CFC.sqrt_nonneg H).isHermitian.eq
  refine ⟨D,?_⟩
  rw [hD]
  simpa only [pow_two] using (CFC.sq_sqrt H hH.nonneg).symm

theorem mixedTensorNormSq_nonneg (H : Fin r → Matrix ι ι ℝ)
    (hH : ∀ j, (H j).PosSemidef) (A : (Fin r → ι) → ℝ) :
    0 ≤ mixedTensorNormSq H A := by
  choose D hD using fun j => posSemidef_exists_gram_factor (H j) (hH j)
  have hp (v w : Fin r → ι) : (∏ j : Fin r, H j (v j) (w j)) =
      ∑ a : Fin r → ι, (∏ j : Fin r, D j (v j) (a j))*(∏ j : Fin r, D j (w j) (a j)) := by
    simp only [hD,Matrix.mul_apply,Matrix.transpose_apply,←Finset.prod_mul_distrib]
    exact Fintype.prod_sum _
  have heq : mixedTensorNormSq H A =
      ∑ a : Fin r → ι, (∑ v : Fin r → ι, A v*∏ j : Fin r, D j (v j) (a j))^2 := by
    unfold mixedTensorNormSq
    simp_rw [hp,Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext v
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    conv_rhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    congr 1
    funext a
    congr 1
    funext v
    congr 1
    funext w
    ring
  rw [heq]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

def tensorSlotMetricContraction (H J : Matrix ι ι ℝ) (s : Fin r)
    (A B : (Fin r → ι) → ℝ) : ℝ :=
  ∑ v : Fin r → ι, ∑ w : Fin r → ι,
    A v*B w*J (v s) (w s)*∏ j ∈ Finset.univ.erase s, H (v j) (w j)

theorem mixedTensorNormSq_slot (H J : Matrix ι ι ℝ) (s : Fin r)
    (A : (Fin r → ι) → ℝ) :
    mixedTensorNormSq (fun j => if j=s then J else H) A =
      tensorSlotMetricContraction H J s A A := by
  unfold mixedTensorNormSq tensorSlotMetricContraction
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  rw [←Finset.mul_prod_erase Finset.univ
    (fun j : Fin r => (if j=s then J else H) (v j) (w j)) (Finset.mem_univ s)]
  simp only [ite_eq_left]
  have hp : (∏ j ∈ Finset.univ.erase s, (if j=s then J else H) (v j) (w j)) =
      ∏ j ∈ Finset.univ.erase s, H (v j) (w j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.mem_erase.mp hj).1]
  rw [hp]
  ring

theorem tensorSlotMetricContraction_self (H : Matrix ι ι ℝ) (s : Fin r)
    (A : (Fin r → ι) → ℝ) :
    tensorSlotMetricContraction H H s A A=tensorContraction H A A := by
  rw [←mixedTensorNormSq_slot]
  simp only [ite_self,mixedTensorNormSq,tensorContraction]

theorem tensorSlotMetricContraction_le (H J : Matrix ι ι ℝ) (c : ℝ)
    (hH : H.PosSemidef) (hJ : (c•H-J).PosSemidef) (s : Fin r)
    (A : (Fin r → ι) → ℝ) :
    tensorSlotMetricContraction H J s A A ≤ c*tensorContraction H A A := by
  have hp (j : Fin r) : ((fun j => if j=s then c•H-J else H) j).PosSemidef := by
    dsimp only
    split_ifs <;> assumption
  have hn := mixedTensorNormSq_nonneg _ hp A
  rw [mixedTensorNormSq_slot] at hn
  have heq : tensorSlotMetricContraction H (c•H-J) s A A =
      c*tensorSlotMetricContraction H H s A A-tensorSlotMetricContraction H J s A A := by
    simp only [tensorSlotMetricContraction,Matrix.sub_apply,Matrix.smul_apply,
      smul_eq_mul,mul_sub,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc,mul_left_comm]
  rw [heq,tensorSlotMetricContraction_self] at hn
  linarith

theorem tensorConnectionAction_contraction_le (H D : Matrix ι ι ℝ) (c : ℝ)
    (hH : H.PosSemidef) (hD : (c•H-D*H).PosSemidef)
    (A : (Fin r → ι) → ℝ) :
    tensorContraction H (tensorConnectionAction D A) A ≤
      (r : ℝ)*c*tensorContraction H A A := by
  rw [tensorContraction_connectionAction_left]
  calc
    _ ≤ ∑ s : Fin r, c*tensorContraction H A A := by
      apply Finset.sum_le_sum
      intro s _
      rw [←tensorSlotMetricAction_left]
      exact tensorSlotMetricContraction_le H (D*H) c hH hD s A
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem tensorMetricVariation_scaled_action (H D : Matrix ι ι ℝ) (σ : ℝ)
    (A : (Fin r → ι) → ℝ) :
    tensorMetricVariation H (σ•(D*H)) A A =
      σ*tensorContraction H (tensorConnectionAction D A) A := by
  rw [tensorContraction_connectionAction_left]
  unfold tensorMetricVariation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [←tensorSlotMetricAction_left]
  simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc,mul_left_comm]

end Yau.LeafProofs.L23Aux
