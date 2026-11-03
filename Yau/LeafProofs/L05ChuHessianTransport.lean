import Yau.LeafProofs.L05ChuLocalRadius

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

local instance l05ChuHessianTransportSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

def chuBilinearMatrixLinear (n : ℕ) :
    (Space n →L[ℝ] Space n →L[ℝ] ℝ) →ₗ[ℝ] Mat n where
  toFun B := fun i j => B (Yau.realVec i) (Yau.realVec j)
  map_add' B C := by ext i j; rfl
  map_smul' c B := by ext i j; rfl

def chuHessianBilinearLinear (n : ℕ) :
    (Space n →L[ℝ] Space n →L[ℝ] ℝ) →ₗ[ℝ] Sym n :=
  (selfAdjointPart ℝ).comp (chuBilinearMatrixLinear n)

def chuHessianTransportConstant (n : ℕ) : ℝ := 1+(Fintype.card (RIdx n):ℝ)^2

theorem chuHessianTransportConstant_pos (n : ℕ) : 0 < chuHessianTransportConstant n := by
  unfold chuHessianTransportConstant
  positivity

theorem chuHessianBilinearLinear_apply {n : ℕ} (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    chuHessianBilinearLinear n B=sym (fun i j => B (Yau.realVec i) (Yau.realVec j)) := rfl

theorem chuHessianBilinear_norm_le {n : ℕ} (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    ‖chuHessianBilinearLinear n B‖ ≤ chuHessianTransportConstant n*‖B‖ := by
  let A := chuBilinearMatrixLinear n B
  have he (i j : RIdx n) : |A i j| ≤ ‖B‖ := by
    change |B (Yau.realVec i) (Yau.realVec j)| ≤ ‖B‖
    have hvec (k : RIdx n) : ‖Yau.realVec k‖=1 := by
      by_cases h : k.2=0 <;> simp [Yau.realVec,h,norm_smul]
    have hh := ((B (Yau.realVec i)).le_opNorm (Yau.realVec j)).trans
      (mul_le_mul_of_nonneg_right (B.le_opNorm (Yau.realVec i)) (norm_nonneg _))
    simpa only [Real.norm_eq_abs,hvec,mul_one] using hh
  have hsum : ‖A‖ ≤ ∑ i : RIdx n, ∑ j : RIdx n, |A i j| := by
    rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_iff.mpr
    refine ⟨Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)),?_⟩
    simp only [Real.norm_eq_abs,Real.rpow_two]
    exact (Finset.sum_le_sum (fun i _ => Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => abs_nonneg (A i j)))).trans (Finset.sum_sq_le_sq_sum_of_nonneg
        (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg (A i j))))
  have hAn : ‖A‖ ≤ (Fintype.card (RIdx n):ℝ)^2*‖B‖ := by
    apply hsum.trans
    calc
      _ ≤ ∑ i : RIdx n, ∑ j : RIdx n, ‖B‖ :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => he i j))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have hsym : ‖sym A‖ ≤ ‖A‖ := by
    change ‖(sym A : Mat n)‖ ≤ _
    rw [sym_coe_formula,norm_smul,Real.norm_eq_abs]
    have hh := norm_add_le A A.transpose
    rw [Matrix.frobenius_norm_transpose] at hh
    norm_num
    linarith only [hh]
  exact hsym.trans (hAn.trans (by unfold chuHessianTransportConstant; nlinarith only [norm_nonneg B]))

theorem hessian_holderBound_of_spatialDD {n : ℕ} {eta C : ℝ} {Q : Set (Point n)}
    {u : Point n → ℝ} (hH : HolderBound eta Q (spatialDD u) C) :
    HolderBound eta Q (hessian u) (chuHessianTransportConstant n*C) := by
  have hK := (chuHessianTransportConstant_pos n).le
  refine ⟨mul_nonneg hK hH.1,?_,?_⟩
  · intro p hp
    exact (chuHessianBilinear_norm_le (spatialDD u p)).trans
      (mul_le_mul_of_nonneg_left (hH.2.1 p hp) hK)
  · intro p hp q hq
    have hn := chuHessianBilinear_norm_le (spatialDD u p-spatialDD u q)
    have he := (chuHessianBilinearLinear n).map_sub (spatialDD u p) (spatialDD u q)
    rw [he] at hn
    exact hn.trans (by
      calc
        _ ≤ chuHessianTransportConstant n*(C*holderWeight eta p q) :=
          mul_le_mul_of_nonneg_left (hH.2.2 p hp q hq) hK
        _ = _ := by ring)

end Yau.LeafProofs.L05Aux
