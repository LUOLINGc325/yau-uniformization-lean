import Yau.Proofs.F05BootstrapDefinitions

/-! Normal recovery isolates the actual diagonal principal entry. Every
other principal term is retained; each such term has at most one normal
index. No symmetry or normalization of the supplied matrix is assumed. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_elliptic_diagonal_lower {Q : Set (Point n)} {a : Point n → Mat n}
    {lam upper : ℝ} (hEll : Elliptic Q a lam upper) {z : Point n} (hz : z ∈ Q) (j : RIdx n) :
    lam ≤ a z j j := by
  classical
  have h := ((hEll.2.2 z hz).2 (Pi.single j (1 : ℝ))).1
  simpa [Pi.single_apply,mul_ite,ite_mul] using h

theorem F05_matrix_sum_except_diagonal (j : RIdx n) (A H : Mat n) :
    (∑ i,∑ k,A i k*H i k) = A j j*H j j+
      ∑ i,∑ k,if i = j ∧ k = j then 0 else A i k*H i k := by
  classical
  have hPoint (i k : RIdx n) :
      A i k*H i k = (if i = j ∧ k = j then A i k*H i k else 0)+
        (if i = j ∧ k = j then 0 else A i k*H i k) := by
    by_cases h : i = j ∧ k = j <;> simp [h]
  conv_lhs => enter [2,i,2,k]; rw [hPoint i k]
  simp only [Finset.sum_add_distrib]
  congr 1
  simp [ite_and]

theorem F05_relative_normal_recovery {X : Set (Space n)} {I : Set ℝ}
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (R u : Point n → ℝ)
    {lam upper : ℝ} (hEll : Elliptic (X ×ˢ I) a lam upper) {z : Point n} (hz : z ∈ X ×ˢ I)
    (hPDE : F05RelT I u z = Real.exp (-u z)*
      ((∑ i,∑ k,a z i k*F05RelDD X u z (realVec i) (realVec k))+
        ∑ i,b z i*F05RelD X u z (realVec i))+(1-Real.exp (-u z))*R z)
    (j : RIdx n) :
    F05RelDD X u z (realVec j) (realVec j) = (a z j j)⁻¹*
      (Real.exp (u z)*F05RelT I u z-(Real.exp (u z)-1)*R z-
        (∑ i,∑ k,if i = j ∧ k = j then 0 else a z i k*F05RelDD X u z (realVec i) (realVec k))-
        ∑ i,b z i*F05RelD X u z (realVec i)) := by
  have hAj : 0 < a z j j := hEll.1.trans_le (F05_elliptic_diagonal_lower hEll hz j)
  have hExp : Real.exp (u z) ≠ 0 := (Real.exp_pos _).ne'
  have hLinear : Real.exp (u z)*F05RelT I u z-(Real.exp (u z)-1)*R z =
      (∑ i,∑ k,a z i k*F05RelDD X u z (realVec i) (realVec k))+
        ∑ i,b z i*F05RelD X u z (realVec i) := by
    rw [Real.exp_neg] at hPDE
    field_simp [hExp] at hPDE
    nlinarith only [hPDE]
  have hSplit := F05_matrix_sum_except_diagonal j (a z)
    (fun i k => F05RelDD X u z (realVec i) (realVec k))
  rw [hLinear,hSplit]
  field_simp [hAj.ne']
  ring

end Yau.Proofs.F05Aux
