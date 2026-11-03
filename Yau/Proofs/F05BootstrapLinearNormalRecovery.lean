import Yau.Proofs.F05BootstrapNormalIdentity

/-! Every computed differentiated equation isolates its actual normal
principal entry with the full finite commutator source retained. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

theorem F05_linear_normal_recovery {X : Set (Space n)} {I : Set ℝ}
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (F v : Point n → ℝ)
    {lam upper : ℝ} (hEll : Elliptic (X ×ˢ I) a lam upper) {z : Point n} (hz : z ∈ X ×ˢ I)
    (hPDE : F05RelOp X I a b v z = F z) (j : RIdx n) :
    F05RelDD X v z (realVec j) (realVec j) = (a z j j)⁻¹*
      (F05RelT I v z-F z-
        (∑ i,∑ k,if i = j ∧ k = j then 0 else a z i k*F05RelDD X v z (realVec i) (realVec k))-
        ∑ i,b z i*F05RelD X v z (realVec i)) := by
  have hAj : 0 < a z j j := hEll.1.trans_le (F05_elliptic_diagonal_lower hEll hz j)
  have hSplit := F05_matrix_sum_except_diagonal j (a z)
    (fun i k => F05RelDD X v z (realVec i) (realVec k))
  unfold F05RelOp at hPDE
  rw [hSplit] at hPDE
  field_simp [hAj.ne']
  nlinarith only [hPDE]

end Yau.Proofs.F05Aux
