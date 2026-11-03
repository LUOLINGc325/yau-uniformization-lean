import Yau.LeafProofs.L17BanachRadialLogarithmDerivative

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BanachRadialLogarithmAux

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]

@[simp] theorem radialLogTerm_zero (z : A) (t : ℝ) : radialLogTerm A z t 0=z := by
  simp [radialLogTerm]

theorem radialLogTerm_mul_left (z : A) (t : ℝ) (k : ℕ) :
    (t • z)*radialLogTerm A z t k= -radialLogTerm A z t (k+1) := by
  simp only [radialLogTerm,smul_mul_smul_comm,← pow_succ',← neg_smul]
  congr 1
  simp only [pow_succ]
  ring

theorem radialLogTerm_mul_right (z : A) (t : ℝ) (k : ℕ) :
    radialLogTerm A z t k*(t • z)= -radialLogTerm A z t (k+1) := by
  simp only [radialLogTerm,smul_mul_smul_comm,← pow_succ,← neg_smul]
  congr 1
  simp only [pow_succ]
  ring

@[simp] theorem radialLogDerivative_zero (z : A) : radialLogDerivative A z 0=z := by
  unfold radialLogDerivative
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    simp [radialLogTerm,zero_pow hk]

variable [CompleteSpace A]

theorem radialLogDerivative_head_tail {z : A} (hz : ‖z‖ < 1) {t : ℝ} (ht : |t| ≤ 1) :
    z+(∑' k : ℕ, radialLogTerm A z t (k+1))=radialLogDerivative A z t := by
  have h : Summable (radialLogTerm A z t) := radialLogDerivative_summable A hz ht
  simpa only [Finset.sum_range_one,radialLogTerm_zero,radialLogDerivative] using
    h.sum_add_tsum_nat_add 1

theorem radialLogDerivative_mul_left {z : A} (hz : ‖z‖ < 1) {t : ℝ} (ht : |t| ≤ 1) :
    (1+t • z)*radialLogDerivative A z t=z := by
  have h : Summable (radialLogTerm A z t) := radialLogDerivative_summable A hz ht
  have htel : (t • z)*radialLogDerivative A z t= -(∑' k : ℕ, radialLogTerm A z t (k+1)) := by
    rw [radialLogDerivative,← h.tsum_mul_left]
    simp only [radialLogTerm_mul_left,tsum_neg]
  rw [add_mul,one_mul,htel,← radialLogDerivative_head_tail A hz ht]
  abel

theorem radialLogDerivative_mul_right {z : A} (hz : ‖z‖ < 1) {t : ℝ} (ht : |t| ≤ 1) :
    radialLogDerivative A z t*(1+t • z)=z := by
  have h : Summable (radialLogTerm A z t) := radialLogDerivative_summable A hz ht
  have htel : radialLogDerivative A z t*(t • z)= -(∑' k : ℕ, radialLogTerm A z t (k+1)) := by
    rw [radialLogDerivative,← h.tsum_mul_right]
    simp only [radialLogTerm_mul_right,tsum_neg]
  rw [mul_add,mul_one,htel,← radialLogDerivative_head_tail A hz ht]
  abel

theorem radialLogDerivative_eq_mul_of_left_inverse {z : A} (hz : ‖z‖ < 1)
    {t : ℝ} (ht : |t| ≤ 1) (B : A) (hB : B*(1+t • z)=1) :
    radialLogDerivative A z t=B*z := by
  calc
    radialLogDerivative A z t=1*radialLogDerivative A z t := (one_mul _).symm
    _ = (B*(1+t • z))*radialLogDerivative A z t := by rw [hB]
    _ = B*((1+t • z)*radialLogDerivative A z t) := mul_assoc _ _ _
    _ = B*z := by rw [radialLogDerivative_mul_left A hz ht]

end Yau.LeafProofs.L17BanachRadialLogarithmAux
