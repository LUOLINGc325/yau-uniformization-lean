import Yau.Proofs.F03WirtingerDifferential
import Yau.LeafProofs.L22LeviCalculus

/-! Computed product and real scalar-chain rules for the actual Levi matrix. -/
noncomputable section
open scoped ContDiff Matrix ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux
variable {n : ℕ}

def realFirstCovector (f : ComplexVector n → ℝ) (z : ComplexVector n) : Fin n → ℂ :=
  fun i => (1/2:ℂ)*((fderiv ℝ f z (stdVec i):ℂ)-Complex.I*(fderiv ℝ f z (Complex.I • stdVec i):ℂ))

theorem realFirstCovector_eq (f : ComplexVector n → ℝ) (z : ComplexVector n) :
    realFirstCovector f z=WithLp.ofLp (realWirtingerMap n (fderiv ℝ f z)) := by
  rw [realWirtingerMap_apply]
  rfl

theorem leviC_real_mul {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    leviC (fun w => f w*g w) z=(f z:ℂ) • leviC g z+(g z:ℂ) • leviC f z+
      Matrix.vecMulVec (star (realFirstCovector f z)) (realFirstCovector g z)+
      Matrix.vecMulVec (star (realFirstCovector g z)) (realFirstCovector f z) := by
  ext i j
  apply Complex.ext
  · simp only [leviC,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.add_re,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      (leviMatrix_entry_re_im (hf.mul hg) stdVec i j).1,
      (leviMatrix_entry_re_im hf stdVec i j).1,(leviMatrix_entry_re_im hg stdVec i j).1,
      secondFDeriv_mul hf hg]
    simp [Matrix.vecMulVec,realFirstCovector,Complex.mul_re,Complex.mul_im]
    <;> ring
  · simp only [leviC,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.add_im,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      (leviMatrix_entry_re_im (hf.mul hg) stdVec i j).2,
      (leviMatrix_entry_re_im hf stdVec i j).2,(leviMatrix_entry_re_im hg stdVec i j).2,
      secondFDeriv_mul hf hg]
    simp [Matrix.vecMulVec,realFirstCovector,Complex.mul_re,Complex.mul_im]
    <;> ring

theorem leviC_real_scalar_comp {f : ComplexVector n → ℝ} {F : ℝ → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hF : ContDiffAt ℝ 2 F (f z)) :
    leviC (F ∘ f) z=Complex.ofReal (deriv F (f z)) • leviC f z+
      Complex.ofReal (deriv (deriv F) (f z)) •
        Matrix.vecMulVec (star (realFirstCovector f z)) (realFirstCovector f z) := by
  have hComp := hF.comp z hf
  have hSecond (v w : ComplexVector n) :
      fderiv ℝ (fderiv ℝ (F ∘ f)) z v w=
        deriv F (f z)*fderiv ℝ (fderiv ℝ f) z v w+
        deriv (deriv F) (f z)*(fderiv ℝ f z v*fderiv ℝ f z w) := by
    rw [secondFDeriv_comp hf hF,secondFDeriv_scalar_apply hF,fderiv_eq_deriv_mul]
    ring
  ext i j
  apply Complex.ext
  · simp only [leviC,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.add_re,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      (leviMatrix_entry_re_im hComp stdVec i j).1,(leviMatrix_entry_re_im hf stdVec i j).1,hSecond]
    simp [Matrix.vecMulVec,realFirstCovector,Complex.mul_re,Complex.mul_im]
    <;> ring
  · simp only [leviC,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.add_im,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      (leviMatrix_entry_re_im hComp stdVec i j).2,(leviMatrix_entry_re_im hf stdVec i j).2,hSecond]
    simp [Matrix.vecMulVec,realFirstCovector,Complex.mul_re,Complex.mul_im]
    <;> ring

end Yau.Proofs.F03Aux
