import Yau.LeafProofs.L18

open Matrix Set
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def complexDirectionCombination [Fintype ι] (dir : ι → E) (v : ι → ℂ) : E :=
  ∑ i, v i • dir i

theorem complex_smul_real_im (c : ℂ) (v : E) :
    c • v = c.re • v+c.im • (Complex.I • v) := by
  calc
    c • v = ((c.re:ℂ)+(c.im:ℂ)*Complex.I) • v :=
      congrArg (fun z : ℂ => z • v) (Complex.re_add_im c).symm
    _ = _ := by
      rw [add_smul,mul_smul]
      rfl

theorem realBilin_complex_combinations [Fintype ι]
    (A : E →L[ℝ] E →L[ℝ] ℝ) (dir : ι → E) (v w : ι → ℂ) :
    A (complexDirectionCombination dir v) (complexDirectionCombination dir w) =
      ∑ i, ∑ j, (
        (v i).re*(w j).re*A (dir i) (dir j)+
        (v i).re*(w j).im*A (dir i) (Complex.I • dir j)+
        (v i).im*(w j).re*A (Complex.I • dir i) (dir j)+
        (v i).im*(w j).im*A (Complex.I • dir i) (Complex.I • dir j)) := by
  unfold complexDirectionCombination
  rw [map_sum A,_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum (A (v i • dir i))]
  apply Finset.sum_congr rfl
  intro j _
  rw [complex_smul_real_im (v i),complex_smul_real_im (w j)]
  simp only [map_add,_root_.add_apply,map_smul,_root_.smul_apply,smul_eq_mul]
  ring

/-- The actual nested Wirtinger matrix is Hermitian for any finite
family of complex directions, not only the standard coordinate family. -/
theorem leviMatrix_isHermitian {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (dir : ι → E) :
    (leviMatrix f z dir).IsHermitian := by
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  apply Matrix.IsHermitian.ext
  intro i j
  apply Complex.ext
  · simp only [Complex.star_def,Complex.conj_re,
      (Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hf dir j i).1,
      (Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hf dir i j).1]
    rw [hs (dir i) (dir j),hs (Complex.I • dir i) (Complex.I • dir j)]
  · simp only [Complex.star_def,Complex.conj_im,
      (Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hf dir j i).2,
      (Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hf dir i j).2]
    rw [hs (dir i) (Complex.I • dir j),hs (Complex.I • dir i) (dir j)]
    ring

/-- Exact finite-direction quadratic identity for the actual Levi matrix. -/
theorem leviMatrix_quadratic_re [Fintype ι] {f : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (dir : ι → E) (v : ι → ℂ) :
    (star v ⬝ᵥ (leviMatrix f z dir *ᵥ v)).re =
      (fderiv ℝ (fderiv ℝ f) z (complexDirectionCombination dir v) (complexDirectionCombination dir v)+
        fderiv ℝ (fderiv ℝ f) z (Complex.I • complexDirectionCombination dir v)
          (Complex.I • complexDirectionCombination dir v))/4 := by
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  have hI : Complex.I • complexDirectionCombination dir v =
      complexDirectionCombination dir (fun i => Complex.I*v i) := by
    simp only [complexDirectionCombination,Finset.smul_sum,mul_smul]
  rw [hI,realBilin_complex_combinations,realBilin_complex_combinations]
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,Complex.re_sum,Pi.star_apply,
    Complex.star_def,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,zero_add,mul_neg,neg_mul,neg_neg]
  rw [←Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [(Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hf dir i j).1,
    (Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hf dir i j).2,
    hs (dir j) (dir i),hs (Complex.I • dir j) (Complex.I • dir i),
    hs (dir j) (Complex.I • dir i),hs (Complex.I • dir j) (dir i)]
  ring

end Yau.NodeProofs.E02Aux
