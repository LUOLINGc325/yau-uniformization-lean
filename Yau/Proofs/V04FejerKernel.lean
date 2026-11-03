import Yau.Proofs.V04FejerCounting
import Yau.Proofs.V04ScalarFejer
import Yau.Proofs.V03FourierKernel

/-! The actual triangular Fejer weights are the Fourier expansion of a
nonnegative normalized square kernel. All constants retain period 2pi
normalization, including the zero-frequency case. -/

open MeasureTheory AddCircle
open scoped Topology ComplexConjugate
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {T : ℝ} [hT : Fact (0 < T)]

def fejerGeometric (P : ℕ) : C(AddCircle T, ℂ) :=
  ∑ r ∈ Finset.Icc (0 : ℤ) P, fourier r

def fejerKernel (P : ℕ) (x : AddCircle T) : ℝ := ‖fejerGeometric P x‖ ^ 2 / (P + 1)

theorem fejerKernel_nonneg (P : ℕ) (x : AddCircle T) : 0 ≤ fejerKernel P x := by
  exact div_nonneg (sq_nonneg _) (by positivity)

theorem fejerKernel_continuous (P : ℕ) : Continuous (fejerKernel (T := T) P) :=
  ((fejerGeometric P).continuous.norm.pow 2).div_const _

theorem fejerGeometric_norm_sq (P : ℕ) (x : AddCircle T) :
    ((‖fejerGeometric P x‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ Finset.Icc (-(P : ℤ)) P, (((P : ℤ) + 1 - |k|).toNat : ℂ) * fourier k x := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, mul_comm]
  calc
    _ = ∑ p ∈ (Finset.Icc (0 : ℤ) P).product (Finset.Icc (0 : ℤ) P), fourier (p.1 - p.2) x := by
      simp only [fejerGeometric, ContinuousMap.sum_apply, map_sum, Finset.sum_mul,
        Finset.mul_sum, Finset.product_eq_sprod, Finset.sum_product]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      rw [sub_eq_add_neg, fourier_add, fourier_neg]
    _ = _ := by simpa only [nsmul_eq_mul] using fejer_difference_sum P (fun k => fourier k x)

theorem fejerKernel_eq_fourier_sum (P : ℕ) (x : AddCircle T) :
    (fejerKernel P x : ℂ) =
      ∑ k ∈ Finset.Icc (-(P : ℤ)) P, (fejerMultiplier P k : ℂ) * fourier k x := by
  rw [fejerKernel, Complex.ofReal_div, fejerGeometric_norm_sq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkabs : |k| ≤ (P : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hk)
  have hn : 0 ≤ (P : ℤ) + 1 - |k| := by omega
  have hcast : ((((P : ℤ) + 1 - |k|).toNat : ℕ) : ℂ) =
      (P : ℂ) + 1 - ((|(k : ℝ)| : ℝ) : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  rw [hcast, fejerMultiplier, if_pos hk]
  push_cast
  have hden : (P : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero P)
  field_simp
  <;> ring

theorem fejerGeometric_integral_norm_sq (P : ℕ) :
    (∫ x : AddCircle T, ‖fejerGeometric P x‖ ^ 2 ∂haarAddCircle) = (P + 1 : ℝ) := by
  have hcard : (Finset.Icc (0 : ℤ) P).card = P + 1 := by simp [Int.card_Icc]
  have hc := (orthonormal_fourier (hT := hT)).inner_sum
    (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) (Finset.Icc (0 : ℤ) P)
  simp only [one_smul, map_one, one_mul, Finset.sum_const, hcard, nsmul_eq_mul, mul_one] at hc
  have hi : inner ℂ (ContinuousMap.toLp 2 haarAddCircle ℂ (fejerGeometric (T := T) P))
      (ContinuousMap.toLp 2 haarAddCircle ℂ (fejerGeometric (T := T) P)) = ((P + 1 : ℕ) : ℂ) := by
    simpa only [fejerGeometric, map_sum, fourierLp] using hc
  rw [ContinuousMap.inner_toLp] at hi
  simp_rw [Complex.mul_conj'] at hi
  simp only [← Complex.ofReal_pow] at hi
  rw [integral_complex_ofReal] at hi
  exact_mod_cast hi

theorem fejerKernel_integral (P : ℕ) :
    (∫ x : AddCircle T, fejerKernel P x ∂haarAddCircle) = 1 := by
  unfold fejerKernel
  rw [integral_div, fejerGeometric_integral_norm_sq]
  exact div_self (by positivity : (P + 1 : ℝ) ≠ 0)

end Yau.Blueprint.V04Proof
