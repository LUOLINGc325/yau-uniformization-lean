import Mathlib.Analysis.Calculus.Taylor

/-! Tests at a nonnegative point from actual second and third derivatives. -/
noncomputable section
open Set
namespace Yau.Proofs.C05TaylorSequenceAux

theorem first_remainder (f : ℝ → ℝ) {δ M x : ℝ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ 2 f (Ioo (-δ) δ))
    (hbound : ∀ t ∈ Ioo (-δ) δ, |iteratedDeriv 2 f t| ≤ M)
    (hx : |x| < δ) (hx0 : x ≠ 0) :
    |f x - f 0 - deriv f 0 * x| ≤ M * |x| ^ 2 / 2 := by
  have h0 : (0:ℝ) ∈ Ioo (-δ) δ := by constructor <;> linarith
  have hsub : uIcc 0 x ⊆ Ioo (-δ) δ := by
    intro t ht
    rcases mem_uIcc.mp ht with ht | ht <;>
      constructor <;> have hxa := abs_lt.mp hx <;> linarith [ht.1,ht.2]
  obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx0.symm (hf.mono hsub)
  have hu := uniqueDiffOn_uIcc hx0.symm
  have hfc : ContDiffAt ℝ 1 f 0 := (hf.contDiffAt (isOpen_Ioo.mem_nhds h0)).of_le (by norm_num)
  have ht : taylorWithinEval f 1 (uIcc 0 x) 0 x = f 0 + deriv f 0*x := by
    rw [show 1=0+1 from rfl,taylorWithinEval_succ]
    simp only [Nat.zero_add]
    rw [iteratedDerivWithin_eq_iteratedDeriv hu hfc left_mem_uIcc]
    simp [iteratedDeriv_one,mul_comm]
  rw [ht] at he
  have hb := hbound y (hsub (uIoo_subset_uIcc_self hy))
  have he' : f x-f 0-deriv f 0*x = iteratedDeriv 2 f y*x^2/2 := by
    norm_num at he
    linarith
  rw [he',abs_div,abs_mul,abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb (sq_nonneg _)) (by norm_num)

theorem second_remainder (f : ℝ → ℝ) {δ M x : ℝ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ 3 f (Ioo (-δ) δ))
    (hbound : ∀ t ∈ Ioo (-δ) δ, |iteratedDeriv 3 f t| ≤ M)
    (hx : |x| < δ) (hx0 : x ≠ 0) :
    |f x - f 0 - deriv f 0*x - (iteratedDeriv 2 f 0/2)*x^2| ≤ M*|x|^3/6 := by
  have h0 : (0:ℝ) ∈ Ioo (-δ) δ := by constructor <;> linarith
  have hsub : uIcc 0 x ⊆ Ioo (-δ) δ := by
    intro t ht
    rcases mem_uIcc.mp ht with ht | ht <;>
      constructor <;> have hxa := abs_lt.mp hx <;> linarith [ht.1,ht.2]
  obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx0.symm (hf.mono hsub)
  have hu := uniqueDiffOn_uIcc hx0.symm
  have hfc : ContDiffAt ℝ 2 f 0 := (hf.contDiffAt (isOpen_Ioo.mem_nhds h0)).of_le (by norm_num)
  have ht1 : taylorWithinEval f 1 (uIcc 0 x) 0 x = f 0+deriv f 0*x := by
    rw [show 1=0+1 from rfl,taylorWithinEval_succ]
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hfc.of_le (by norm_num)) left_mem_uIcc]
    simp [iteratedDeriv_one,mul_comm]
  have ht : taylorWithinEval f 2 (uIcc 0 x) 0 x =
      f 0+deriv f 0*x+(iteratedDeriv 2 f 0/2)*x^2 := by
    rw [show 2=1+1 from rfl,taylorWithinEval_succ,ht1]
    rw [iteratedDerivWithin_eq_iteratedDeriv hu hfc left_mem_uIcc]
    norm_num
    ring
  rw [ht] at he
  have hb := hbound y (hsub (uIoo_subset_uIcc_self hy))
  have he' : f x-f 0-deriv f 0*x-(iteratedDeriv 2 f 0/2)*x^2 =
      iteratedDeriv 3 f y*x^3/6 := by
    norm_num at he
    linarith
  rw [he',abs_div,abs_mul,abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb (pow_nonneg (abs_nonneg _) _))
    (by norm_num)

theorem abs_deriv_zero_le (f : ℝ → ℝ) {δ M r : ℝ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ 2 f (Ioo (-δ) δ))
    (hnonneg : ∀ t ∈ Ioo (-δ) δ, 0 ≤ f t)
    (hbound : ∀ t ∈ Ioo (-δ) δ, |iteratedDeriv 2 f t| ≤ M)
    (hr : 0 < r) (hrδ : r < δ) :
    |deriv f 0| ≤ f 0/r + M*r/2 := by
  have hp := (abs_le.mp (first_remainder f hδ hf hbound
    (by simpa [abs_of_pos hr] using hrδ) hr.ne')).2
  have hm := (abs_le.mp (first_remainder f hδ hf hbound
    (by simpa [abs_of_pos hr] using hrδ : |(-r)|<δ) (neg_ne_zero.mpr hr.ne'))).2
  have hnp := hnonneg r (by constructor <;> linarith)
  have hnm := hnonneg (-r) (by constructor <;> linarith)
  rw [abs_of_pos hr] at hp
  rw [abs_neg,abs_of_pos hr] at hm
  have hup : deriv f 0 ≤ (f 0+M*r^2/2)/r := (le_div_iff₀ hr).mpr (by nlinarith)
  have hlo : -(f 0+M*r^2/2)/r ≤ deriv f 0 := (div_le_iff₀ hr).mpr (by nlinarith)
  have he : (f 0+M*r^2/2)/r = f 0/r+M*r/2 := by field_simp [hr.ne']
  rw [he] at hup
  rw [neg_div,he] at hlo
  exact abs_le.mpr ⟨hlo,hup⟩

theorem second_deriv_zero_lower (f : ℝ → ℝ) {δ M r : ℝ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ 3 f (Ioo (-δ) δ))
    (hnonneg : ∀ t ∈ Ioo (-δ) δ, 0 ≤ f t)
    (hbound : ∀ t ∈ Ioo (-δ) δ, |iteratedDeriv 3 f t| ≤ M)
    (hr : 0 < r) (hrδ : r < δ) :
    -2*f 0/r^2-M*r/3 ≤ iteratedDeriv 2 f 0 := by
  have hp := (abs_le.mp (second_remainder f hδ hf hbound
    (by simpa [abs_of_pos hr] using hrδ) hr.ne')).2
  have hm := (abs_le.mp (second_remainder f hδ hf hbound
    (by simpa [abs_of_pos hr] using hrδ : |(-r)|<δ) (neg_ne_zero.mpr hr.ne'))).2
  have hnp := hnonneg r (by constructor <;> linarith)
  have hnm := hnonneg (-r) (by constructor <;> linarith)
  rw [abs_of_pos hr] at hp
  rw [abs_neg,abs_of_pos hr] at hm
  have hb : (-2*f 0-M*r^3/3)/r^2 ≤ iteratedDeriv 2 f 0 :=
    (div_le_iff₀ (sq_pos_of_pos hr)).mpr (by nlinarith)
  have he : (-2*f 0-M*r^3/3)/r^2 = -2*f 0/r^2-M*r/3 := by
    field_simp [hr.ne']
  rwa [he] at hb

end Yau.Proofs.C05TaylorSequenceAux
