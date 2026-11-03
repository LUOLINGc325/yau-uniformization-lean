import Yau.Proofs.F05Reflection

/-! The reflected one-sided time derivative is the literal reflected time
jet, including the closed initial face. -/

open Set
noncomputable section
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_reflection_hasDerivWithinAt {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {T : ℝ} {v K : Point n → ℝ}
    (ht : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
      HasDerivWithinAt (fun t => v (p.1,t)) (K p) (Icc 0 T) p.2)
    {p : Point n} (hp : p.2 ∈ Icc 0 T) :
    HasDerivWithinAt (fun t => halfSpaceSecondOrderExtension e v (p.1,t))
      (halfSpaceSecondOrderExtension e K p) (Icc 0 T) p.2 := by
  by_cases hn : 0 ≤ inner ℝ e p.1
  · simpa only [halfSpaceSecondOrderExtension,ite_eq_left hn] using ht p ⟨hn,hp⟩
  · have hs (j : ℝ) (hj : 0 ≤ j) :
        HasDerivWithinAt (fun t => v (normalSample e j p.1,t))
          (K (normalSample e j p.1,p.2)) (Icc 0 T) p.2 := by
      apply ht (normalSample e j p.1,p.2)
      refine ⟨?_,hp⟩
      change 0 ≤ inner ℝ e (normalSample e j p.1)
      rw [normalSample_normal he]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hj) (lt_of_not_ge hn).le
    have hneg := (((hs 1 (by norm_num)).const_smul (6 : ℝ)).sub
      ((hs 2 (by norm_num)).const_smul (8 : ℝ))).add ((hs 3 (by norm_num)).const_smul (3 : ℝ))
    simp only [halfSpaceSecondOrderExtension,ite_eq_right hn]
    apply hneg.congr <;> intros <;>
      simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]

theorem F05_reflection_timeD {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {T : ℝ} (hT : 0 < T) {v K : Point n → ℝ}
    (ht : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
      HasDerivWithinAt (fun t => v (p.1,t)) (K p) (Icc 0 T) p.2)
    {p : Point n} (hp : p.2 ∈ Icc 0 T) :
    timeD (cylinder univ 0 T) (halfSpaceSecondOrderExtension e v) p =
      halfSpaceSecondOrderExtension e K p := by
  have hFiber : {t | (p.1,t) ∈ cylinder (univ : Set (Space n)) 0 T} = Icc 0 T := by
    ext t
    simp only [cylinder,mem_prod,mem_univ,true_and,mem_setOf_eq]
  unfold timeD
  rw [hFiber]
  exact (F05_reflection_hasDerivWithinAt he ht hp).derivWithin (uniqueDiffOn_Icc hT p.2 hp)

theorem F05_reflection_zero_slice {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {v : Point n → ℝ} {t : ℝ}
    (hv : ∀ x, 0 ≤ inner ℝ e x → v (x,t) = 0) (x : Space n) :
    halfSpaceSecondOrderExtension e v (x,t) = 0 := by
  by_cases hn : 0 ≤ inner ℝ e x
  · simpa only [halfSpaceSecondOrderExtension,ite_eq_left hn] using hv x hn
  · have hs (j : ℝ) (hj : 0 ≤ j) : v (normalSample e j x,t) = 0 := by
      apply hv
      rw [normalSample_normal he]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hj) (lt_of_not_ge hn).le
    simp only [halfSpaceSecondOrderExtension,ite_eq_right hn,hs 1 (by norm_num),
      hs 2 (by norm_num),hs 3 (by norm_num),mul_zero,sub_zero,add_zero]

end Yau.Proofs.F05Aux
