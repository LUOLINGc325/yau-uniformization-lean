import Yau.LeafProofs.L05DiniKernelTailBudget

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem diniModulusTail_spatial_modulus {n : ℕ} {T G : ℝ} {g : Point n → ℝ} {phi : ℝ → ℝ}
    (hphi1 : 0 ≤ phi 1) (hG : ∀ p ∈ cylinder Set.univ 0 T, |g p| ≤ G)
    (hmod : ∀ r ∈ Set.Ioc (0:ℝ) 1, ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T,
      parabolicDistance p q ≤ r → |g p-g q| ≤ phi r)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) (x y : Space n) :
    |g (x,t)-g (y,t)| ≤ diniModulusTail G phi ‖x-y‖ := by
  by_cases hxy : x=y
  · subst y
    simp [diniModulusTail]
  have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [diniModulusTail,if_neg hd.not_ge]
  by_cases hd1 : ‖x-y‖ ≤ 1
  · rw [if_pos hd1]
    apply hmod _ ⟨hd,hd1⟩ (x,t) ⟨Set.mem_univ _,ht⟩ (y,t) ⟨Set.mem_univ _,ht⟩
    simp [parabolicDistance]
  · rw [if_neg hd1]
    have hh : |g (x,t)-g (y,t)| ≤ |g (x,t)|+|g (y,t)| := abs_sub _ _
    have hx := hG (x,t) ⟨Set.mem_univ _,ht⟩
    have hy := hG (y,t) ⟨Set.mem_univ _,ht⟩
    linarith only [hh,hx,hy,hphi1]

theorem diniTransform_nonneg_of_powerBound {phi : ℝ → ℝ} {eta B r : ℝ}
    (he : 0 < eta) (he1 : eta < 1) (hB : 0 ≤ B) (hm : Measurable phi)
    (hmono : MonotoneOn phi (Set.Ioc (0:ℝ) 1)) (hp : powerBound eta B phi)
    (hr : r ∈ Set.Ioc (0:ℝ) 1) : 0 ≤ diniTransform phi r := by
  have hd := diniModulusTail_data he he1 hB (le_refl (0:ℝ)) hm hmono hp
  have hz := diniBudget_nonneg hr.1 (fun a ha => (hd.2.2.2 a ha).1)
  have hb := diniModulusTail_budget_le he he1 hB (le_refl (0:ℝ)) hm hmono hp hr
  simpa only [mul_zero,add_zero] using hz.trans hb

end Yau.LeafProofs.L05Aux
