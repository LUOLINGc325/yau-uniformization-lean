import Yau.LeafProofs.L05DiniKernelBudget

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

theorem diniModulusTail_data {phi : ℝ → ℝ} {eta B G : ℝ}
    (he : 0 < eta) (_he1 : eta < 1) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hm : Measurable phi) (hmono : MonotoneOn phi (Set.Ioc (0:ℝ) 1))
    (hp : powerBound eta B phi) :
    Measurable (diniModulusTail G phi) ∧ diniModulusTail G phi 0=0 ∧
      Monotone (diniModulusTail G phi) ∧
      (∀ s : ℝ, 0 < s → 0 ≤ diniModulusTail G phi s ∧ diniModulusTail G phi s ≤ (B+2*G)*s^eta) := by
  have hp1 := hp 1 ⟨by norm_num,le_rfl⟩
  have hpos (s : ℝ) (hs : 0 < s) :
      0 ≤ diniModulusTail G phi s ∧ diniModulusTail G phi s ≤ (B+2*G)*s^eta := by
    rw [diniModulusTail,if_neg hs.not_ge]
    by_cases hs1 : s ≤ 1
    · rw [if_pos hs1]
      have hh := hp s ⟨hs,hs1⟩
      refine ⟨hh.1,?_⟩
      nlinarith only [hh.2,mul_nonneg hG (Real.rpow_nonneg hs.le eta)]
    · rw [if_neg hs1]
      have hpow : 1 ≤ s^eta := Real.one_le_rpow (le_of_not_ge hs1) he.le
      have hscale := mul_le_mul_of_nonneg_left hpow (show 0 ≤ B+2*G by positivity)
      have hb1 : phi 1 ≤ B := by simpa only [Real.one_rpow,mul_one] using hp1.2
      exact ⟨by linarith only [hp1.1,hG],by nlinarith only [hscale,hb1]⟩
  refine ⟨?_,by simp [diniModulusTail],?_,hpos⟩
  · have hinner : Measurable (fun s : ℝ => if s ≤ 1 then phi s else phi 1+2*G) :=
      hm.piecewise measurableSet_Iic measurable_const
    exact measurable_const.piecewise measurableSet_Iic hinner
  · intro x y hxy
    by_cases hy : y ≤ 0
    · simp only [diniModulusTail,if_pos hy,if_pos (hxy.trans hy),le_refl]
    have hy0 : 0 < y := lt_of_not_ge hy
    by_cases hx : x ≤ 0
    · rw [diniModulusTail,if_pos hx]
      exact (hpos y hy0).1
    have hx0 : 0 < x := lt_of_not_ge hx
    simp only [diniModulusTail,if_neg hx,if_neg hy]
    by_cases hy1 : y ≤ 1
    · rw [if_pos hy1,if_pos (hxy.trans hy1)]
      exact hmono ⟨hx0,hxy.trans hy1⟩ ⟨hy0,hy1⟩ hxy
    rw [if_neg hy1]
    by_cases hx1 : x ≤ 1
    · rw [if_pos hx1]
      have hh := hmono ⟨hx0,hx1⟩ ⟨by norm_num,le_rfl⟩ hx1
      linarith only [hh,hG]
    · rw [if_neg hx1]

end Yau.LeafProofs.L05Aux
