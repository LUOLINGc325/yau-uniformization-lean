import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic

/-! A genuine smooth saturation preserves every jet on the unit interval.
The elementary Mathlib proof is reconstructed from canonical Ae0dbe
L23LocalDistanceSupportSaturation, SHA be4fe037d6923af55108f3dada6bcc4db9d67e0922595cafd1bcbf1de5fdef70.
Only the displayed Mathlib imports are used. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.C01Aux

theorem exists_smooth_unit_saturation {δ : ℝ} (hδ : 0 < δ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      Set.MapsTo χ Set.univ (Set.Ioo (-δ) (1+δ)) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, χ =ᶠ[𝓝 u] id := by
  let β : ContDiffBump (1/2 : ℝ) :=
    ⟨1/2+δ/2,1/2+δ,by linarith,by linarith⟩
  let χ : ℝ → ℝ := fun u => β u*u+(1-β u)*(1/2)
  have hχ : ContDiff ℝ ∞ χ :=
    (β.contDiff.mul contDiff_id).add ((contDiff_const.sub β.contDiff).mul contDiff_const)
  refine ⟨χ,hχ,?_,?_⟩
  · intro u _
    by_cases hb : β u = 0
    · simp only [χ,hb,zero_mul,sub_zero,one_mul,Set.mem_Ioo]
      constructor <;> linarith
    · have huBall : u ∈ Metric.ball (1/2 : ℝ) β.rOut := by
        rw [← β.support_eq]
        exact hb
      rw [Real.ball_eq_Ioo] at huBall
      change (1/2)-(1/2+δ) < u ∧ u < (1/2)+(1/2+δ) at huBall
      have hbpos : 0 < β u := lt_of_le_of_ne β.nonneg (by intro h; exact hb h.symm)
      have hlo := mul_pos hbpos (show 0 < u+δ by linarith [huBall.1])
      have hhi := mul_pos hbpos (show 0 < 1+δ-u by linarith [huBall.2])
      have hbrem : 0 ≤ 1-β u := sub_nonneg.mpr (β.le_one (x := u))
      have hnlo := mul_nonneg hbrem (show 0 ≤ (1/2 : ℝ)+δ by linarith)
      have hnhi := mul_nonneg hbrem (show 0 ≤ (1/2 : ℝ)+δ by linarith)
      dsimp only [χ]
      constructor <;> nlinarith
  · intro u hu
    have hd : |u-(1/2 : ℝ)| ≤ 1/2 := abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hball : u ∈ Metric.ball (1/2 : ℝ) β.rIn := by
      rw [Metric.mem_ball,Real.dist_eq]
      exact hd.trans_lt (by dsimp [β]; linarith)
    filter_upwards [β.eventuallyEq_one_of_mem_ball hball] with v hv
    have hv' : β v = 1 := by simpa only [Pi.one_apply] using hv
    simp only [χ,hv',one_mul,sub_self,zero_mul,add_zero,id_eq]

end Yau.NodeProofs.C01Aux
