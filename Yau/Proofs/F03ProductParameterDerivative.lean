import Yau.Proofs.F03ClosedParameterIntegral
import Mathlib.Analysis.Normed.Operator.Prod

/-! The exact product derivative and its norm bound for a spatial kernel times a closed-slab time profile. -/
noncomputable section
open Set
namespace Yau.Proofs.F03Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def spatialTimeProductDerivative (D : E →L[ℝ] ℝ) (q f q' : ℝ) : E × ℝ →L[ℝ] ℝ :=
  q • D.comp (ContinuousLinearMap.fst ℝ E ℝ)+(f*q') • ContinuousLinearMap.snd ℝ E ℝ

theorem spatialTimeProduct_hasFDerivWithinAt
    (f : E → ℝ) (q : ℝ → ℝ) {z : E} {s q' : ℝ} {D : E →L[ℝ] ℝ}
    {O : Set E} {I : Set ℝ} (hf : HasFDerivAt f D z) (hq : HasDerivWithinAt q q' I s) :
    HasFDerivWithinAt (fun p : E × ℝ => f p.1*q p.2)
      (spatialTimeProductDerivative D (q s) (f z) q') (O ×ˢ I) (z,s) := by
  have hFst : HasFDerivAt (Prod.fst : E × ℝ → E)
      (ContinuousLinearMap.fst ℝ E ℝ) (z,s) := hasFDerivAt_fst
  have hSnd : HasFDerivWithinAt (Prod.snd : E × ℝ → ℝ)
      (ContinuousLinearMap.snd ℝ E ℝ) (O ×ˢ I) (z,s) := hasFDerivWithinAt_snd
  have hSpatial := (hf.comp (z,s) hFst).hasFDerivWithinAt (s := O ×ˢ I)
  have hTime := hq.hasFDerivWithinAt.comp (z,s) hSnd
    (show MapsTo (fun p : E × ℝ => p.2) (O ×ˢ I) I from fun _ hp => hp.2)
  convert hSpatial.mul hTime using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro v
    change q s*D v.1+(f z*q')*v.2=f z*(v.2*q')+q s*D v.1
    ring

theorem spatialTimeProductDerivative_norm_le (D : E →L[ℝ] ℝ) (q f q' : ℝ) :
    ‖spatialTimeProductDerivative D q f q'‖ ≤ |q| * ‖D‖+|f| * |q'| := by
  have hComp : ‖D.comp (ContinuousLinearMap.fst ℝ E ℝ)‖ ≤ ‖D‖ :=
    (D.opNorm_comp_le (ContinuousLinearMap.fst ℝ E ℝ)).trans
      (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_fst_le ℝ E ℝ) (norm_nonneg D)))
  change ‖q • D.comp (ContinuousLinearMap.fst ℝ E ℝ)+(f*q') • ContinuousLinearMap.snd ℝ E ℝ‖ ≤ _
  calc
    _ ≤ ‖q • D.comp (ContinuousLinearMap.fst ℝ E ℝ)‖+
        ‖(f*q') • ContinuousLinearMap.snd ℝ E ℝ‖ := norm_add_le _ _
    _ = |q| * ‖D.comp (ContinuousLinearMap.fst ℝ E ℝ)‖+
        |f*q'| * ‖ContinuousLinearMap.snd ℝ E ℝ‖ := by rw [norm_smul,norm_smul];rfl
    _ ≤ |q| * ‖D‖+|f*q'| * 1 := add_le_add
      (mul_le_mul_of_nonneg_left hComp (abs_nonneg q))
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ℝ E ℝ) (abs_nonneg _))
    _ = _ := by rw [abs_mul,mul_one]

end Yau.Proofs.F03Aux
