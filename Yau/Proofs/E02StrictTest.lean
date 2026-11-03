import Yau.Proofs.E02LocalPeano
import Yau.Proofs.E02NormQuadraticJet

open Set Filter Asymptotics
open scoped Topology ContDiff Asymptotics InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def strictifyTest (f : E → ℝ) (x y : E) : ℝ := f y-‖y-x‖^4

theorem realSecondJet_quartic (x : E) : RealSecondJet (fun y => ‖y-x‖^4) x 0 0 := by
  refine ⟨fun _ _ => rfl,?_⟩
  have hSq : (fun y : E => ‖y-x‖^2) =o[𝓝 x] (fun y => ‖y-x‖) := by
    simpa only [isLittleO_norm_right] using
      (isLittleO_pow_sub_sub x (by norm_num : 1 < (2:ℕ)))
  have hFourth := hSq.pow (by norm_num : 0 < (2:ℕ))
  simpa only [sub_self,norm_zero,zero_pow (by norm_num : 4 ≠ 0),
    _root_.zero_apply,mul_zero,sub_zero,←pow_mul] using hFourth

theorem realSecondJet_strictify {f : E → ℝ} {x : E} {p : E →L[ℝ] ℝ}
    {A : E →L[ℝ] E →L[ℝ] ℝ} (hf : RealSecondJet f x p A) :
    RealSecondJet (strictifyTest f x) x p A := by
  refine ⟨hf.1,?_⟩
  have hRem := hf.2.sub (realSecondJet_quartic x).2
  convert hRem using 1
  funext y
  simp only [strictifyTest,sub_self,norm_zero,zero_pow (by norm_num : 4 ≠ 0),
    _root_.zero_apply,mul_zero,sub_zero]
  ring

theorem strictifyTest_contDiffAt_two {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 2 (strictifyTest f x) x := by
  have hSq : ContDiff ℝ 2 (fun y : E => ‖y-x‖^2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hFourth : ContDiff ℝ 2 (fun y : E => ‖y-x‖^4) := by
    simpa only [←pow_mul] using hSq.pow 2
  exact hf.sub hFourth.contDiffAt

omit [InnerProductSpace ℝ E] in
theorem strictifyTest_at (f : E → ℝ) (x : E) : strictifyTest f x x = f x := by
  simp [strictifyTest]

omit [InnerProductSpace ℝ E] in
theorem strictifyTest_le (f : E → ℝ) (x y : E) : strictifyTest f x y ≤ f y :=
  sub_le_self _ (pow_nonneg (norm_nonneg _) _)

omit [InnerProductSpace ℝ E] in
theorem strictifyTest_eq_iff (f : E → ℝ) (x y : E) :
    strictifyTest f x y = f y ↔ y = x := by
  simp only [strictifyTest,sub_eq_self,pow_eq_zero_iff (by norm_num : 4 ≠ 0),
    norm_eq_zero,sub_eq_zero]

omit [InnerProductSpace ℝ E] in
theorem strictifyTest_strict_lower {f L : E → ℝ} {x y : E} (hLower : f y ≤ L y) (hNe : y ≠ x) :
    strictifyTest f x y < L y := by
  apply lt_of_lt_of_le _ hLower
  exact sub_lt_self _ (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hNe)) 4)

end Yau.NodeProofs.E02Aux
