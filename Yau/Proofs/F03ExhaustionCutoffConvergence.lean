import Yau.Proofs.F03ExhaustionCutoffGradient

/-! The constructed compact cutoff sequence converges genuinely to one under every integrable envelope. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau Blueprint F02Aux LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exhaustionCutoff_eventually_one (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {C A : ℝ} (hC : 0 < C)
    (hupper : ∀ x,u x ≤ C*(1+distFrom X.metric.form o x))
    (hCA : C ≤ A) (hA : 0 < A) (x : Pt X) :
    ∀ᶠ j : ℕ in atTop,exhaustionCutoff u A ((j:ℝ)+1) x=1 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (distFrom X.metric.form o x)
  apply eventually_atTop.mpr
  refine ⟨N,fun j hj => ?_⟩
  have hL : 1 ≤ (j:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  apply exhaustionCutoff_one_on_ball X o u hu C hC hupper hCA hA hL x
  apply (LeafProofs.L12Aux.mem_distBall_iff X.metric o x (by positivity)).mpr
  exact hN.trans_le (by exact_mod_cast (show N ≤ j+1 from hj.trans (Nat.le_succ j)))

theorem exhaustionCutoff_integral_tendsto (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {C A : ℝ} (hC : 0 < C)
    (hupper : ∀ x,u x ≤ C*(1+distFrom X.metric.form o x))
    (hCA : C ≤ A) (hA : 0 < A) (μ : Measure (Pt X))
    (f : Pt X → ℝ) (hf : Integrable f μ) :
    Tendsto (fun j : ℕ => ∫ y,exhaustionCutoff u A ((j:ℝ)+1) y*f y ∂μ) atTop
      (𝓝 (∫ y,f y ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun y => ‖f y‖)
  · intro j
    exact (continuous_of_smoothFn (exhaustionCutoff_smooth hu.1 A ((j:ℝ)+1))).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · exact hf.norm
  · intro j
    apply ae_of_all μ
    intro y
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (exhaustionCutoff_range u A ((j:ℝ)+1) y).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (exhaustionCutoff_range u A ((j:ℝ)+1) y).2
  · apply ae_of_all μ
    intro y
    apply tendsto_const_nhds.congr'
    filter_upwards [exhaustionCutoff_eventually_one X o u hu hC hupper hCA hA y] with j hj
    rw [hj,one_mul]

theorem exhaustionCutoff_integral_remainder_tendsto_zero (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {C A : ℝ} (hC : 0 < C)
    (hupper : ∀ x,u x ≤ C*(1+distFrom X.metric.form o x))
    (hCA : C ≤ A) (hA : 0 < A) (μ : Measure (Pt X))
    (f : Pt X → ℝ) (hf : Integrable f μ) :
    Tendsto (fun j : ℕ => ∫ y,(1-exhaustionCutoff u A ((j:ℝ)+1) y)*f y ∂μ) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := ∫ y,f y ∂μ) (f := atTop)).sub
    (exhaustionCutoff_integral_tendsto X o u hu hC hupper hCA hA μ f hf)
  simp only [sub_self] at h
  apply h.congr'
  apply Eventually.of_forall
  intro j
  have hInt : Integrable (fun y => exhaustionCutoff u A ((j:ℝ)+1) y*f y) μ := by
    apply hf.norm.mono'
      ((continuous_of_smoothFn (exhaustionCutoff_smooth hu.1 A ((j:ℝ)+1))).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    apply ae_of_all μ
    intro y
    change |exhaustionCutoff u A ((j:ℝ)+1) y*f y| ≤ ‖f y‖
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (exhaustionCutoff_range u A ((j:ℝ)+1) y).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (exhaustionCutoff_range u A ((j:ℝ)+1) y).2
  change (∫ y,f y ∂μ)-(∫ y,exhaustionCutoff u A ((j:ℝ)+1) y*f y ∂μ)=_
  rw [← integral_sub hf hInt]
  apply integral_congr_ae
  exact ae_of_all μ (fun y => by
    change f y-exhaustionCutoff u A ((j:ℝ)+1) y*f y=(1-exhaustionCutoff u A ((j:ℝ)+1) y)*f y
    ring)

end Yau.Proofs.F03Aux
