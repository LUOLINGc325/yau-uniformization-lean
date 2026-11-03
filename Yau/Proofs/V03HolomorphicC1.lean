import Yau.Proofs.V03HolomorphicLine
import Yau.Proofs.V03ParameterIntegral
import Yau.Proofs.V03ComplexNeighborhood

/-! Cauchy's formula proves continuity of the actual derivative columns
before differentiating those columns. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem continuousAt_fderiv_apply_of_line_neighborhood
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U)
    {K : Set E} (hK : IsCompact K) {x : E} (hx : K ∈ 𝓝 x) (v : E)
    {R : ℝ} (hR : 0 < R)
    (hline : ∀ y ∈ K, ∀ t ∈ Metric.closedBall (0 : ℂ) R, y + t • v ∈ U) :
    ContinuousAt (fun y => fderiv ℂ f y v) x := by
  let c : ℝ → ℂ := fun θ =>
    (circleMap 0 R θ * Complex.I) * (1 / circleMap 0 R θ ^ 2)
  let I : E → F := fun y =>
    ∫ θ in (0 : ℝ)..(2 * Real.pi), c θ • f (y + circleMap 0 R θ • v)
  have hcn : ∀ θ, circleMap 0 R θ ≠ 0 := by
    intro θ hz
    have hn := norm_circleMap_zero R θ
    rw [hz, norm_zero, abs_of_pos hR] at hn
    linarith
  have hc : Continuous c :=
    ((continuous_circleMap 0 R).mul continuous_const).mul
      (continuous_const.div ((continuous_circleMap 0 R).pow 2)
        (fun θ => pow_ne_zero 2 (hcn θ)))
  have hs : Continuous (fun p : E × ℝ => p.1 + circleMap 0 R p.2 • v) := by
    fun_prop
  have hF : ContinuousOn (fun p : E × ℝ => f (p.1 + circleMap 0 R p.2 • v))
      (K ×ˢ Set.uIcc (0 : ℝ) (2 * Real.pi)) :=
    hf.continuousOn.comp hs.continuousOn (fun p hp =>
      hline p.1 hp.1 (circleMap 0 R p.2) (circleMap_mem_closedBall 0 hR.le p.2))
  have hI : ContinuousAt I x :=
    continuousAt_intervalIntegral_of_joint_compact hK hx
      ((hc.comp continuous_snd).continuousOn.smul hF)
  have hconst : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hid : ∀ y ∈ K, fderiv ℂ f y v = (2 * Real.pi * Complex.I : ℂ)⁻¹ • I y := by
    intro y hy
    have hC := holomorphic_directional_cauchy hU hf y v hR (hline y hy)
    have hC' : I y = (2 * Real.pi * Complex.I : ℂ) • fderiv ℂ f y v := by
      simpa only [I, c, circleIntegral, deriv_circleMap, smul_smul] using hC
    rw [hC', smul_smul, inv_mul_cancel₀ hconst, one_smul]
  apply (hI.const_smul (2 * Real.pi * Complex.I : ℂ)⁻¹).congr_of_eventuallyEq
  filter_upwards [hx] with y hy
  exact hid y hy

theorem complex_holomorphic_fderiv_apply_continuousAt [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U)
    {x : E} (hx : x ∈ U) (v : E) :
    ContinuousAt (fun y => fderiv ℂ f y v) x := by
  obtain ⟨K, R, hK, hxK, hR, hline⟩ := exists_compact_line_neighborhood hU hx v
  exact continuousAt_fderiv_apply_of_line_neighborhood hU hf hK hxK v hR hline

theorem complex_holomorphic_continuousOn_fderiv [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fderiv ℂ f) U := by
  intro x hx
  exact (continuousAt_clm_apply.mpr fun v =>
    complex_holomorphic_fderiv_apply_continuousAt hU hf hx v).continuousWithinAt

theorem complex_holomorphic_contDiffOn_one [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ 1 f U := by
  exact (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hU).mpr
    ⟨hf, by simp, contDiffOn_zero.mpr (complex_holomorphic_continuousOn_fderiv hU hf)⟩

end Yau.Blueprint.V03Proof
