import Yau.Proofs.V03HolomorphicC1
import Yau.Proofs.V03ParameterDerivative

/-! Differentiating the actual directional Cauchy integrals proves that the
Fréchet derivative columns remain holomorphic. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem differentiableAt_fderiv_apply_of_line_neighborhood
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U)
    {K : Set E} (hK : IsCompact K) {x : E} (hx : K ∈ 𝓝 x) (v : E)
    {R : ℝ} (hR : 0 < R)
    (hline : ∀ y ∈ K, ∀ t ∈ Metric.closedBall (0 : ℂ) R, y + t • v ∈ U) :
    DifferentiableAt ℂ (fun y => fderiv ℂ f y v) x := by
  let c : ℝ → ℂ := fun θ =>
    (circleMap 0 R θ * Complex.I) * (1 / circleMap 0 R θ ^ 2)
  let A : E → ℝ → F := fun y θ => c θ • f (y + circleMap 0 R θ • v)
  let A' : E → ℝ → E →L[ℂ] F := fun y θ =>
    c θ • fderiv ℂ f (y + circleMap 0 R θ • v)
  let I : E → F := fun y => ∫ θ in (0 : ℝ)..(2 * Real.pi), A y θ
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
  have hmap : Set.MapsTo (fun p : E × ℝ => p.1 + circleMap 0 R p.2 • v)
      (K ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) U := fun p hp =>
    hline p.1 hp.1 (circleMap 0 R p.2) (circleMap_mem_closedBall 0 hR.le p.2)
  have hA : ContinuousOn (fun p : E × ℝ => A p.1 p.2)
      (K ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    (hc.comp continuous_snd).continuousOn.smul
      (hf.continuousOn.comp hs.continuousOn hmap)
  have hA' : ContinuousOn (fun p : E × ℝ => A' p.1 p.2)
      (K ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    (hc.comp continuous_snd).continuousOn.smul
      ((complex_holomorphic_continuousOn_fderiv hU hf).comp hs.continuousOn hmap)
  have hderiv : ∀ y ∈ K, ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      HasFDerivAt (fun z => A z θ) (A' y θ) y := by
    intro y hy θ hθ
    have hyU := hline y hy (circleMap 0 R θ) (circleMap_mem_closedBall 0 hR.le θ)
    have hdf := ((hf _ hyU).differentiableAt (hU.mem_nhds hyU)).hasFDerivAt
    have ht : HasFDerivAt (fun z : E => z + circleMap 0 R θ • v)
        (ContinuousLinearMap.id ℂ E) y := (hasFDerivAt_id y).add_const _
    have htotal := (hdf.comp y ht).const_smul (c θ)
    convert htotal using 1 <;> ext z <;> rfl
  have hI : DifferentiableAt ℂ I x :=
    differentiableAt_intervalIntegral_of_joint_compact hK hx
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hA hA' hderiv
  have hconst : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hid : ∀ y ∈ K, fderiv ℂ f y v = (2 * Real.pi * Complex.I : ℂ)⁻¹ • I y := by
    intro y hy
    have hC := holomorphic_directional_cauchy hU hf y v hR (hline y hy)
    have hC' : I y = (2 * Real.pi * Complex.I : ℂ) • fderiv ℂ f y v := by
      simpa only [I, A, c, circleIntegral, deriv_circleMap, smul_smul] using hC
    rw [hC', smul_smul, inv_mul_cancel₀ hconst, one_smul]
  apply (hI.const_smul (2 * Real.pi * Complex.I : ℂ)⁻¹).congr_of_eventuallyEq
  filter_upwards [hx] with y hy
  exact hid y hy

theorem complex_holomorphic_fderiv_apply_differentiableOn
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) (v : E) :
    DifferentiableOn ℂ (fun y => fderiv ℂ f y v) U := by
  intro x hx
  obtain ⟨K, R, hK, hxK, hR, hline⟩ := exists_compact_line_neighborhood hU hx v
  exact (differentiableAt_fderiv_apply_of_line_neighborhood hU hf hK hxK v hR hline).differentiableWithinAt

end Yau.Blueprint.V03Proof
