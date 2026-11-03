import Yau.Proofs.F03TerminalDensityGaussian
import Yau.Proofs.F03CoarseKernelBound

/-! A genuine integrable same-kernel terminal density dominates all physical-time potential data. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_terminal_density_integrable
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b) (x : Pt X) :
    Integrable (fun y => dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*ρ y T) μ := by
  let L := max 1 (Real.sqrt b)
  have hL : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hbL : b ≤ L^2 := by
    have hh : Real.sqrt b ≤ L := le_max_right _ _
    nlinarith [Real.sq_sqrt hb.le,Real.sqrt_nonneg b]
  let C₀ := inducedDistance X.metric.form o x/L
  have hC₀ : 0 ≤ C₀ := div_nonneg (X.metric.induced_distance_nonneg o x) hL0.le
  have hx : inducedDistance X.metric.form o x ≤ C₀*L := by
    dsimp [C₀]
    rw [div_mul_cancel₀ _ hL0.ne']
  obtain ⟨K,c,hK,hc,hKernel⟩ := dirichletMinimalKernelCandidate_coarse_gaussian X o h U P ρ hf C₀ hC₀
  let R := (C₀+1)*L
  have hR : 1 ≤ R := by dsimp [R];nlinarith
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hV : 0 < (μ (distBall X.metric.form o R)).toReal := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos X.metric μ hμ o hR0).ne'
    (riemannianVolume_distBall_lt_top X.metric μ hμ o hR0).ne
  have hInt := localizedFlow_terminal_density_gaussian_integrable X o h U P ρ hf hT μ hμ hc hR
  have hHCont := kernelSmooth_univ_continuous_right _
    (dirichletMinimalKernelCandidate_joint_smooth X.metric X.kahler_metric μ hμ O hO) hb x
  have hρCont := continuous_of_smoothFn (LeafProofs.L19Aux.smoothSpaceTime_slice hf.2.2.2.1 hT)
  apply (hInt.const_mul (K*(L/Real.sqrt b)^(2*n)/(μ (distBall X.metric.form o R)).toReal)).mono'
    (hHCont.aestronglyMeasurable.mul hρCont.aestronglyMeasurable)
  apply ae_of_all μ
  intro y
  have hρ0 := (hf.2.2.2.2.2.2.2.2.2.1 y T hT).2
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
    (dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb x y) hρ0)]
  convert mul_le_mul_of_nonneg_right (hKernel μ hμ O hO L hL b hb hbL x hx y) hρ0 using 1 <;> dsimp [R] <;> ring

theorem dirichletMinimalKernel_potential_slab_integrable
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b) (x : Pt X)
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    Integrable (fun y => dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*P y s) μ ∧
      Integrable (fun y => dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*U y s) μ := by
  have hDom := dirichletMinimalKernel_terminal_density_integrable X o h U P ρ hf hT μ hμ O hO hb x
  have hHCont := kernelSmooth_univ_continuous_right _
    (dirichletMinimalKernelCandidate_joint_smooth X.metric X.kahler_metric μ hμ O hO) hb x
  have hPCont := continuous_of_smoothFn (LeafProofs.L19Aux.smoothSpaceTime_slice hf.2.2.1 hs.1)
  have hUCont := continuous_of_smoothFn (LeafProofs.L19Aux.smoothSpaceTime_slice hf.2.1 hs.1)
  constructor
  · apply hDom.mono' (hHCont.aestronglyMeasurable.mul hPCont.aestronglyMeasurable)
    apply ae_of_all μ
    intro y
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg
      (dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb x y)]
    exact mul_le_mul_of_nonneg_left (localizedFlow_potential_time_envelope X o h U P ρ hf hs y).1
      (dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb x y)
  · apply (hDom.const_mul T).mono' (hHCont.aestronglyMeasurable.mul hUCont.aestronglyMeasurable)
    apply ae_of_all μ
    intro y
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg
      (dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb x y)]
    convert mul_le_mul_of_nonneg_left (localizedFlow_potential_time_envelope X o h U P ρ hf hs y).2
      (dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb x y) using 1 <;> ring

end Yau.Proofs.F03Aux
