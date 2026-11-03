import Yau.Proofs.F03ChartGradientComparison
import Yau.Proofs.F03KernelSpatialDifferential
import Yau.Proofs.F03KernelLeftProfileDomination

/-! Compact chart geometry and the actual kernel Gaussian produce one genuine differential envelope. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_compact_chart_profile_envelope
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b)
    (a : Pt X) (K : Set (ComplexVector n)) (hK : IsCompact K) (hKt : K ⊆ chartTarget a) :
    ∃ E : Pt X → ℝ,Integrable E μ ∧ (∀ y,0 ≤ E y) ∧
      ∀ z ∈ K,∀ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b (chartInv a z) y ≤ E y ∧
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b (chartInv a z) y*ρ y T ≤ E y ∧
      ‖kernelLeftChartDifferential
        (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO) a b z y‖*ρ y T ≤ E y := by
  let H := dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO
  let L := max 1 (Real.sqrt b)
  have hL : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hbL : b ≤ L^2 := (Real.sqrt_le_iff.mp (show Real.sqrt b ≤ L from le_max_right _ _)).2
  have hDistance : ContinuousOn (fun z => inducedDistance X.metric.form o (chartInv a z)) K :=
    (LeafProofs.L12Aux.continuous_distFrom X.metric o).comp_continuousOn
      ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono hKt)
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hDistance
  let C₀ := max M 0/L
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀];positivity
  have hNear (z : ComplexVector n) (hz : z ∈ K) :
      inducedDistance X.metric.form o (chartInv a z) ≤ C₀*L := by
    have hBound := hM z hz
    rw [Real.norm_eq_abs] at hBound
    dsimp [C₀]
    rw [div_mul_cancel₀ _ hL0.ne']
    exact ((le_abs_self _).trans hBound).trans (le_max_left _ _)
  obtain ⟨D,hD,hD0,hDom⟩ := dirichletMinimalKernel_left_profile_domination X o h U P ρ hf hT
    μ hμ O hO hb C₀ hC₀ hL hbL
  obtain ⟨C,hC,hChart⟩ := compact_chart_fderiv_le_physical_gradient X.metric a K hK hKt
  refine ⟨fun y => (C+1)*D y,hD.const_mul (C+1),fun y => mul_nonneg (by positivity) (hD0 y),?_⟩
  intro z hz y
  have hρ0 := (hf.2.2.2.2.2.2.2.2.2.1 y T hT).2
  have hE := hDom (chartInv a z) (hNear z hz) y
  have hEnlarge : D y ≤ (C+1)*D y := by nlinarith [mul_nonneg hC.le (hD0 y)]
  refine ⟨hE.1.trans hEnlarge,hE.2.2.1.trans hEnlarge,?_⟩
  have hDiff := hChart z hz (fun x => H b x y)
    (kernelSmooth_univ_smoothFn_left H
      (dirichletMinimalKernelCandidate_joint_smooth X.metric X.kahler_metric μ hμ O hO) hb y)
  change ‖kernelLeftChartDifferential H a b z y‖ ≤
    C*Real.sqrt (gradNormSq X.metric.form (fun x => H b x y) (chartInv a z)) at hDiff
  calc
    _ ≤ (C*Real.sqrt (gradNormSq X.metric.form (fun x => H b x y) (chartInv a z)))*ρ y T :=
      mul_le_mul_of_nonneg_right hDiff hρ0
    _ ≤ C*D y := by
      convert mul_le_mul_of_nonneg_left hE.2.2.2 hC.le using 1 <;> ring
    _ ≤ (C+1)*D y := by nlinarith [hD0 y]

end Yau.Proofs.F03Aux
