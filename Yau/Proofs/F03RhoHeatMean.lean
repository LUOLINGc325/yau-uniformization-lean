import Yau.Proofs.F03UnboundedHeatMeanBudget
import Yau.Proofs.F03FlowTimeEnvelope

/-! The original localized-flow rho averages yield the actual matching-scale heat mean, uniformly on the whole slab. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem localizedFlow_rho_matching_heat_mean
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ L : ℝ,1 ≤ L →
      ∀ x,inducedDistance X.metric.form o x ≤ C₀*L →
      Integrable (fun y => dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y*ρ y s) μ ∧
      (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO (L^2) x y*ρ y s ∂μ) ≤ C*L := by
  obtain ⟨A,hMean⟩ := hf.2.2.2.2.2.2.2.2.2.2.2.1 T hT.le
  obtain ⟨K,hK,hBudget⟩ := dirichletMinimalKernel_linear_ball_mean_bound X o h U P ρ hf C₀ hC₀
  let M := max A 1
  have hM : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨K*M,mul_pos hK hM,fun μ hμ O hO s hs L hL x hx => ?_⟩
  have hActual := hBudget μ hμ O hO (fun y => ρ y s)
    (continuous_of_smoothFn (LeafProofs.L19Aux.smoothSpaceTime_slice hf.2.2.2.1 hs.1)).measurable
    (fun y => (hf.2.2.2.2.2.2.2.2.2.1 y s hs.1).2) M hM.le
    (fun R hR => F02Aux.ballIntegralLE_mono_bound X.metric.form μ o (fun y => ρ y s) R
      (hMean μ hμ R hR s hs)
      (mul_le_mul_of_nonneg_right (le_max_left A 1) (zero_le_one.trans hR))) L hL x hx
  exact ⟨hActual.1,by simpa only [mul_assoc] using hActual.2⟩

end Yau.Proofs.F03Aux
