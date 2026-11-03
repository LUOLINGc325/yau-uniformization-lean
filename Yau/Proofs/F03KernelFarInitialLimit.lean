import Yau.Proofs.F03SmallTimeKernelGaussian
import Yau.Proofs.F03GaussianSmallTimeNumerics
import Yau.Proofs.F03TranslatedGaussianEnvelope

/-! Actual off-diagonal Gaussian tails give the true initial limit for every terminal-density dominated far source. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_far_source_initial_limit
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (x : Pt X)
    (f : Pt X → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hBound : ∀ y,|f y| ≤ A*(1+ρ y T))
    (hFar : ∀ y,inducedDistance X.metric.form x y ≤ 1 → f y=0) :
    Tendsto (fun b => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*f y ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,c,hC,hc,hKernel⟩ := dirichletMinimalKernel_small_time_gaussian X o h U P ρ hf μ hμ O hO x
  let E : Pt X → ℝ := fun y => Real.exp (-(c/2)*inducedDistance X.metric.form x y^2)*(1+ρ y T)
  have hE : Integrable E μ := localizedFlow_translated_gaussian_envelope_integrable
    X o h U P ρ hf hT μ hμ x (half_pos hc)
  have hE0 (y : Pt X) : 0 ≤ E y := by
    have hρ0 := (hf.2.2.2.2.2.2.2.2.2.1 y T hT).2
    dsimp [E]
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  have hEstimate (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
      |∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*f y ∂μ| ≤
        (C*A*(b⁻¹)^n*Real.exp (-(c/2)/b))*(∫ y,E y ∂μ) := by
    have hNorm : |∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*f y ∂μ| ≤
        ∫ y,(C*A*(b⁻¹)^n*Real.exp (-(c/2)/b))*E y ∂μ := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hE.const_mul _)
      apply ae_of_all μ
      intro y
      change |dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*f y| ≤ _
      by_cases hy : inducedDistance X.metric.form x y ≤ 1
      · rw [hFar y hy,mul_zero,abs_zero]
        exact mul_nonneg (by positivity) (hE0 y)
      have hρ0 := (hf.2.2.2.2.2.2.2.2.2.1 y T hT).2
      have hρ1 : 0 ≤ 1+ρ y T := by linarith
      have hH0 := dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb x y
      have hSplit := small_time_gaussian_split hc.le zero_le_one (le_of_not_ge hy) hb hb1
      simp only [one_pow,mul_one] at hSplit
      rw [abs_mul,abs_of_nonneg hH0]
      calc
        _ ≤ dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*(A*(1+ρ y T)) :=
          mul_le_mul_of_nonneg_left (hBound y) hH0
        _ ≤ (C*(b⁻¹)^n*Real.exp (-c*inducedDistance X.metric.form x y^2/b))*(A*(1+ρ y T)) :=
          mul_le_mul_of_nonneg_right (hKernel b hb hb1 y) (mul_nonneg hA hρ1)
        _ ≤ (C*(b⁻¹)^n*(Real.exp (-(c/2)/b)*Real.exp (-(c/2)*inducedDistance X.metric.form x y^2)))*
            (A*(1+ρ y T)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSplit (by positivity)) (mul_nonneg hA hρ1)
        _ = _ := by dsimp [E];ring
    simpa only [integral_const_mul] using hNorm
  have hAmp := ((inv_pow_mul_exp_neg_div_tendsto_zero n (half_pos hc)).const_mul (C*A)).mul_const
    (∫ y,E y ∂μ)
  simp only [mul_zero,zero_mul] at hAmp
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hPos : ∀ᶠ b : ℝ in 𝓝[>] 0,0 < b := self_mem_nhdsWithin
  have hSmall : ∀ᶠ b : ℝ in 𝓝[>] 0,b < 1 :=
    (eventually_lt_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hPos,hSmall,hAmp.eventually (gt_mem_nhds hδ)] with b hb hb1 hClose
  rw [Real.dist_eq,sub_zero]
  exact (hEstimate b hb hb1.le).trans_lt (by convert hClose using 1 <;> ring)

end Yau.Proofs.F03Aux
