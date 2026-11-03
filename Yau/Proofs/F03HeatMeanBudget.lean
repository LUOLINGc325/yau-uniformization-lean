import Yau.Proofs.F03CoarseKernelBound
import Yau.Proofs.F03GaussianAverageBudget
import Yau.Proofs.F03MinimalBoundedEvolution

/-! Ball-average data give an actual uniform mean bound for the same minimal heat kernel. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder ENNReal
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem integral_le_of_gaussian_lintegral_budget {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f q : α → ℝ) (hf : Integrable f μ) (hf0 : ∀ y,0 ≤ f y)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hPoint : ∀ y,f y ≤ K*q y)
    (hBudget : (∫⁻ y,ENNReal.ofReal (q y) ∂μ) ≤ ENNReal.ofReal B) :
    (∫ y,f y ∂μ) ≤ K*B := by
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK hB)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hf (ae_of_all μ hf0),ENNReal.ofReal_mul hK]
  calc
    _ ≤ ∫⁻ y,ENNReal.ofReal K*ENNReal.ofReal (q y) ∂μ := by
      apply lintegral_mono
      intro y
      change ENNReal.ofReal (f y) ≤ ENNReal.ofReal K*ENNReal.ofReal (q y)
      rw [← ENNReal.ofReal_mul hK]
      exact ENNReal.ofReal_le_ofReal (hPoint y)
    _ = ENNReal.ofReal K*(∫⁻ y,ENNReal.ofReal (q y) ∂μ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_of_nonneg_left hBudget (by positivity)

theorem dirichletMinimalBoundedHeat_ball_mean_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (f : Pt X → ℝ),Measurable f → (∃ B : ℝ,∀ y,|f y| ≤ B) →
      (∀ y,0 ≤ f y) → ∀ A : ℝ,0 ≤ A →
      (∀ R : ℝ,1 ≤ R → BallIntegralLE X.metric.form μ o f R (A/R)) →
      ∀ L : ℝ,1 ≤ L → ∀ b : ℝ,0 < b → b ≤ L^2 →
      ∀ x,inducedDistance X.metric.form o x ≤ C₀*L →
      boundedKernelEvolution μ (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO) f b x ≤
        C*A/L*(L/Real.sqrt b)^(2*n) := by
  obtain ⟨K,c,hK,hc,hKernel⟩ := dirichletMinimalKernelCandidate_coarse_gaussian X o h U P ρ hf C₀ hC₀
  obtain ⟨J,hJ,hBudget⟩ := exists_gaussian_average_budget X.metric X.complete_metric X.kahler_metric
    (F02Aux.initialRicci_posSemidef X o h U P ρ hf) hc
  refine ⟨K*J,mul_pos hK hJ,fun μ hμ O hO f hfMeas hfBound hf0 A hA hMean L hL b hb hbL x hx => ?_⟩
  let D := C₀+1
  let R := D*L
  let V := (μ (distBall X.metric.form o R)).toReal
  let q := (L/Real.sqrt b)^(2*n)
  have hD : 1 ≤ D := by dsimp [D];linarith
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hR1 : 1 ≤ R := by dsimp [R];nlinarith
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  have hLR : L ≤ R := by dsimp [R];nlinarith
  have hV : 0 < V := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos X.metric μ hμ o hR0).ne'
    (riemannianVolume_distBall_lt_top X.metric μ hμ o hR0).ne
  have hq : 0 ≤ q := by dsimp [q];positivity
  have hInt := dirichletMinimalKernelCandidate_bounded_source_integrable X.metric X.kahler_metric
    μ hμ O hO f hfMeas.aestronglyMeasurable hfBound hb x
  have hIntegral := integral_le_of_gaussian_lintegral_budget μ
    (fun y => dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*f y)
    (fun y => Real.exp (-c*(inducedDistance X.metric.form o y/R)^2)*f y) hInt
    (fun y => mul_nonneg (dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb x y) (hf0 y))
    (K := K*q/V) (B := J*A/R*V) (by positivity) (by positivity)
    (fun y => by
      have hh := mul_le_mul_of_nonneg_right (hKernel μ hμ O hO L hL b hb hbL x hx y) (hf0 y)
      convert hh using 1 <;> dsimp [q,R,D,V] <;> ring)
    (hBudget μ hμ o f hfMeas A hA hMean R hR1)
  rw [boundedKernelEvolution,if_neg hb.ne']
  calc
    _ ≤ (K*q/V)*(J*A/R*V) := hIntegral
    _ = (K*J*A/R)*q := by field_simp
    _ ≤ (K*J*A/L)*q := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by positivity) hL0 hLR) hq

end Yau.Proofs.F03Aux
