import Yau.Proofs.F03KernelGradientGaussian
import Yau.Proofs.F03TerminalEnvelopeGaussian

/-! On a genuine positive heat-time band one integrable function controls the kernel and its first gradient. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_positive_band_gaussian
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    {ε B : ℝ} (hε : 0 < ε) (hεB : ε ≤ B) (x : Pt X) :
    ∃ C c R : ℝ,0 < C ∧ 0 < c ∧ 1 ≤ R ∧ ∀ b ∈ Icc ε B,∀ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y ≤
        C*Real.exp (-c*(inducedDistance X.metric.form o y/R)^2) ∧
      Real.sqrt (gradNormSq X.metric.form (fun z =>
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x z) y) ≤
        C*Real.exp (-c*(inducedDistance X.metric.form o y/R)^2) := by
  let L := max 1 (Real.sqrt B)
  have hL : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let C₀ := inducedDistance X.metric.form o x/L
  have hC₀ : 0 ≤ C₀ := div_nonneg (X.metric.induced_distance_nonneg o x) hL0.le
  have hx : inducedDistance X.metric.form o x ≤ C₀*L := by
    dsimp [C₀]
    rw [div_mul_cancel₀ _ hL0.ne']
  obtain ⟨K,c₀,hK,hc₀,hKernel⟩ := dirichletMinimalKernelCandidate_coarse_gaussian X o h U P ρ hf C₀ hC₀
  obtain ⟨G,c₁,hG,hc₁,hGradient⟩ :=
    dirichletMinimalKernelCandidate_right_gradient_coarse_gaussian X o h U P ρ hf C₀ hC₀
  let R := (C₀+1)*L
  have hR : 1 ≤ R := by dsimp [R];nlinarith
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let V := (μ (distBall X.metric.form o R)).toReal
  have hV : 0 < V := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos X.metric μ hμ o hR0).ne'
    (riemannianVolume_distBall_lt_top X.metric μ hμ o hR0).ne
  let D := (L/Real.sqrt ε)^(2*n)
  have hD : 0 < D := pow_pos (div_pos hL0 (Real.sqrt_pos.mpr hε)) _
  let C := (K+G/Real.sqrt ε)*D/V
  refine ⟨C,min c₀ c₁,R,by dsimp [C];positivity,lt_min hc₀ hc₁,hR,?_⟩
  intro b hb y
  have hb0 : 0 < b := hε.trans_le hb.1
  have hbL : b ≤ L^2 := by
    have hBL : Real.sqrt B ≤ L := le_max_right _ _
    exact hb.2.trans (Real.sqrt_le_iff.mp hBL).2
  have hr : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  have hεr : Real.sqrt ε ≤ Real.sqrt b := Real.sqrt_le_sqrt hb.1
  have hRatio : (L/Real.sqrt b)^(2*n) ≤ D :=
    pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left hL0.le (Real.sqrt_pos.mpr hε) hεr) _
  have hGDiv : G/Real.sqrt b ≤ G/Real.sqrt ε :=
    div_le_div_of_nonneg_left hG.le (Real.sqrt_pos.mpr hε) hεr
  have hE₀ : Real.exp (-c₀*(inducedDistance X.metric.form o y/R)^2) ≤
      Real.exp (-(min c₀ c₁)*(inducedDistance X.metric.form o y/R)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr (min_le_left c₀ c₁))
      (sq_nonneg (inducedDistance X.metric.form o y/R))]
  have hE₁ : Real.exp (-c₁*(inducedDistance X.metric.form o y/R)^2) ≤
      Real.exp (-(min c₀ c₁)*(inducedDistance X.metric.form o y/R)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr (min_le_right c₀ c₁))
      (sq_nonneg (inducedDistance X.metric.form o y/R))]
  constructor
  · calc
      _ ≤ K*(L/Real.sqrt b)^(2*n)*Real.exp (-c₀*(inducedDistance X.metric.form o y/R)^2)/V :=
        hKernel μ hμ O hO L hL b hb0 hbL x hx y
      _ ≤ K*D*Real.exp (-(min c₀ c₁)*(inducedDistance X.metric.form o y/R)^2)/V :=
        div_le_div_of_nonneg_right (mul_le_mul
          (mul_le_mul_of_nonneg_left hRatio hK.le) hE₀ (by positivity) (by positivity)) hV.le
      _ ≤ C*Real.exp (-(min c₀ c₁)*(inducedDistance X.metric.form o y/R)^2) := by
        have hCoeff : K*D/V ≤ C := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hD.le) hV.le
        convert mul_le_mul_of_nonneg_right hCoeff
          (Real.exp_pos (-(min c₀ c₁)*(inducedDistance X.metric.form o y/R)^2)).le using 1 <;> ring
  · calc
      _ ≤ G/Real.sqrt b*(L/Real.sqrt b)^(2*n)*Real.exp (-c₁*(inducedDistance X.metric.form o y/R)^2)/V :=
        hGradient μ hμ O hO L hL b hb0 hbL x hx y
      _ ≤ (G/Real.sqrt ε)*D*Real.exp (-(min c₀ c₁)*(inducedDistance X.metric.form o y/R)^2)/V :=
        div_le_div_of_nonneg_right (mul_le_mul
          (mul_le_mul hGDiv hRatio (by positivity) (by positivity)) hE₁
          (by positivity) (by positivity)) hV.le
      _ ≤ C*Real.exp (-(min c₀ c₁)*(inducedDistance X.metric.form o y/R)^2) := by
        have hCoeff : (G/Real.sqrt ε)*D/V ≤ C := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK.le) hD.le) hV.le
        convert mul_le_mul_of_nonneg_right hCoeff
          (Real.exp_pos (-(min c₀ c₁)*(inducedDistance X.metric.form o y/R)^2)).le using 1 <;> ring

end Yau.Proofs.F03Aux
