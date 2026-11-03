import Yau.Proofs.F03GaussianSingleCenter
import Yau.Proofs.F03BallCenterTransfer

/-! Actual Bishop--Gromov isolates the exact small-time polynomial loss of the same kernel. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux LeafProofs.L24Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_small_time_gaussian
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (x : Pt X) :
    ∃ C c : ℝ,0 < C ∧ 0 < c ∧ ∀ b : ℝ,0 < b → b ≤ 1 → ∀ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y ≤
        C*(b⁻¹)^n*Real.exp (-c*inducedDistance X.metric.form x y^2/b) := by
  obtain ⟨K,c,hK,hc,hBound⟩ := dirichletMinimalKernelCandidate_single_center_gaussian X o h U P ρ hf
  let V := (μ (distBall X.metric.form x 1)).toReal
  have hV : 0 < V := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos X.metric μ hμ x zero_lt_one).ne'
    (riemannianVolume_distBall_lt_top X.metric μ hμ x zero_lt_one).ne
  let C := K*2^(2*n)/V
  refine ⟨C,c,by dsimp [C];positivity,hc,?_⟩
  intro b hb hb1 y
  have hr : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hr1 : Real.sqrt b ≤ 1 := Real.sqrt_le_iff.mpr ⟨zero_le_one,by simpa only [one_pow] using hb1⟩
  have hInv := ball_inverse_volume_center_transfer X.metric X.complete_metric X.kahler_metric
    (F02Aux.initialRicci_posSemidef X o h U P ρ hf) μ hμ x x hr hr1
      (by rw [X.metric.induced_distance_eq_zero.mpr rfl];norm_num)
  have hPow : (Real.sqrt b)^(2*n)=b^n := by rw [pow_mul,Real.sq_sqrt hb.le]
  calc
    _ ≤ K*Real.exp (-c*inducedDistance X.metric.form x y^2/b)*
        (1/(μ (distBall X.metric.form x (Real.sqrt b))).toReal) := by
      simpa only [distFrom,lengthDist,div_eq_mul_inv,one_mul] using hBound μ hμ O hO b hb x y
    _ ≤ K*Real.exp (-c*inducedDistance X.metric.form x y^2/b)*
        ((2/Real.sqrt b)^(2*n)/V) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [mul_one] using hInv
    _ = _ := by
      rw [div_pow,hPow]
      dsimp [C]
      simp only [div_eq_mul_inv,inv_pow]
      ring

end Yau.Proofs.F03Aux
