import Yau.Proofs.U02Contraction
import Yau.Proofs.U02InverseBallBudget
import Yau.Proofs.U02ChartShadow
import Yau.Proofs.U02CorrectedOrbits

/-! The actual map `G_{0,k} Ψ Φ_{t_k}` maps a smaller raw ball onto
the prescribed target ball. This gives the original inverse-ball inclusion. -/

open scoped Manifold Topology ContDiff Matrix
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem models_forward_prefix_zero {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv) :
    ∀ k, (forwardComp G k).eval 0 = 0 := by
  intro k
  induction k with
  | zero => exact polynomial_eval_id 0
  | succ k ih =>
    rw [forwardComp, polynomial_eval_comp, ih,
      polynomial_fixesZero_eval_zero (G k) (hp.2.2.2.2.1 k).2.2.2.1]

theorem inverse_ball_of_actual_chart_shadow {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {psi : Pt X → ComplexVector n}
    (hpsi : ContMDiff (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ psi) (hpsi0 : psi o = 0)
    {gamma gammap : ℝ} (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) (hgap : gamma < gammap)
    (hshadow : ∀ᶠ k in atTop, ∀ z ∈ closedBall (0 : ComplexVector n)
      (Real.exp (-gamma * rho o (tk k))),
      ‖(forwardComp G k).eval (psi (Phi (tk k) z)) - (H k).eval z‖ ≤
        Real.exp (-6 * rho o (tk k))) :
    ∀ᶠ k in atTop, ∀ w : ComplexVector n, ‖w‖ < Real.exp (-gammap * rho o (tk k)) →
      (backwardComp Ginv k).eval w ∈ Set.range psi := by
  filter_upwards [hshadow, inverse_ball_cauchy_budget hp hgamma hgamma1 hgap,
    eventually_models_time_ge hf hp ht t0,
    eventually_exp_decay_lt hp.2.1 hgamma (hc.1.trans hc.2.1),
    eventually_exp_decay_lt hp.2.1 hgamma (by norm_num : (0 : ℝ) < 1)]
    with k hsh hbudget htime hr0 hr1
  let r := Real.exp (-gamma * rho o (tk k))
  let T := fun z => (forwardComp G k).eval (psi (Phi (tk k) z))
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (H k).linearPart
  let Ai := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (H k).linearPart⁻¹
  let M := 2 * (H k).coeffNorm * r ^ 2 + Real.exp (-6 * rho o (tk k))
  have hr : 0 < r := Real.exp_pos _
  have hCoeff : 0 ≤ (H k).coeffNorm := Yau.Proofs.Y02Aux.coeffNorm_nonneg _
  have hchart := hc.2.2.2.2.1 (tk k) htime
  have hT : DifferentiableOn ℂ T (ball 0 r0) :=
    ((polynomial_contDiff (forwardComp G k)).differentiable (by simp)).comp_differentiableOn
      (((hpsi.mdifferentiable (by simp)).comp_mdifferentiableOn
        (hchart.1.1.mdifferentiableOn (by simp))).differentiableOn)
  have hT0 : T 0 = 0 := by
    dsimp only [T]
    rw [hchart.2.1, hpsi0, models_forward_prefix_zero hp k]
  have hdet := (hp.2.2.2.2.1 k).2.2.2.2.2.1
  have hleft : Ai.comp A = ContinuousLinearMap.id ℂ (ComplexVector n) := by
    change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (H k).linearPart⁻¹ *
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (H k).linearPart = 1
    rw [← map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), map_one]
  have hright : A.comp Ai = ContinuousLinearMap.id ℂ (ComplexVector n) := by
    change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (H k).linearPart *
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (H k).linearPart⁻¹ = 1
    rw [← map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), map_one]
  have hM : 0 ≤ M := by
    positivity
  have hbound : ∀ z ∈ closedBall (0 : ComplexVector n) r, ‖T z - A z‖ ≤ M := by
    intro z hz
    have hz' : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hq := polynomial_quadratic_error (H k) (hp.2.2.2.2.1 k).1 (hz'.trans hr1.le)
    have hh := norm_sub_le_norm_sub_add_norm_sub (T z) ((H k).eval z) (A z)
    have hqr := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz' 2)
      (by positivity : 0 ≤ 2 * (H k).coeffNorm)
    have hshz := hsh z hz
    dsimp only [M]
    linarith
  have hball : closedBall (0 : ComplexVector n) (2 * (r / 2)) ⊆ ball 0 r0 := by
    rw [show 2 * (r / 2) = r by ring]
    exact closedBall_subset_ball hr0
  have hD : ∀ z ∈ closedBall (0 : ComplexVector n) (r / 2),
      ‖Ai.comp (fderiv ℂ T z - A)‖ ≤ 1 / 4 := by
    intro z hz
    have hd := V02FlowProof.norm_fderiv_sub_le_of_cauchy isOpen_ball hT A.differentiable.differentiableOn
      (by positivity : 0 < r / 2) hM hball (by simpa only [show 2 * (r / 2) = r by ring] using hbound) hz
    rw [A.fderiv] at hd
    exact (ContinuousLinearMap.opNorm_comp_le Ai (fderiv ℂ T z - A)).trans
      ((mul_le_mul_of_nonneg_left hd (norm_nonneg Ai)).trans hbudget.1)
  intro w hw
  have hw' : ‖Ai w‖ ≤ (r / 2) / 2 := by
    calc
      _ ≤ ‖Ai‖ * ‖w‖ := Ai.le_opNorm w
      _ ≤ ‖Ai‖ * Real.exp (-gammap * rho o (tk k)) :=
        mul_le_mul_of_nonneg_left hw.le (norm_nonneg Ai)
      _ ≤ r / 4 := hbudget.2
      _ = _ := by ring
  obtain ⟨z, _hz, hTz⟩ := U02ContractionAux.exists_preimage_of_small_derivative T A Ai hleft hright
    isOpen_ball hT hT0 (by positivity : 0 < r / 2)
    (closedBall_subset_ball (by linarith : r / 2 < r0)) hD w hw'
  refine ⟨Phi (tk k) z, ?_⟩
  have hpref := hp.2.2.2.2.2.2.2.2.2 k
  rw [← hTz]
  dsimp only [T]
  rw [← polynomial_eval_comp, hpref.2, polynomial_eval_id]

end Yau.NodeProofs.U02Proof
