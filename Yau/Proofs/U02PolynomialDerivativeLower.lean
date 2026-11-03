import Yau.Proofs.U02ModelSeparation

/-! The small nonlinear error preserves the actual differential conorm. -/

open scoped Topology Matrix
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem polynomial_derivative_lower {n : ℕ} (P : PolyMap n) (hP : P.FixesZero)
    (hdet : P.linearPart.det ≠ 0) {r : ℝ} (hr : 0 < r) (hr1 : 2 * r ≤ 1)
    (hsmall : matOpNorm P.linearPart⁻¹ * (8 * P.coeffNorm * r) ≤ 1 / 2)
    {z : ComplexVector n} (hz : z ∈ closedBall 0 r) (v : ComplexVector n) :
    ‖v‖ ≤ 2 * matOpNorm P.linearPart⁻¹ * ‖fderiv ℂ P.eval z v‖ := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart
  let Ai := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart⁻¹
  let K := matOpNorm P.linearPart⁻¹
  have hK : 0 ≤ K := norm_nonneg Ai
  have hmul : Ai * A = 1 := by
    change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart⁻¹ *
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) P.linearPart = 1
    rw [← map_mul, Matrix.nonsing_inv_mul P.linearPart (isUnit_iff_ne_zero.mpr hdet), map_one]
  have hrecover : Ai (A v) = v := by
    change (Ai * A) v = v
    rw [hmul]
    rfl
  have hlower : ‖v‖ ≤ K * ‖A v‖ := by
    calc
      ‖v‖ = ‖Ai (A v)‖ := congrArg norm hrecover.symm
      _ ≤ _ := Ai.le_opNorm (A v)
  have he : ‖fderiv ℂ P.eval z v - A v‖ ≤ (8 * P.coeffNorm * r) * ‖v‖ := by
    exact ((fderiv ℂ P.eval z - A).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (polynomial_derivative_error P hP hr hr1 hz) (norm_nonneg v))
  have htri : ‖A v‖ ≤ ‖fderiv ℂ P.eval z v‖ + ‖fderiv ℂ P.eval z v - A v‖ := by
    have hh := norm_sub_le (fderiv ℂ P.eval z v) (fderiv ℂ P.eval z v - A v)
    have heq : fderiv ℂ P.eval z v - (fderiv ℂ P.eval z v - A v) = A v := by abel
    simpa only [heq] using hh
  have hbound := mul_le_mul_of_nonneg_left (htri.trans (add_le_add le_rfl he)) hK
  have hpaid := mul_le_mul_of_nonneg_right hsmall (norm_nonneg v)
  change ‖v‖ ≤ 2 * K * ‖fderiv ℂ P.eval z v‖
  dsimp only [K] at hK hlower hbound ⊢
  nlinarith

theorem models_H_derivative_lower {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {rho : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ k in atTop, ∀ z : ComplexVector n, ‖z‖ ≤ Real.exp (-a * rho o (tk k)) →
      ∀ v : ComplexVector n,
        ‖v‖ ≤ 2 * matOpNorm (H k).linearPart⁻¹ * ‖fderiv ℂ (H k).eval z v‖ := by
  obtain ⟨eta, heta, hcoeff⟩ := hp.2.2.2.2.2.2.2.1
  filter_upwards [models_H_inverse_linear_exp hp (by positivity : 0 < a / 4),
    subexponential_absorption hp.2.1 heta 16 (by positivity : 0 < a / 4),
    eventually_exp_decay_lt hp.2.1 ha (by norm_num : (0 : ℝ) < 1 / 2),
    (tendsto_atTop.1 hp.2.1) 0] with k hlin hcoef hr hsk
  have hc : 16 * (H k).coeffNorm ≤ Real.exp ((a / 4) * rho o (tk k)) :=
    (mul_le_mul_of_nonneg_left (hcoeff k).1 (by norm_num)).trans hcoef
  have hsmall : matOpNorm (H k).linearPart⁻¹ *
      (8 * (H k).coeffNorm * Real.exp (-a * rho o (tk k))) ≤ 1 / 2 := by
    have hA0 : 0 ≤ matOpNorm (H k).linearPart⁻¹ := norm_nonneg _
    have hC0 : 0 ≤ (H k).coeffNorm := Yau.Proofs.Y02Aux.coeffNorm_nonneg _
    have hprod := mul_le_mul hlin hc (by positivity) (Real.exp_pos _).le
    have he : Real.exp ((a / 4) * rho o (tk k)) *
        Real.exp ((a / 4) * rho o (tk k)) * Real.exp (-a * rho o (tk k)) ≤ 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    have hh := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-a * rho o (tk k))).le
    nlinarith
  intro z hz v
  have hn := hp.2.2.2.2.1 k
  exact polynomial_derivative_lower (H k) hn.1 hn.2.2.2.2.2.1 (Real.exp_pos _)
    (by linarith) hsmall (by simpa only [mem_closedBall, dist_zero_right] using hz) v

end Yau.NodeProofs.U02Proof
