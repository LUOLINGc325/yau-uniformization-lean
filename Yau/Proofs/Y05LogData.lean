import Yau.Proofs.Y05TransitionLogs
import Yau.Proofs.Y05PolynomialEstimates

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open scoped ContDiff

variable {n : ℕ}

/-- One normalized logarithm for each actual transition, on one common
ball; every fixed-order jet has the required linear step-length bound. -/
theorem exists_shrinking_transition_logs {X : KahlerManifold n}
    {o : Pt X} {h : Flow X} {ρ : STF X} {r₀ r₁ σ C Cb t₀ : ℝ}
    {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n}
    (hc : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} (htk : StrictMono tk) (hlate : ∀ k, t₀ ≤ tk k)
    (hclock : Monotone (fun k => ρ o (tk k))) :
    ∃ P : ℕ → ComplexVector n → ℂ,
      (∀ k, P k 0 = 0 ∧ DifferentiableOn ℂ (P k) (Metric.ball 0 (r₁ / 2)) ∧
        ∀ z ∈ Metric.ball (0 : ComplexVector n) (r₁ / 2),
          Complex.exp (P k z) = transitionDet F (tk k) (tk (k + 1)) z /
            transitionDet F (tk k) (tk (k + 1)) 0) ∧
      ∀ d : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ k m, m ≤ d →
        ‖iteratedFDeriv ℂ m (P k) 0‖ ≤ K * (1 + (ρ o (tk (k + 1)) - ρ o (tk k))) := by
  rcases hc with ⟨hr, hr0, hσ, hC, hcharts, htrans, hcomp, hf0, hinv, hdec, hj, hreg⟩
  have hCb : 0 ≤ Cb := (norm_nonneg (F t₀ t₀ 0)).trans
    (((htrans t₀ t₀ le_rfl le_rfl).2.1 0 (Metric.mem_ball_self hr)).2)
  have hlogs (k : ℕ) := exists_transition_log hr hCb
    (htrans (tk k) (tk (k + 1)) (hlate k) (htk.monotone (Nat.le_succ k))).1
    (fun z hz => ((htrans (tk k) (tk (k + 1)) (hlate k)
      (htk.monotone (Nat.le_succ k))).2.1 z hz).2)
    (fun z hz => ((htrans (tk k) (tk (k + 1)) (hlate k)
      (htk.monotone (Nat.le_succ k))).2.1 z hz).1)
    (htrans (tk k) (tk (k + 1)) (hlate k)
      (htk.monotone (Nat.le_succ k))).2.2.2.2.2.1
  choose P hP0 hPd hPexp hPre using hlogs
  refine ⟨P, fun k => ⟨hP0 k, hPd k, hPexp k⟩, ?_⟩
  intro d
  let H := Real.log (transitionDetBound n r₁ Cb)
  have hH : 0 ≤ H := Real.log_nonneg (le_max_left _ _)
  have hJ : 0 ≤ polynomialJetConstant d := Finset.sum_nonneg fun m _ => by positivity
  have hL : 0 < logJetConstant n d (r₁ / 2) := logJetConstant_pos n d (by positivity)
  let K := 1 + polynomialJetConstant d * logJetConstant n d (r₁ / 2) * (H + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro k m hm
  let Δ := ρ o (tk (k + 1)) - ρ o (tk k)
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (hclock (Nat.le_succ k))
  have hM : 0 < H + 1 + Δ / 2 := by linarith
  obtain ⟨B, hBdeg, hB0, hBjet, hBnorm⟩ := exists_scalar_taylor_bound_of_boundedRe
    (by positivity : 0 < r₁ / 2) hM (hPd k) (hP0 k)
    (fun z hz => (hPre k z hz).trans (by dsimp [H, Δ]; linarith)) d
  rw [← hBjet m hm]
  apply (polynomial_jet_norm_le B hm).trans
  have hMbound : H + 1 + Δ / 2 ≤ (H + 1) * (1 + Δ) := by
    nlinarith [mul_nonneg hH hΔ]
  calc
    polynomialJetConstant d * polynomialCoeffNorm B ≤
        polynomialJetConstant d * (logJetConstant n d (r₁ / 2) * (H + 1 + Δ / 2)) :=
      mul_le_mul_of_nonneg_left hBnorm hJ
    _ ≤ polynomialJetConstant d * (logJetConstant n d (r₁ / 2) *
        ((H + 1) * (1 + Δ))) := by gcongr
    _ ≤ K * (1 + Δ) := by dsimp [K]; nlinarith

end Yau.Proofs.Y05Aux
