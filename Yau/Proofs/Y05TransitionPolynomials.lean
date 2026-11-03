import Yau.Proofs.Y05GlobalJetDecay
import Yau.Proofs.Y05LogData

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open scoped ContDiff Topology

variable {n : ℕ}

theorem exists_transition_log_polynomials
    {T : ℕ → ℕ → ComplexVector n → ComplexVector n}
    {P : ℕ → ComplexVector n → ℂ} {s : ℕ → ℝ} {r σ C K : ℝ} {d : ℕ}
    (hr : 0 < r) (hC : 0 < C) (hK : 0 ≤ K)
    (hs : ∀ k, 0 < s k) (hsm : Monotone s)
    (hTa : ∀ k l, k ≤ l → AnalyticAt ℂ (T k l) 0)
    (hT0 : ∀ k l, k ≤ l → T k l 0 = 0)
    (hPd : ∀ k, DifferentiableOn ℂ (P k) (Metric.ball 0 r))
    (hP0 : ∀ k, P k 0 = 0)
    (hPjet : ∀ k m, m ≤ d → ‖iteratedFDeriv ℂ m (P k) 0‖ ≤
      K * (1 + (s (k + 1) - s k)))
    (hdecay : ∀ k l, k ≤ l → jetNorm (T k l) d ≤
      C * min 1 (Real.exp (C * s k - σ * s l))) :
    ∃ (D L : ℝ) (B : ℕ → ℕ → MvPolynomial (Fin n) ℂ),
      1 ≤ D ∧ 0 ≤ L ∧ ∀ k l, k ≤ l →
        (B k l).totalDegree ≤ d ∧ (B k l).coeff 0 = 0 ∧
        ScalarJetEq (scalarEval (B k l)) (fun z => P l (T k l z)) d ∧
        polynomialCoeffNorm (B k l) ≤ L * (1 + (s (l + 1) - s l)) *
          min 1 (Real.exp (D * s k - σ * s l)) := by
  let D := 1 + C
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hCD : C ≤ D := by dsimp [D]; linarith
  have hdecayD (k l : ℕ) (hkl : k ≤ l) : jetNorm (T k l) d ≤
      D * min 1 (Real.exp (D * s k - σ * s l)) := by
    apply (hdecay k l hkl).trans
    apply mul_le_mul hCD
      (min_le_min le_rfl (Real.exp_le_exp.mpr (by nlinarith [hs k])))
      (le_min (by norm_num) (Real.exp_pos _).le) (le_trans zero_le_one hD)
  let L := scalarTaylorConstant n d * compositionJetConstant d * K * D ^ d
  have hL : 0 ≤ L := by
    dsimp [L, scalarTaylorConstant, compositionJetConstant]
    positivity
  have hPa (k : ℕ) : AnalyticAt ℂ (P k) 0 :=
    U02AnalyticAux.analyticOnNhd_of_complex_contDiffOn_infty Metric.isOpen_ball
      (Yau.Blueprint.V03Proof.complex_holomorphic_contDiffOn Metric.isOpen_ball (hPd k))
      0 (Metric.mem_ball_self hr)
  have hex (k l : ℕ) : ∃ B : MvPolynomial (Fin n) ℂ, k ≤ l →
      B.totalDegree ≤ d ∧ B.coeff 0 = 0 ∧
      ScalarJetEq (scalarEval B) (fun z => P l (T k l z)) d ∧
      polynomialCoeffNorm B ≤ L * (1 + (s (l + 1) - s l)) *
        min 1 (Real.exp (D * s k - σ * s l)) := by
    by_cases hkl : k ≤ l
    · let δ := min 1 (Real.exp (D * s k - σ * s l))
      have hδ : 0 ≤ δ := le_min (by norm_num) (Real.exp_pos _).le
      have hδ1 : δ ≤ 1 := min_le_left _ _
      have hstep : 0 ≤ s (l + 1) - s l := sub_nonneg.mpr (hsm (Nat.le_succ l))
      have hG : 0 ≤ K * (1 + (s (l + 1) - s l)) := mul_nonneg hK (by linarith)
      have hfb (m : ℕ) (_hm : 1 ≤ m) (hm : m ≤ d) :
          ‖iteratedFDeriv ℂ m (T k l) 0‖ ≤ D * δ :=
        (norm_jet_component_le (T k l) hm).trans (hdecayD k l hkl)
      obtain ⟨B, hdeg, hzero, hjet, hnorm⟩ := exists_composed_taylor_bound
        (hTa k l hkl) (hPa l) (hT0 k l hkl) (hP0 l) hD hG hδ hδ1
        (hPjet l) hfb
      refine ⟨B, fun _ => ⟨hdeg, hzero, hjet, hnorm.trans_eq ?_⟩⟩
      dsimp [L]
      ring
    · exact ⟨0, fun h => False.elim (hkl h)⟩
  choose B hB using hex
  exact ⟨D, L, B, hD, hL, hB⟩

end Yau.Proofs.Y05Aux
