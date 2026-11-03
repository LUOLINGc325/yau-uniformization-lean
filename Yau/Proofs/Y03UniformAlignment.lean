import Yau.Proofs.Y03LocalExtension
import Yau.Proofs.Y03InfiniteRun
import Yau.Proofs.Y03PolynomialBudget
import Yau.Proofs.Y03BootstrapThreshold

/-! One late threshold closes every finite horizon and every infinite regular tail for the actual frames. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem uniform_alignment_runs {hm eps B γ : ℝ} (hhm : 0 < hm) (heps : 0 < eps)
    (hB : 0 < B) (hγ : 0 < γ) :
    ∃ J : ℕ, ∀ (Q : ℕ → ℝ) (N : ℕ) (M scale K b : ℝ) (j₀ : ℕ), J ≤ j₀ →
      ∀ (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (tk : ℕ → ℝ) (E : Frames n),
        SingularFrames F tk E → RateOrder F tk E →
        WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E) →
        (∀ k, Regular Q N M (macroAt Q N M hm j₀ k) → Regular Q N M (macroAt Q N M hm j₀ (k + 1)) →
          0 < Q (macroAt Q N M hm j₀ k) ∧
          (∀ i, 0 ≤ rate F tk E k i ∧ rate F tk E k i ≤ B * Q (macroAt Q N M hm j₀ k)) ∧
          (∀ i, 0 ≤ rate F tk E (k + 1) i ∧ rate F tk E (k + 1) i ≤ B * Q (macroAt Q N M hm j₀ k)) ∧
          γ * Real.sqrt (macroClock hm (macroAt Q N M hm j₀ k)) / (macroAt Q N M hm j₀ k : ℝ) ^ 2 ≤
            theta Q (macroAt Q N M hm j₀ k) * Real.log (tk (k + 1) / tk k)) →
        AlignmentRuns E (diagonal F tk E) (weight Q N M hm scale K eps j₀ (rate F tk E))
          (fun k => Regular Q N M (macroAt Q N M hm j₀ k)) (macroAt Q N M hm j₀) (macroClock hm) := by
  let C : ℝ := ((n + 3 : ℕ) : ℝ)
  let c := eps * γ / 4
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := div_pos (mul_pos heps hγ) (by norm_num)
  have hcscale : c ≤ eps * γ / 2 := by dsimp [c]; nlinarith [mul_pos heps hγ]
  obtain ⟨Jpoly, hpoly⟩ := uniform_polynomial_budget n (alignmentCoefficient_pos n B eps).le
  obtain ⟨Jboot, hboot⟩ := uniform_bootstrap_threshold hhm hc hC.le heps hB
  let J := max Jpoly (max Jboot 1)
  refine ⟨J, ?_⟩
  intro Q N M scale K b j₀ hj₀ F tk E hE horder hweights hdata
  let jIndex := macroAt Q N M hm j₀
  let w := weight Q N M hm scale K eps j₀ (rate F tk E)
  let reg := fun k => Regular Q N M (jIndex k)
  have hmacro (k : ℕ) : J ≤ jIndex k := hj₀.trans (macroAt_mem Q N M hm j₀ k).1
  have hmacro1 (k : ℕ) : 1 ≤ jIndex k := (le_max_right _ _).trans ((le_max_right _ _).trans (hmacro k))
  have hbudgets (k : ℕ) :
      (2 : ℝ) ≤ (1 + (jIndex k : ℝ)) ^ C ∧
      (n + 1 : ℝ) * (alignmentCoefficient n B eps * (jIndex k : ℝ) + 1) ^ (n + 1) ≤ (1 + (jIndex k : ℝ)) ^ C ∧
      (n : ℝ) ^ 2 * alignmentCoefficient n B eps * (jIndex k : ℝ) ≤ (1 + (jIndex k : ℝ)) ^ C := by
    have h := (hpoly (jIndex k) ((le_max_left _ _).trans (hmacro k))).2
    simpa only [C, Real.rpow_natCast] using h
  have hbootstrap (k : ℕ) :
      (1 + (jIndex (k + 1) : ℝ)) ^ C * Real.exp (-c * Real.sqrt (macroClock hm (jIndex (k + 1))) / (jIndex (k + 1) : ℝ) ^ 2) ≤ 1 / 2 ∧
      (1 + (jIndex (k + 1) : ℝ)) ^ C * Real.exp (-c * Real.sqrt (macroClock hm (jIndex (k + 1))) / (jIndex (k + 1) : ℝ) ^ 2) ≤
        eps / (64 * B * (jIndex k : ℝ) ^ 2) := by
    have hb' := hboot (jIndex (k + 1)) ((le_max_left _ _).trans ((le_max_right _ _).trans (hmacro (k + 1))))
    have hjm : jIndex k ≤ jIndex (k + 1) := by
      rcases macroAt_succ_eq_or Q N M hm j₀ k with h | h <;> dsimp [jIndex] <;> omega
    have hjmR : (jIndex k : ℝ) ≤ jIndex (k + 1) := by exact_mod_cast hjm
    have hjpos : 0 < (jIndex k : ℝ) := by
      exact_mod_cast (show 0 < jIndex k by have := hmacro1 k; omega)
    have hsq := pow_le_pow_left₀ (show (0 : ℝ) ≤ (jIndex k : ℝ) from Nat.cast_nonneg _) hjmR 2
    have hfrac : eps / (64 * B * (jIndex (k + 1) : ℝ) ^ 2) ≤ eps / (64 * B * (jIndex k : ℝ) ^ 2) :=
      div_le_div_of_nonneg_left heps.le (by positivity) (mul_le_mul_of_nonneg_left hsq (by positivity))
    exact ⟨hb'.2.1, hb'.2.2.trans hfrac⟩
  have hD (k : ℕ) : IsUnit (diagonal F tk E k) := by
    rw [diagonal_eq_endpointDiagonal hE]
    exact endpointDiagonal_isUnit _ _
  apply alignmentRuns_of_uniform_finite E (diagonal F tk E) w reg jIndex (macroClock hm) C c hC hc hD
  apply finite_alignment_of_local_extension E (diagonal F tk E) w reg jIndex (macroClock hm) C c
  · intro k _
    exact identity_changeAt_of_singularFrames hE w jIndex (macroClock hm) C c k (hbudgets k).1
  · intro k hk hk' next hnext
    obtain ⟨hq, hμ, hν, htime⟩ := hdata k hk hk'
    exact local_alignment_extension Q N M hm scale K eps b j₀ hE horder hweights k hk hk' hB heps hcscale
      hq (hmacro1 k) hμ hν (hbudgets k).2.1 (hbudgets k).2.2 htime (hbootstrap k) next hnext

end Yau.Blueprint.Alignment.Y03Proof
