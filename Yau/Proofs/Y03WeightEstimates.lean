import Yau.Proofs.Y03WeightAssembly

/-! Assemble every clause of the literal propagated-weight estimates. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem weightEstimates_of_uniform_rate_bounds (Q : ℕ → ℝ) (N : ℕ) (M hm : ℝ)
    (_hhm : 0 < hm) (scale K eps b c : ℝ) (j₀ : ℕ) (μ : ℕ → Fin n → ℝ)
    (hscale : 0 < scale) (hK : 0 ≤ K) (heps : 0 ≤ eps) (hb : 0 < b) (hc : 0 < c)
    (hsmall : (n : ℝ) * eps ≤ 0.1) (heps' : eps ≤ 0.9)
    (hKb : 2 ≤ K * b) (hscaleLower : 2 ≤ scale * b * c)
    (hmono : ∀ i, Monotone (fun k => μ k i))
    (hQ : ∀ j, j₀ ≤ j → c ≤ Q j)
    (hθ : ∀ j, j₀ ≤ j → theta Q j ≤ b * Q j / 2)
    (hratio : ∀ j, j₀ ≤ j → K / ((j + 1 : ℕ) : ℝ) ^ 2 ≤ 1)
    (hμ : ∀ k i, Regular Q N M (macroAt Q N M hm j₀ k) →
      b * Q (macroAt Q N M hm j₀ k) ≤ μ k i ∧
        μ k i ≤ b⁻¹ * Q (macroAt Q N M hm j₀ k)) :
    WeightEstimates Q N M hm scale K eps b j₀ μ := by
  let J := macroAt Q N M hm j₀
  let w := weight Q N M hm scale K eps j₀ μ
  have hJ (k : ℕ) : j₀ ≤ J k := (macroAt_mem Q N M hm j₀ k).1
  have hQpos (k : ℕ) : 0 < Q (J k) := hc.trans_le (hQ _ (hJ k))
  have hθpos (k : ℕ) : 0 ≤ theta Q (J k) := div_nonneg (hQpos k).le (sq_nonneg _)
  have hlam (k : ℕ) : 0 < multiplier scale K (J k) := multiplier_pos hscale hK _
  have hbounds (k : ℕ) (i : Fin n) :
      multiplier scale K (J k) * (μ k i - theta Q (J k)) ≤ w k i ∧
        w k i ≤ multiplier scale K (J k) * (μ k i - 0.9 * theta Q (J k)) := by
    have hbnd := propagatedWeight_bounds (pieces Q N M hm (J k)) μ
      (offset Q N M hm j₀ (J k)) (hlam k).le heps (hθpos k) hsmall hmono
      (slotAt Q N M hm j₀ k, i)
    simpa only [J, w, weight, offset_add_slotAt] using hbnd
  have hone (k : ℕ) (i : Fin n) (hreg : Regular Q N M (J k)) : 1 ≤ w k i := by
    have hl := (hμ k i hreg).1
    have htheta := hθ _ (hJ k)
    have hq := hQ _ (hJ k)
    have hmuth : b * c / 2 ≤ μ k i - theta Q (J k) := by nlinarith
    have hfactor : 0 ≤ μ k i - theta Q (J k) := (by positivity : 0 ≤ b * c / 2).trans hmuth
    calc
      1 ≤ scale * (b * c / 2) := by nlinarith
      _ ≤ scale * (μ k i - theta Q (J k)) := mul_le_mul_of_nonneg_left hmuth hscale.le
      _ ≤ multiplier scale K (J k) * (μ k i - theta Q (J k)) :=
        mul_le_mul_of_nonneg_right (scale_le_multiplier hscale.le hK _) hfactor
      _ ≤ w k i := (hbounds k i).1
  refine ⟨?_, ?_, ?_, multiplier_bounded hscale.le hK⟩
  · intro k i hreg
    exact ⟨(hμ k i hreg).1, (hμ k i hreg).2, hone k i hreg, hbounds k i⟩
  · intro k i l hreg hreg' hpass
    rcases macroAt_succ_eq_or Q N M hm j₀ k with hsame | hnext
    · exact weight_passage_same_macro Q N M hm scale K eps j₀ μ k i l hsame hpass
    · have hnew : b * Q (J k + 1) ≤ μ (k + 1) i := by
        simpa only [J, hnext] using (hμ (k + 1) i hreg').1
      apply cross_macro_weight_passage (hlam k).le hK
        ((hc.trans_le (hQ (J k + 1) (by have := hJ k; omega))).le)
        (hθpos k) heps' hKb (hratio _ (hJ k)) hnew hpass (hbounds k l).2
      simpa only [J, hnext] using (hbounds (k + 1) i).1
  · intro k i β _ hdegree hweight
    exact forbidden_nonlinear_gap (hlam k) (hθpos k)
      (fun l => (hbounds k l).1) (fun l => (hbounds k l).2) i β hdegree hweight

end Yau.Blueprint.Alignment.Y03Proof
