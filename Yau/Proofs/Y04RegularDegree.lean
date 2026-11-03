import Yau.Proofs.Y04PolynomialDegree
import Yau.Proofs.Y04BadCharging
import Yau.Proofs.Y03Weights

/-! Actual regular model transport and the late reset lower weight. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Blueprint.Alignment.Y04Proof

open Yau Y03Proof

theorem multiplier_monotone {scale K : ℝ} (hscale : 0 < scale) (hK : 0 ≤ K) :
    Monotone (multiplier scale K) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [multiplier_succ]
  have hl := (multiplier_pos hscale hK j).le
  have hf : 0 ≤ K / ((j+1:ℕ):ℝ)^2 := by positivity
  nlinarith

theorem exists_reset_index {M b₀ : ℝ} (hb₀ : 0 < b₀) :
    ∃ Jreset : ℕ, 1 ≤ Jreset ∧ ∀ j, Jreset ≤ j →
      2*Real.exp M ≤ b₀*(j:ℝ)^2 := by
  obtain ⟨J, hJ⟩ := exists_nat_gt (max 1 (2*Real.exp M/b₀))
  have hJone : (1:ℝ) < J := (le_max_left _ _).trans_lt hJ
  refine ⟨J, by exact_mod_cast hJone.le, ?_⟩
  intro j hj
  have hJj : (J:ℝ) ≤ j := by exact_mod_cast hj
  have hpos : (1:ℝ) ≤ j := hJone.le.trans hJj
  have hbound : 2*Real.exp M < (j:ℝ)*b₀ :=
    (div_lt_iff₀ hb₀).mp (((le_max_right _ _).trans_lt hJ).trans_le hJj)
  have hsq : (j:ℝ) ≤ (j:ℝ)^2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hsq hb₀.le
  nlinarith

theorem macroAt_offset_add {Q : ℕ → ℝ} {N j₀ j r : ℕ} {M hm : ℝ}
    (hj : j₀ ≤ j) (hr : r < pieces Q N M hm j) :
    macroAt Q N M hm j₀ (offset Q N M hm j₀ j+r) = j := by
  apply (macroAt_eq_iff Q N M hm).mpr
  refine ⟨hj, by omega, ?_⟩
  rw [offset_succ Q N M hm hj]
  omega

theorem regular_step_component_degree
    {n : ℕ} {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ}
    {Q : ℕ → ℝ} {N j₀ Dstar k : ℕ} {M hm scale K eps b : ℝ}
    {E : Frames n} {L : Changes n} {H G Ginv g : ℕ → PolyMap n}
    (hweights : WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E))
    (hcompat : RegularModelCompatibility F tk Q N M hm scale K eps j₀ Dstar E L H G Ginv g)
    (hk : Regular Q N M (macroAt Q N M hm j₀ k))
    (hP : ∀ i, (((forwardComp G k) i).totalDegree:ℝ) ≤
      weight Q N M hm scale K eps j₀ (rate F tk E) k i) :
    ∀ i, (((forwardComp G (k+1)) i).totalDegree:ℝ) ≤
      if Regular Q N M (macroAt Q N M hm j₀ (k+1)) then
        weight Q N M hm scale K eps j₀ (rate F tk E) (k+1) i else
        weight Q N M hm scale K eps j₀ (rate F tk E) k i := by
  have hg := hcompat.2.2.2.2.2 k hk
  have hnonlin := allowed_comp_component_degree
    (fun i => (zero_le_one.trans (hweights.1 k i hk).2.2.1))
    hg.2.1 hg.2.2.1 hg.2.2.2.1 hP
  change ∀ i, (((G k).comp (forwardComp G k) i).totalDegree:ℝ) ≤ _
  rw [hg.1, Yau.Proofs.Y02Aux.comp_assoc]
  by_cases hn : Regular Q N M (macroAt Q N M hm j₀ (k+1))
  · simp only [if_pos hn]
    obtain ⟨C, c, hC, hc, hchanges⟩ := hcompat.2.2.1
    exact linear_comp_component_degree
      (fun i => zero_le_one.trans (hweights.1 (k+1) i hn).2.2.1)
      ((hchanges k hk).2 hn) hnonlin
  · simp only [if_neg hn, linearPolynomial_one, Yau.Proofs.Y02Aux.id_comp]
    exact hnonlin

theorem regular_weight_upper
    {n : ℕ} {Q : ℕ → ℝ} {N j₀ j k : ℕ} {M hm scale K eps b b₀ : ℝ}
    {μ : ℕ → Fin n → ℝ}
    (hscale : 0 < scale) (hK : 0 ≤ K) (hQ : 0 ≤ Q j)
    (hmacro : macroAt Q N M hm j₀ k = j) (hreg : Regular Q N M j)
    (hwindow : WindowRateBounds Q N M hm b₀ j₀ μ)
    (hweights : WeightEstimates Q N M hm scale K eps b j₀ μ) :
    ∀ i, weight Q N M hm scale K eps j₀ μ k i ≤ multiplier scale K j * Q (j+1) := by
  intro i
  have hk : Regular Q N M (macroAt Q N M hm j₀ k) := hmacro ▸ hreg
  have hupper := (hweights.1 k i hk).2.2.2.2
  have hrate := (hwindow k i hk).2
  rw [hmacro] at hupper hrate
  have htheta : 0 ≤ theta Q j := div_nonneg hQ (sq_nonneg _)
  have hlam := (multiplier_pos hscale hK j).le
  exact hupper.trans (mul_le_mul_of_nonneg_left (by linarith) hlam)

theorem reset_weight_lower
    {n : ℕ} {Q : ℕ → ℝ} {N jBound j₀ v Dstar : ℕ} {M hm scale K eps b b₀ : ℝ}
    {μ : ℕ → Fin n → ℝ}
    (hscale : 0 < scale) (hK : 0 ≤ K) (hb₀ : 0 < b₀)
    (hstart : jBound+N ≤ j₀) (hv : j₀ ≤ v) (hvpos : 1 ≤ v)
    (hreg : Regular Q N M v)
    (hreset : 2*Real.exp M ≤ b₀*(v:ℝ)^2)
    (hcharge : BadCharging Q jBound N Dstar M hm b₀)
    (hwindow : WindowRateBounds Q N M hm b₀ j₀ μ)
    (hweights : WeightEstimates Q N M hm scale K eps b j₀ μ) :
    ∀ i, multiplier scale K v * (b₀/2) * Q (v-N) ≤
      weight Q N M hm scale K eps j₀ μ (offset Q N M hm j₀ v) i := by
  intro i
  have hleft : jBound ≤ v-N := by omega
  have htail : jBound ≤ v := by omega
  have hQleft := hcharge.2.1 (v-N) hleft
  have hQnext := hcharge.2.1 (v+1) (by omega)
  have hQv := hcharge.2.1 v htail
  have hgrowth := regular_growth_bound hreg (by omega : N ≤ v) hQleft hQnext
  have hmono := hcharge.1 htail (show jBound ≤ v+1 by omega) (show v ≤ v+1 by omega)
  have hsq : 0 < (v:ℝ)^2 := by positivity
  have htheta : theta Q v ≤ (b₀/2)*Q (v-N) := by
    unfold theta
    apply (div_le_iff₀ hsq).mpr
    have := mul_le_mul_of_nonneg_right hreset hQleft.le
    nlinarith
  have hmacro := macroAt_offset Q N M hm hv
  have hk : Regular Q N M (macroAt Q N M hm j₀ (offset Q N M hm j₀ v)) := by
    rw [hmacro]
    exact hreg
  have hraw := (hweights.1 _ i hk).2.2.2.1
  have hrate := (hwindow _ i hk).1
  rw [hmacro] at hraw hrate
  have hlam := (multiplier_pos hscale hK v).le
  calc
    _ = multiplier scale K v * ((b₀/2)*Q (v-N)) := by ring
    _ ≤ multiplier scale K v * (μ (offset Q N M hm j₀ v) i - theta Q v) :=
      mul_le_mul_of_nonneg_left (by linarith) hlam
    _ ≤ _ := hraw

end Yau.Blueprint.Alignment.Y04Proof
