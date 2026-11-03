import Yau.Proofs.Y04RegularDegree

/-! One macro induction for the same accumulated polynomial maps. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y04Proof

open Yau Y03Proof

theorem regular_macro_propagation
    {n : ℕ} {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ}
    {Q : ℕ → ℝ} {N j₀ j Dstar : ℕ} {M hm scale K eps b b₀ : ℝ}
    {E : Frames n} {L : Changes n} {H G Ginv g : ℕ → PolyMap n}
    (hscale : 0 < scale) (hK : 0 ≤ K) (hj : j₀ ≤ j)
    (hreg : Regular Q N M j) (hQ : 0 ≤ Q j) (hQnext : 0 ≤ Q (j+1))
    (hwindow : WindowRateBounds Q N M hm b₀ j₀ (rate F tk E))
    (hweights : WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E))
    (hcompat : RegularModelCompatibility F tk Q N M hm scale K eps j₀ Dstar E L H G Ginv g)
    (hP : ∀ i, (((forwardComp G (offset Q N M hm j₀ j)) i).totalDegree:ℝ) ≤
      weight Q N M hm scale K eps j₀ (rate F tk E) (offset Q N M hm j₀ j) i) :
    (Regular Q N M (j+1) → ∀ i,
      (((forwardComp G (offset Q N M hm j₀ (j+1))) i).totalDegree:ℝ) ≤
      weight Q N M hm scale K eps j₀ (rate F tk E) (offset Q N M hm j₀ (j+1)) i) ∧
    (Bad Q N M (j+1) →
      ((forwardComp G (offset Q N M hm j₀ (j+1))).degree:ℝ) ≤
        multiplier scale K j * Q (j+1)) := by
  let p := pieces Q N M hm j
  let off := offset Q N M hm j₀ j
  have hp : 1 ≤ p := one_le_pieces Q N M hm j
  have hinside : ∀ r, r < p → ∀ i,
      (((forwardComp G (off+r)) i).totalDegree:ℝ) ≤
      weight Q N M hm scale K eps j₀ (rate F tk E) (off+r) i := by
    intro r
    induction r with
    | zero => intro hr; simpa [off] using hP
    | succ r ih =>
      intro hr
      have hrp : r < p := by omega
      have hcur : Regular Q N M (macroAt Q N M hm j₀ (off+r)) := by
        rw [macroAt_offset_add hj hrp]
        exact hreg
      have hnext : Regular Q N M (macroAt Q N M hm j₀ ((off+r)+1)) := by
        rw [show (off+r)+1 = off+(r+1) by omega, macroAt_offset_add hj hr]
        exact hreg
      have hs := regular_step_component_degree hweights hcompat hcur (ih hrp)
      simpa only [if_pos hnext, Nat.add_assoc] using hs
  let k := off+(p-1)
  have hk : Regular Q N M (macroAt Q N M hm j₀ k) := by
    rw [macroAt_offset_add hj (show p-1 < p by omega)]
    exact hreg
  have hk1 : k+1 = offset Q N M hm j₀ (j+1) := by
    rw [offset_succ Q N M hm hj]
    dsimp [k, off, p]
    omega
  have hmacro1 : macroAt Q N M hm j₀ (k+1) = j+1 := by
    rw [hk1, macroAt_offset Q N M hm (by omega : j₀ ≤ j+1)]
  have hs := regular_step_component_degree hweights hcompat hk (hinside (p-1) (by omega))
  constructor
  · intro hnext i
    have hnext' : Regular Q N M (macroAt Q N M hm j₀ (k+1)) := hmacro1 ▸ hnext
    simpa only [if_pos hnext', hk1] using hs i
  · intro hbad
    have hnext' : ¬ Regular Q N M (macroAt Q N M hm j₀ (k+1)) := by
      rw [hmacro1]
      exact fun h => h hbad
    have hupper := regular_weight_upper hscale hK hQ
      (macroAt_offset_add hj (show p-1 < p by omega)) hreg hwindow hweights
    apply degree_le_of_component_degree (mul_nonneg (multiplier_pos hscale hK j).le hQnext)
    intro i
    have hsi := hs i
    simp only [if_neg hnext', hk1] at hsi
    exact hsi.trans (hupper i)

theorem macro_degree_bound
    {n : ℕ}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ}
    {Q : ℕ → ℝ} {N jBound j₀ Dstar : ℕ}
    {M hm scale K eps b b₀ : ℝ}
    {E : Frames n} {L : Changes n}
    {H G Ginv g : ℕ → PolyMap n}
    (hN : 1 ≤ N) (hD : 1 ≤ Dstar) (hM : 0 < M)
    (hhm : 0 < hm) (hscale : 0 < scale) (hK : 0 < K) (hb₀ : 0 < b₀)
    (hstart : jBound+N ≤ j₀) (hreg₀ : Regular Q N M j₀)
    (hreset : ∀ j, j₀ ≤ j → 2*Real.exp M ≤ b₀*(j:ℝ)^2)
    (hcharge : BadCharging Q jBound N Dstar M hm b₀)
    (hgrid : GridLayout Q N M hm j₀)
    (hwindow : WindowRateBounds Q N M hm b₀ j₀ (rate F tk E))
    (hweights : WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E))
    (hcompat : RegularModelCompatibility F tk Q N M hm scale K eps
      j₀ Dstar E L H G Ginv g) :
    ∃ B : ℝ, 0 < B ∧ ∀ j, j₀ ≤ j →
      ((forwardComp G (offset Q N M hm j₀ j)).degree : ℝ) ≤ B*Q j := by
  classical
  let w := weight Q N M hm scale K eps j₀ (rate F tk E)
  let κ := offset Q N M hm j₀
  let lam := multiplier scale K
  have hlampos : ∀ j, 0 < lam j := multiplier_pos hscale hK.le
  have hlammono : Monotone lam := multiplier_monotone hscale hK.le
  have hQpos : ∀ j, j₀ ≤ j → 0 < Q j := fun j hj => hcharge.2.1 j (by omega)
  have hinv : ∀ j, j₀ ≤ j →
      (Regular Q N M j → ∀ i, (((forwardComp G (κ j)) i).totalDegree:ℝ) ≤ w (κ j) i) ∧
      (Bad Q N M j → ∃ u, j₀ < u ∧ u ≤ j ∧ Regular Q N M (u-1) ∧
        (∀ r, u ≤ r → r ≤ j → Bad Q N M r) ∧
        ((forwardComp G (κ j)).degree:ℝ) ≤ (Dstar:ℝ)^(j-u)*lam (u-1)*Q u) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      constructor
      · intro _ i
        have hmacro : macroAt Q N M hm j₀ 0 = j₀ := by
          simpa only [offset_self] using macroAt_offset Q N M hm (le_refl j₀)
        have hregat : Regular Q N M (macroAt Q N M hm j₀ 0) := by rw [hmacro]; exact hreg₀
        have h := (hweights.1 0 i hregat).2.2.1
        simpa [κ, offset_self, forwardComp, PolyMap.id] using h
      · intro hbad; exact False.elim (hreg₀ hbad)
    | succ j hj ih =>
      by_cases hregj : Regular Q N M j
      · obtain ⟨hregular, hbad⟩ := regular_macro_propagation hscale hK.le hj hregj
          (hQpos j hj).le (hQpos (j+1) (by omega)).le hwindow hweights hcompat (ih.1 hregj)
        refine ⟨hregular, ?_⟩
        intro hbnext
        refine ⟨j+1, by omega, le_rfl, ?_, ?_, ?_⟩
        · simpa using hregj
        · intro r hr hrj
          have : r = j+1 := by omega
          simpa [this] using hbnext
        · simpa [κ, lam] using hbad hbnext
      · have hbcur : Bad Q N M j := Classical.not_not.mp hregj
        obtain ⟨u, hu₀, huj, huleft, hubad, hdegree⟩ := ih.2 hbcur
        have hpieces : pieces Q N M hm j = 1 := if_pos hbcur
        have hoff : κ (j+1) = κ j+1 := by
          exact (offset_succ Q N M hm hj).trans (by rw [hpieces])
        have hcomp : ((forwardComp G (κ (j+1))).degree:ℝ) ≤
            (Dstar:ℝ) * ((forwardComp G (κ j)).degree:ℝ) := by
          rw [hoff, forwardComp]
          exact_mod_cast (Yau.Proofs.Y02Aux.comp_degree_le (G (κ j)) (forwardComp G (κ j))).trans
            (Nat.mul_le_mul_right _ (hcompat.2.2.2.2.1 (κ j)).1)
        have hDnonneg : 0 ≤ (Dstar:ℝ) := by positivity
        have hdegree' : ((forwardComp G (κ (j+1))).degree:ℝ) ≤
            (Dstar:ℝ)^(j+1-u)*lam (u-1)*Q u := by
          calc
            _ ≤ (Dstar:ℝ)*((Dstar:ℝ)^(j-u)*lam (u-1)*Q u) :=
              hcomp.trans (mul_le_mul_of_nonneg_left hdegree hDnonneg)
            _ = _ := by rw [show j+1-u = (j-u)+1 by omega, pow_succ]; ring
        constructor
        · intro hregnext i
          have hc : FullBadComponent Q N M u (j+1) :=
            ⟨by omega, Or.inr huleft, hregnext, fun r hr hrj => hubad r hr (by omega)⟩
          have hcost := (hcharge.2.2.1 u (j+1) (by omega) hc).2
          have hQleft := hcharge.2.1 (j+1-N) (by omega)
          have hresetlower := reset_weight_lower hscale hK.le hb₀ hstart (by omega : j₀ ≤ j+1)
            (by omega : 1 ≤ j+1) hregnext (hreset (j+1) (by omega)) hcharge hwindow hweights i
          have hcomponent : (((forwardComp G (κ (j+1))) i).totalDegree:ℝ) ≤
              ((forwardComp G (κ (j+1))).degree:ℝ) := by
            exact_mod_cast Yau.Proofs.Y02Aux.component_degree_le (forwardComp G (κ (j+1))) i
          apply hcomponent.trans (hdegree'.trans (le_trans ?_ hresetlower))
          calc
            _ = lam (u-1) * ((Dstar:ℝ)^(j+1-u)*Q u) := by ring
            _ ≤ lam (u-1) * ((b₀/2)*Q (j+1-N)) := mul_le_mul_of_nonneg_left hcost (hlampos _).le
            _ ≤ lam (j+1) * ((b₀/2)*Q (j+1-N)) :=
              mul_le_mul_of_nonneg_right (hlammono (by omega)) (by positivity)
            _ = _ := by ring
        · intro hbnext
          refine ⟨u, hu₀, by omega, huleft, ?_, hdegree'⟩
          intro r hr hrj
          by_cases hrprev : r ≤ j
          · exact hubad r hr hrprev
          · have : r = j+1 := by omega
            simpa [this] using hbnext
  obtain ⟨Λ, hΛ⟩ := multiplier_bounded hscale.le hK.le
  have hΛpos : 0 < Λ := (hlampos 0).trans_le (hΛ 0)
  let C := max (Real.exp M) ((Dstar:ℝ)^(2*N+1))
  have hCpos : 0 < C := (Real.exp_pos M).trans_le (le_max_left _ _)
  refine ⟨Λ*C, mul_pos hΛpos hCpos, ?_⟩
  intro j hj
  by_cases hregj : Regular Q N M j
  · have hweightsupper := regular_weight_upper hscale hK.le (hQpos j hj).le
      (macroAt_offset Q N M hm hj) hregj hwindow hweights
    have hdeg := degree_le_of_component_degree
      (mul_nonneg (hlampos j).le (hQpos (j+1) (by omega)).le)
      (fun i => (hinv j hj).1 hregj i |>.trans (hweightsupper i))
    have hcomp := (regular_local_comparability hregj (by omega : N ≤ j)
      (by omega : jBound ≤ j-N) hcharge.1 hcharge.2.1).2
    calc
      _ ≤ lam j*Q (j+1) := hdeg
      _ ≤ Λ*Q (j+1) := mul_le_mul_of_nonneg_right (hΛ j) (hQpos (j+1) (by omega)).le
      _ ≤ Λ*(Real.exp M*Q j) := mul_le_mul_of_nonneg_left hcomp hΛpos.le
      _ ≤ (Λ*C)*Q j := by
        have := mul_le_mul_of_nonneg_right (le_max_left (Real.exp M) ((Dstar:ℝ)^(2*N+1))) (hQpos j hj).le
        have := mul_le_mul_of_nonneg_left this hΛpos.le
        nlinarith
  · have hbcur : Bad Q N M j := Classical.not_not.mp hregj
    obtain ⟨u, hu₀, huj, huleft, hubad, hdegree⟩ := (hinv j hj).2 hbcur
    have hprefix := (hcharge.2.2.2.1 u j (by omega) huj (Or.inr huleft)
      (fun r hr hrj => hubad r hr (by omega))).2
    calc
      _ ≤ (Dstar:ℝ)^(j-u)*lam (u-1)*Q u := hdegree
      _ = lam (u-1)*((Dstar:ℝ)^(j-u)*Q u) := by ring
      _ ≤ lam (u-1)*((Dstar:ℝ)^(2*N+1)*Q j) := mul_le_mul_of_nonneg_left hprefix (hlampos _).le
      _ ≤ Λ*((Dstar:ℝ)^(2*N+1)*Q j) := mul_le_mul_of_nonneg_right (hΛ _)
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (hQpos j hj).le)
      _ ≤ (Λ*C)*Q j := by
        have := mul_le_mul_of_nonneg_right (le_max_right (Real.exp M) ((Dstar:ℝ)^(2*N+1))) (hQpos j hj).le
        have := mul_le_mul_of_nonneg_left this hΛpos.le
        nlinarith

end Yau.Blueprint.Alignment.Y04Proof
