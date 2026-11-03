import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Uniform simultaneous bounds for the three actual radial jet recurrences.
The envelope precedes the sequences, and the lower-order remainder need not
be monotone in its numerical bound. -/

noncomputable section

namespace Yau.Proofs.C04Aux

theorem radial_jet_order_bound
    (R lam B : ℝ) (hR : 0 ≤ R) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (hsmall : lam * R ^ 2 ≤ (1 / 2 : ℝ))
    (Q : ℕ → ℝ → ℝ) (hQ : ∀ m L, 1 ≤ L → 0 ≤ Q m L) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a w f : ℕ → ℝ,
      (∀ k, 0 ≤ a k ∧ 0 ≤ w k ∧ 0 ≤ f k) →
      a 0 ≤ B → w 0 ≤ B → f 0 ≤ B →
      (∀ k, 1 ≤ k → w k ≤ R * f k + (k : ℝ) * f (k - 1)) →
      (∀ k, 1 ≤ k → a k ≤ R * w k + (k : ℝ) * w (k - 1)) →
      (∀ k, 1 ≤ k → ∀ L : ℝ, 1 ≤ L →
        (∀ j, j < k → a j ≤ L ∧ w j ≤ L ∧ f j ≤ L) →
        f k ≤ lam * a k + Q k L) →
      a m ≤ C ∧ w m ≤ C ∧ f m ≤ C := by
  induction m using Nat.strong_induction_on with
  | h m IH =>
    by_cases hm : m = 0
    · subst m
      refine ⟨1 + B, by positivity, ?_⟩
      intro a w f hnonneg ha0 hw0 hf0 hw ha hf
      exact ⟨by linarith, by linarith, by linarith⟩
    · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      choose P hPpos hPbound using fun k : Fin m => IH k k.isLt
      let L : ℝ := 1 + ∑ k : Fin m, P k
      have hsum : 0 ≤ ∑ k : Fin m, P k :=
        Finset.sum_nonneg fun k hk => (hPpos k).le
      have hL : 1 ≤ L := by dsimp [L]; linarith
      have hL0 : 0 ≤ L := zero_le_one.trans hL
      have hPL (k : Fin m) : P k ≤ L := by
        have hh : P k ≤ ∑ j : Fin m, P j :=
          Finset.single_le_sum (fun j hj => (hPpos j).le) (Finset.mem_univ k)
        dsimp [L]
        linarith
      let q := Q m L
      let A := 2 * (R ^ 2 * q + (m : ℝ) * (R + 1) * L)
      let F := lam * A + q
      let W := R * F + (m : ℝ) * L
      have hq : 0 ≤ q := hQ m L hL
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hF : 0 ≤ F := by dsimp [F]; positivity
      have hW : 0 ≤ W := by dsimp [W]; positivity
      refine ⟨1 + L + A + F + W, by positivity, ?_⟩
      intro a w f hnonneg ha0 hw0 hf0 hw ha hf
      have hprev (k : ℕ) (hk : k < m) : a k ≤ L ∧ w k ≤ L ∧ f k ≤ L := by
        obtain ⟨h₁, h₂, h₃⟩ :=
          hPbound ⟨k, hk⟩ a w f hnonneg ha0 hw0 hf0 hw ha hf
        exact ⟨h₁.trans (hPL ⟨k, hk⟩), h₂.trans (hPL ⟨k, hk⟩),
          h₃.trans (hPL ⟨k, hk⟩)⟩
      have hpred : m - 1 < m := Nat.sub_lt (by omega) (by omega)
      have hw' : w m ≤ R * f m + (m : ℝ) * L :=
        (hw m hmpos).trans (by gcongr; exact (hprev (m - 1) hpred).2.2)
      have ha' : a m ≤ R * w m + (m : ℝ) * L :=
        (ha m hmpos).trans (by gcongr; exact (hprev (m - 1) hpred).2.1)
      have hf' : f m ≤ lam * a m + q := hf m hmpos L hL hprev
      have hcombine : a m ≤ R ^ 2 * f m + (m : ℝ) * (R + 1) * L := by
        calc
          a m ≤ R * (R * f m + (m : ℝ) * L) + (m : ℝ) * L :=
            ha'.trans (by gcongr)
          _ = R ^ 2 * f m + (m : ℝ) * (R + 1) * L := by ring
      have habsorb : a m ≤ lam * R ^ 2 * a m + R ^ 2 * q +
          (m : ℝ) * (R + 1) * L := by
        calc
          a m ≤ R ^ 2 * (lam * a m + q) + (m : ℝ) * (R + 1) * L :=
            hcombine.trans (by gcongr)
          _ = lam * R ^ 2 * a m + R ^ 2 * q + (m : ℝ) * (R + 1) * L := by ring
      have hhalf : lam * R ^ 2 * a m ≤ (1 / 2 : ℝ) * a m :=
        mul_le_mul_of_nonneg_right hsmall (hnonneg m).1
      have haA : a m ≤ A := by dsimp [A]; linarith
      have hfF : f m ≤ F :=
        hf'.trans (by dsimp [F]; exact add_le_add (mul_le_mul_of_nonneg_left haA hlam) le_rfl)
      have hwW : w m ≤ W :=
        hw'.trans (by dsimp [W]; exact add_le_add (mul_le_mul_of_nonneg_left hfF hR) le_rfl)
      exact ⟨haA.trans (by linarith), hwW.trans (by linarith), hfF.trans (by linarith)⟩

theorem exists_uniform_radial_jet_envelope
    (R lam B : ℝ) (hR : 0 ≤ R) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (hsmall : lam * R ^ 2 ≤ (1 / 2 : ℝ))
    (Q : ℕ → ℝ → ℝ) (hQ : ∀ m L, 1 ≤ L → 0 ≤ Q m L) :
    ∃ J : ℕ → ℝ, (∀ m, 0 < J m) ∧
      ∀ a w f : ℕ → ℝ,
        (∀ m, 0 ≤ a m ∧ 0 ≤ w m ∧ 0 ≤ f m) →
        a 0 ≤ B → w 0 ≤ B → f 0 ≤ B →
        (∀ m, 1 ≤ m → w m ≤ R * f m + (m : ℝ) * f (m - 1)) →
        (∀ m, 1 ≤ m → a m ≤ R * w m + (m : ℝ) * w (m - 1)) →
        (∀ m, 1 ≤ m → ∀ L : ℝ, 1 ≤ L →
          (∀ k, k < m → a k ≤ L ∧ w k ≤ L ∧ f k ≤ L) →
          f m ≤ lam * a m + Q m L) →
        ∀ m, a m ≤ J m ∧ w m ≤ J m ∧ f m ≤ J m := by
  choose J hJpos hJbound using fun m => radial_jet_order_bound R lam B hR hlam hB hsmall Q hQ m
  exact ⟨J, hJpos, fun a w f hnonneg ha0 hw0 hf0 hw ha hf m =>
    hJbound m a w f hnonneg ha0 hw0 hf0 hw ha hf⟩

end Yau.Proofs.C04Aux
