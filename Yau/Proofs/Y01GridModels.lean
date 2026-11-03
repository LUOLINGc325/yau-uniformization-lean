import Yau.Proofs.Y03GridWindows
import Yau.Proofs.Y03GridLower

/-! The literal canonical grid supplies the macro subdivision and physical
clock clauses of `PolynomialModels`. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Filter Yau.Blueprint Yau.Blueprint.Alignment
open Yau.Blueprint.Alignment.Y03Proof

variable {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm : ℝ}

theorem gridClock_positive (hgrid : GridLayout Q N M hm j₀) (k : ℕ) :
    0 < gridClock Q N M hm j₀ k := by
  have h0 : 0 < gridClock Q N M hm j₀ 0 := by
    rw [hgrid.1]
    exact Real.exp_pos _
  exact h0.trans_le (hgrid.2.1.monotone (Nat.zero_le k))

theorem macroAt_eq_of_clock_window (hhm : 0 < hm) {j k : ℕ}
    (hlo : macroClock hm j ≤ gridClock Q N M hm j₀ k)
    (hhi : gridClock Q N M hm j₀ k < macroClock hm (j + 1)) :
    macroAt Q N M hm j₀ k = j := by
  have hmem := gridClock_mem_Ico Q N M hm hhm j₀ k
  have hmono := (macroClock_strictMono hm hhm).monotone
  apply le_antisymm
  · by_contra hn
    have hj : j + 1 ≤ macroAt Q N M hm j₀ k := by omega
    have := hmono hj
    linarith
  · by_contra hn
    have hj : macroAt Q N M hm j₀ k + 1 ≤ j := by omega
    have := hmono hj
    linarith

theorem canonical_macro_subdivision (hhm : 0 < hm)
    (hgrid : GridLayout Q N M hm j₀) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧
      gridClock Q N M hm j₀ 0 = macroClock hm j₀ ∧
      (∀ j, j₀ ≤ j → ∃ k, gridClock Q N M hm j₀ k = macroClock hm j) ∧
      ∀ j, j₀ ≤ j →
        (∃ k, gridClock Q N M hm j₀ k = macroClock hm j ∧
          gridClock Q N M hm j₀ (k + 1) = macroClock hm (j + 1)) ∨
        (∀ k, macroClock hm j ≤ gridClock Q N M hm j₀ k →
          gridClock Q N M hm j₀ k < macroClock hm (j + 1) →
          c₁ * Real.sqrt (macroClock hm j) ≤
            gridClock Q N M hm j₀ (k + 1) - gridClock Q N M hm j₀ k ∧
          gridClock Q N M hm j₀ (k + 1) - gridClock Q N M hm j₀ k ≤
            C₁ * Real.sqrt (macroClock hm j)) := by
  classical
  obtain ⟨ch, Ch, hch, hCh, hsteps⟩ := hgrid.2.2.2.2.2
  refine ⟨ch, Ch * Real.sqrt (Real.exp hm), hch, hgrid.1, ?_, ?_⟩
  · intro j hj
    exact ⟨offset Q N M hm j₀ j, gridClock_offset Q N M hm hj⟩
  · intro j hj
    by_cases hbad : Bad Q N M j
    · left
      refine ⟨offset Q N M hm j₀ j, gridClock_offset Q N M hm hj, ?_⟩
      have hp : pieces Q N M hm j = 1 := by simp only [pieces, ite_eq_left hbad]
      have ho := offset_succ Q N M hm hj
      rw [hp] at ho
      rw [← ho]
      exact gridClock_offset Q N M hm (by omega)
    · right
      intro k hlo hhi
      have hmacro := macroAt_eq_of_clock_window hhm hlo hhi
      have hk := hsteps k
      have hregular : Regular Q N M (macroAt Q N M hm j₀ k) := by
        simpa only [Regular, hmacro] using hbad
      refine ⟨?_, ?_⟩
      · exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlo) hch.le).trans hk.1
      · have hroot : Real.sqrt (gridClock Q N M hm j₀ k) ≤
            Real.sqrt (Real.exp hm) * Real.sqrt (macroClock hm j) := by
          have h := Real.sqrt_le_sqrt hhi.le
          rw [macroClock_succ, Real.sqrt_mul (Real.exp_pos hm).le] at h
          exact h
        calc
          _ ≤ Ch * Real.sqrt (gridClock Q N M hm j₀ k) := hk.2.2 hregular
          _ ≤ Ch * (Real.sqrt (Real.exp hm) * Real.sqrt (macroClock hm j)) :=
            mul_le_mul_of_nonneg_left hroot hCh.le
          _ = _ := by ring

theorem physical_grid_properties
    {n : ℕ} {X : Yau.KahlerManifold n} {o : Pt X} {h : Flow X} {ρ : STF X}
    {time : ℝ → ℝ} {s₀ : ℝ}
    (hclock : ClockParameter X o h ρ time s₀)
    (hgrid : GridLayout Q N M hm j₀)
    (hdomain : ∀ k, s₀ ≤ gridClock Q N M hm j₀ k) :
    StrictMono (fun k => time (gridClock Q N M hm j₀ k)) ∧
      (∀ k, 0 < time (gridClock Q N M hm j₀ k)) ∧
      (∀ k, ρ o (time (gridClock Q N M hm j₀ k)) = gridClock Q N M hm j₀ k) ∧
      Tendsto (fun k => ρ o (time (gridClock Q N M hm j₀ k))) atTop atTop := by
  have heq : (fun k => ρ o (time (gridClock Q N M hm j₀ k))) =
      gridClock Q N M hm j₀ := funext (fun k => (hclock.2.2.1 _ (hdomain k)).2)
  refine ⟨?_, fun k => (hclock.2.2.1 _ (hdomain k)).1,
    fun k => (hclock.2.2.1 _ (hdomain k)).2, ?_⟩
  · intro i j hij
    exact hclock.2.1 (hdomain i) (hdomain j) (hgrid.2.1 hij)
  · rw [heq]
    exact hgrid.2.2.1

end Yau.Proofs.Y01Aux
