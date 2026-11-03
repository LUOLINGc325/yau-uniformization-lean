import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-! Coarse uniform composition budgets on the same open source domain. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

def pullbackModelFiniteJetBound (B : ℕ → ℝ) (m : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (m + 1), B j

theorem pullbackModelFiniteJetBound_one_le (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (m : ℕ) :
    1 ≤ pullbackModelFiniteJetBound B m := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j hj => hB j)

theorem pullbackModelFiniteJetBound_le (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    {m j : ℕ} (hj : j ≤ m) : B j ≤ pullbackModelFiniteJetBound B m := by
  have hh : B j ≤ ∑ i ∈ Finset.range (m + 1), B i :=
    Finset.single_le_sum (fun i hi => hB i) (Finset.mem_range.mpr (by omega))
  dsimp [pullbackModelFiniteJetBound]
  linarith

def pullbackModelCompositionJetBudget (P B : ℕ → ℝ) (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * pullbackModelFiniteJetBound B m *
    (pullbackModelFiniteJetBound P m) ^ m

theorem pullbackModelCompositionJetBudget_pos (P B : ℕ → ℝ)
    (hP : ∀ j, 0 ≤ P j) (hB : ∀ j, 0 ≤ B j) (m : ℕ) :
    0 < pullbackModelCompositionJetBudget P B m := by
  have hp : 0 < pullbackModelFiniteJetBound P m :=
    zero_lt_one.trans_le (pullbackModelFiniteJetBound_one_le P hP m)
  have hb : 0 < pullbackModelFiniteJetBound B m :=
    zero_lt_one.trans_le (pullbackModelFiniteJetBound_one_le B hB m)
  dsimp [pullbackModelCompositionJetBudget]
  positivity

variable {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem pullback_model_composition_jet {f : D → E} {g : E → F} {U : Set D} {V : Set E}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (hU : IsOpen U) (hV : IsOpen V)
    (hmap : Set.MapsTo f U V) {x : D} (hx : x ∈ U)
    (P B : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (hB : ∀ j, 0 ≤ B j)
    (hfjet : ∀ j, ‖iteratedFDeriv ℝ j f x‖ ≤ P j)
    (hgjet : ∀ j, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ B j) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (g ∘ f) x‖ ≤ pullbackModelCompositionJetBudget P B m := by
  have hC (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDerivWithin ℝ j g V (f x)‖ ≤ pullbackModelFiniteJetBound B m := by
    rw [iteratedFDerivWithin_of_isOpen j hV (hmap hx)]
    exact (hgjet j).trans (pullbackModelFiniteJetBound_le B hB hj)
  have hD (j : ℕ) (hjpos : 1 ≤ j) (hj : j ≤ m) :
      ‖iteratedFDerivWithin ℝ j f U x‖ ≤ (pullbackModelFiniteJetBound P m) ^ j := by
    rw [iteratedFDerivWithin_of_isOpen j hU hx]
    exact (hfjet j).trans ((pullbackModelFiniteJetBound_le P hP hj).trans
      (le_self_pow₀ (pullbackModelFiniteJetBound_one_le P hP m) (by omega)))
  have hh := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) hg hf
    (by simp : (m : ℕ∞ω) ≤ ∞) hV.uniqueDiffOn hU.uniqueDiffOn hmap hx hC hD
  rw [iteratedFDerivWithin_of_isOpen m hU hx] at hh
  exact hh

end Yau.Proofs.C04Aux
