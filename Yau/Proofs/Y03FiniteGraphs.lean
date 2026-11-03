import Yau.Proofs.Y03CoordinateGraphStep

/-! A whole finite nested graph flag with a norm bound linear in its number of levels. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem exists_finite_nested_graphs {m : ℕ} (s : ℕ → Finset (Fin n))
    (A : ℕ → Submodule ℂ (ComplexVector n)) {B C : ℝ} (hC : 0 ≤ C)
    (hs : ∀ r, r < m → s r ⊆ s (r + 1)) (hA : ∀ r, r < m → A r ≤ A (r + 1))
    (hprojection : ∀ r, r < m → ∀ a : A r, ‖a‖ ≤ C * ‖coordinateProjectionOnto (s r) a‖)
    (base : CoordinateGraph (s m) (A m) B) :
    ∃ G : (r : Fin (m + 1)) → CoordinateGraph (s r.val) (A r.val) (B + ((m - r.val : ℕ) : ℝ) * C),
      ∀ r : Fin m, LinearMap.range (G r.castSucc).lift.toLinearMap ≤
        LinearMap.range (G r.succ).lift.toLinearMap := by
  let State := fun r : Fin (m + 1) => CoordinateGraph (s r.val) (A r.val) (B + ((m - r.val : ℕ) : ℝ) * C)
  have hstep (r : Fin m) (next : State r.succ) :
      ∃ current : State r.castSucc, LinearMap.range current.lift.toLinearMap ≤
        LinearMap.range next.lift.toLinearMap := by
    change CoordinateGraph (s (r.val + 1)) (A (r.val + 1))
      (B + ((m - (r.val + 1) : ℕ) : ℝ) * C) at next
    obtain ⟨L, hpL, hcontains, hrange, hnorm⟩ := exists_coordinate_graph_step
      (hs r.val r.isLt) (A r.val) next.lift next.right_inverse
      ((hA r.val r.isLt).trans next.contains) hC (hprojection r.val r.isLt)
    have hnorm' : ‖L‖ ≤ B + ((m - r.val : ℕ) : ℝ) * C := by
      have hnext := next.norm_bound
      have hdiff : m - r.val = (m - (r.val + 1)) + 1 := by omega
      rw [hdiff, Nat.cast_add, Nat.cast_one]
      change ‖next.lift‖ ≤ B + ((m - (r.val + 1) : ℕ) : ℝ) * C at hnext
      nlinarith
    exact ⟨⟨L, hpL, hcontains, hnorm'⟩, hrange⟩
  let step := fun (r : Fin m) (next : State r.succ) => (hstep r next).choose
  have hstepSpec (r : Fin m) (next : State r.succ) :
      LinearMap.range (step r next).lift.toLinearMap ≤ LinearMap.range next.lift.toLinearMap :=
    (hstep r next).choose_spec
  have hbase : State (Fin.last m) := by
    simpa only [State, Fin.val_last, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero] using base
  let G : (r : Fin (m + 1)) → State r := Fin.reverseInduction (motive := State) hbase step
  refine ⟨G, ?_⟩
  intro r
  change LinearMap.range (Fin.reverseInduction (motive := State) hbase step r.castSucc).lift.toLinearMap ≤ _
  rw [Fin.reverseInduction_castSucc]
  exact hstepSpec r (G r.succ)

end Yau.Blueprint.Alignment.Y03Proof
