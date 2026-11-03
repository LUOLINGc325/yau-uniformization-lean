import Yau.Proofs.F03ScalarL2

/-! Native uniform boundedness for actual finite multilinear derivative families. -/
noncomputable section
open scoped Topology
namespace Yau.Proofs.F03Aux

/-- Repeated native Banach-Steinhaus through the isometric curry maps
turns pointwise multilinear bounds into one true operator-norm bound. -/
theorem multilinear_uniform_bound
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (k : ℕ) (A : ι → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    (h : ∀ v : Fin k → E, ∃ C : ℝ, ∀ i, ‖A i v‖ ≤ C) :
    ∃ C : ℝ, ∀ i, ‖A i‖ ≤ C := by
  induction k with
  | zero =>
    obtain ⟨C,hC⟩ := h (fun i => Fin.elim0 i)
    refine ⟨C,?_⟩
    intro i
    simpa only [ContinuousMultilinearMap.fin0_apply_norm] using hC i
  | succ k ih =>
    have hx (x : E) : ∃ C : ℝ, ∀ i, ‖(A i).curryLeft x‖ ≤ C := by
      apply ih (fun i => (A i).curryLeft x)
      intro v
      simpa only [ContinuousMultilinearMap.curryLeft_apply] using h (Fin.cons x v)
    obtain ⟨C,hC⟩ := banach_steinhaus (g := fun i => (A i).curryLeft) hx
    refine ⟨C,?_⟩
    intro i
    simpa only [ContinuousMultilinearMap.curryLeft_norm] using hC i

end Yau.Proofs.F03Aux
