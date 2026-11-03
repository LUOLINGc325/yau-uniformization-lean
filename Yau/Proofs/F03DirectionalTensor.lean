import Yau.Proofs.F03DirectionalJets
import Yau.Proofs.F03MultilinearUniformBound

/-! Actual directional words control full finite Fréchet derivative tensors. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- The genuine finite Fréchet tensor evaluated on a tuple is the actual
outermost-first directional derivative word on every smooth open germ. -/
theorem iteratedFDeriv_eq_directionalWord {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Q : Set E} (hQ : IsOpen Q)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f Q) (k : ℕ) (v : Fin k → E)
    {x : E} (hx : x ∈ Q) :
    iteratedFDeriv ℝ k f x v = directionalWordDerivative f (List.ofFn v) x := by
  induction k generalizing x with
  | zero => simp only [iteratedFDeriv_zero_apply,List.ofFn_zero,directionalWordDerivative]
  | succ k ih =>
    have hd := (hf.contDiffAt (hQ.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)
    rw [hd.iteratedFDeriv_succ_apply_left']
    have heq : (fun y => iteratedFDeriv ℝ k f y (Fin.tail v)) =ᶠ[𝓝 x]
        directionalWordDerivative f (List.ofFn (Fin.tail v)) := by
      filter_upwards [hQ.mem_nhds hx] with y hy
      exact ih (Fin.tail v) hy
    rw [heq.fderiv_eq,List.ofFn_succ]
    rfl

/-- True operator-norm bounds follow from already known uniform actual
word bounds by native multilinear Banach-Steinhaus, before every index/point. -/
theorem iteratedFDeriv_uniform_bound_of_words {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Q K : Set E} (hQ : IsOpen Q) (hKQ : K ⊆ Q) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Q)
    (hWords : ∀ w : List E, ∃ C : ℝ, ∀ i, ∀ x ∈ K,
      |directionalWordDerivative (f i) w x| ≤ C) (k : ℕ) :
    ∃ C : ℝ, ∀ i, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ C := by
  let A : (ι × K) → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ :=
    fun i => iteratedFDeriv ℝ k (f i.1) i.2.val
  have hv (v : Fin k → E) : ∃ C : ℝ, ∀ i : ι × K, ‖A i v‖ ≤ C := by
    obtain ⟨C,hC⟩ := hWords (List.ofFn v)
    refine ⟨C,?_⟩
    intro i
    change ‖iteratedFDeriv ℝ k (f i.1) i.2.val v‖ ≤ C
    rw [iteratedFDeriv_eq_directionalWord hQ (hf i.1) k v (hKQ i.2.property),Real.norm_eq_abs]
    exact hC i.1 i.2.val i.2.property
  obtain ⟨C,hC⟩ := multilinear_uniform_bound k A hv
  exact ⟨C,fun i x hx => hC (i,⟨x,hx⟩)⟩

end Yau.Proofs.F03Aux
