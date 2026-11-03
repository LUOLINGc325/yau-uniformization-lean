import Yau.Proofs.F03EllipticTranslation

/-! Genuine finite-order coefficient bounds on fixed compact chart buffers. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem compact_finite_norm_family_bound {E F ι : Type*} [TopologicalSpace E]
    [NormedAddCommGroup F] [Fintype ι]
    (K : Set E) (hK : IsCompact K) (f : ι → E → F)
    (hf : ∀ i,ContinuousOn (f i) K) :
    ∃ C : ℝ,0 < C ∧ ∀ i x,x ∈ K → ‖f i x‖ ≤ C := by
  classical
  have hEach : ∀ i,∃ C : ℝ,0 ≤ C ∧ ∀ x ∈ K,‖f i x‖ ≤ C := by
    intro i
    obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (hf i)
    exact ⟨max 0 C,le_max_left _ _,fun x hx => (hC x hx).trans (le_max_right _ _)⟩
  choose C hC0 hC using hEach
  refine ⟨1+∑ i,C i,add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => hC0 i)),?_⟩
  intro i x hx
  have hi : C i ≤ ∑ j,C j := Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i)
  exact (hC i x hx).trans (hi.trans (by linarith))

theorem elliptic_coefficients_compact_jet_bounds {n : ℕ}
    (D : Set (ComplexVector n)) (hD : IsOpen D)
    (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (b : ComplexVector n → RIdx n → ℝ)
    (ha : ∀ i j,ContDiffOn ℝ ∞ (fun z => a z i j) D)
    (hb : ∀ i,ContDiffOn ℝ ∞ (fun z => b z i) D)
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hKD : K ⊆ D) (N : ℕ) :
    ∃ A : ℝ,0 < A ∧ ∀ k ≤ N,∀ z ∈ K,∀ i j,
      ‖iteratedFDeriv ℝ k (fun w => a w i j) z‖ ≤ A ∧
      ‖iteratedFDeriv ℝ k (fun w => b w i) z‖ ≤ A := by
  have hAC : ∀ q : Fin (N+1) × RIdx n × RIdx n,ContinuousOn
      (fun z => ‖iteratedFDeriv ℝ q.1.val (fun w => a w q.2.1 q.2.2) z‖) K := by
    intro q z hz
    exact (((ha q.2.1 q.2.2).contDiffAt (hD.mem_nhds (hKD hz))).differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl q.1.val)).continuousAt.norm.continuousWithinAt
  have hBC : ∀ q : Fin (N+1) × RIdx n,ContinuousOn
      (fun z => ‖iteratedFDeriv ℝ q.1.val (fun w => b w q.2) z‖) K := by
    intro q z hz
    exact (((hb q.2).contDiffAt (hD.mem_nhds (hKD hz))).differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl q.1.val)).continuousAt.norm.continuousWithinAt
  obtain ⟨A,hA,hAb⟩ := compact_finite_norm_family_bound K hK
    (fun q : Fin (N+1) × RIdx n × RIdx n =>
      fun z => ‖iteratedFDeriv ℝ q.1.val (fun w => a w q.2.1 q.2.2) z‖) hAC
  obtain ⟨B,hB,hBb⟩ := compact_finite_norm_family_bound K hK
    (fun q : Fin (N+1) × RIdx n => fun z => ‖iteratedFDeriv ℝ q.1.val (fun w => b w q.2) z‖) hBC
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro k hk z hz i j
  have h1 := hAb (⟨k,by omega⟩,i,j) z hz
  have h2 := hBb (⟨k,by omega⟩,i) z hz
  rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] at h1 h2
  exact ⟨h1.trans (by linarith),h2.trans (by linarith)⟩

end Yau.Proofs.F03Aux
