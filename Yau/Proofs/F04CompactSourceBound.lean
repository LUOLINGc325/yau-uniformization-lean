import Yau.Proofs.F04FlowSourceSmooth

open Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- A genuine compact spatial cutoff gives ONE global source bound on
 the closed time slab, selected before every finite exhaustion domain. -/
theorem flow_compact_cutoff_source_bound
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S : ℝ} (hS : 0 < S)
    (q : Pt X → ℝ) (hq : SmoothFn q) (hcq : HasCompactSupport q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Pt X, ∀ t ∈ Icc 0 S, |q x * source X h x t| ≤ M := by
  have hSmooth := flow_cutoff_source_smooth_closed X o h U P ρ hloc hS q hq
  obtain ⟨M,hM,hMb⟩ := compact_scalar_profile_bound hS.le (fun x t => q x * source X h x t)
    (smoothSpaceTime_continuousOn hSmooth) (tsupport q) hcq
  refine ⟨M,hM,?_⟩
  intro x t ht
  by_cases hx : x ∈ tsupport q
  · simpa only [timeClamp_eq_of_mem S hS.le ht,Real.norm_eq_abs] using hMb x hx t
  · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,abs_zero]
    exact hM

end Yau.F04Proof
