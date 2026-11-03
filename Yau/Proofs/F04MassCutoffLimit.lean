import Yau.Proofs.F04MassCutoff

open Filter Set
open scoped Topology Manifold

noncomputable section

namespace Yau.F04Proof

theorem massCutoff_nat_mono {α : Type*} (u : α → ℝ) (hu : ∀ x, 0 ≤ u x) (x : α) :
    Monotone (fun N : ℕ => massCutoff u ((N : ℝ) + 1) x) := by
  intro N L hNL
  apply massCutoff_mono u hu (by positivity)
  exact_mod_cast Nat.add_le_add_right hNL 1

theorem massCutoff_eventually_one_on_compact {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ x ∈ K, massCutoff u ((m : ℝ) + 1) x = 1 := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (Yau.LeafProofs.L18Aux.continuous_of_smoothFn hu).continuousOn
  obtain ⟨N, hN⟩ := exists_nat_ge B
  refine ⟨N, ?_⟩
  intro m hm x hx
  apply massCutoff_one u (by positivity)
  have hxm : u x ≤ (N : ℝ) := (le_abs_self _).trans ((hB x hx).trans hN)
  have hNm : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

theorem massCutoff_nat_tendsto_one {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (x : M.Carrier) :
    Tendsto (fun N : ℕ => massCutoff u ((N : ℝ) + 1) x) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := massCutoff_eventually_one_on_compact hu
    (isCompact_singleton : IsCompact ({x} : Set M.Carrier))
  have heq : (fun N : ℕ => massCutoff u ((N : ℝ) + 1) x) =ᶠ[atTop] (fun _ => (1 : ℝ)) :=
    eventually_atTop.mpr ⟨N, fun m hm => hN m hm x (mem_singleton x)⟩
  exact (tendsto_congr' heq).mpr tendsto_const_nhds

end Yau.F04Proof
