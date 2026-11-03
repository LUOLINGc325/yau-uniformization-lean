import Yau.Proofs.HeatSmoothExhaustionPerturbation

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Yau.Proofs.SmoothExhaustionAux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem regular_function_around_compact {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ f : M.Carrier → ℝ, SmoothFn f ∧ (∀ p ∈ K, f p < 0) ∧
      IsCompact {p | f p ≤ 0} ∧ ChartRegularZero f := by
  letI : LocallyCompactSpace M.Carrier := ChartedSpace.locallyCompactSpace (ComplexVector n) M.Carrier
  let C := CompactExhaustion.choice M.Carrier
  obtain ⟨j,hj⟩ := C.exists_superset_of_isCompact hK
  obtain ⟨β,hβ,hcβ,hβK,hβT,hβbounds⟩ := cutoff_between_compacts hK (C.isCompact (j+1))
    (hj.trans (C.subset_interior_succ j))
  let f₀ : M.Carrier → ℝ := fun p => 1-2*β p
  have hf₀ : SmoothFn f₀ := by
    intro a
    exact contDiffOn_const.sub (contDiffOn_const.mul (hβ a))
  have hf₀c : Continuous f₀ := continuous_of_smoothFn hf₀
  let S : Set M.Carrier := {p | |f₀ p| ≤ 1/2}
  have hSc : IsClosed S := isClosed_le (continuous_abs.comp hf₀c) continuous_const
  have hST : S ⊆ C (j+1) := by
    intro p hp
    by_contra hn
    have HB := hβT p hn
    change |1-2*β p| ≤ (1/2 : ℝ) at hp
    rw [HB] at hp
    norm_num at hp
  have hS : IsCompact S := (C.isCompact (j+1)).of_isClosed_subset hSc hST
  obtain ⟨f,hf,hsmall,hreg⟩ := exists_small_regular_perturbation f₀ hf₀ S hS
  have hnegative (p : M.Carrier) (hp : p ∈ K) : f p < 0 := by
    have HH := (abs_lt.mp (hsmall p)).2
    change f p-(1-2*β p)<(1/4 : ℝ) at HH
    rw [hβK p hp] at HH
    linarith
  have hsublevel : {p | f p ≤ 0} ⊆ C (j+1) := by
    intro p hp
    by_contra hn
    have HH := (abs_lt.mp (hsmall p)).1
    change -(1/4 : ℝ)<f p-(1-2*β p) at HH
    rw [hβT p hn] at HH
    change f p ≤ 0 at hp
    linarith
  have hcompact : IsCompact {p | f p ≤ 0} := (C.isCompact (j+1)).of_isClosed_subset
    (isClosed_le (continuous_of_smoothFn hf) continuous_const) hsublevel
  refine ⟨f,hf,hnegative,hcompact,?_⟩
  intro p hp
  have Hp := hsmall p
  rw [hp,zero_sub,abs_neg] at Hp
  have hpS : p ∈ S := le_trans Hp.le (by norm_num)
  exact hreg p hpS hp

end Yau.Proofs.SmoothExhaustionAux
