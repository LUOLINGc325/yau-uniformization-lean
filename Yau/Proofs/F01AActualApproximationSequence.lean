import Yau.Proofs.F01AControlledHorizonContinuation

/-! Choose one family of actual continued approximants on increasing
horizons, before any comparison weight or canonical section is selected. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem exists_actual_approximation_sequence
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef) :
    ∃ L : ℕ → ℝ, ∃ ho : ∀ m : ℕ, u o < L m,
      ∃ h : ∀ m : ℕ, ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o (L m) (ho m)),
      ∃ U : ∀ m : ℕ, (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier → ℝ → ℝ,
        Tendsto L atTop atTop ∧ ∀ m : ℕ,
          (m : ℝ) + 1 ≤ L m ∧
          NativePotentialSlab (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m))
            ((m : ℝ) + 2) (h m) (U m) := by
  classical
  have hex (m : ℕ) : ∃ L : ℝ, ∃ ho : u o < L,
      ∃ h : ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o L ho),
      ∃ U : (sublevelManifold X.manifold u hu.1 o L ho).Carrier → ℝ → ℝ,
        (m : ℝ) + 1 ≤ L ∧
        NativePotentialSlab (approximatingMetric X.manifold X.metric.form u hu.1 o L ho)
          ((m : ℝ) + 2) h U := by
    obtain ⟨L0, hL0, hExists⟩ := controlled_approximation_exists_to_horizon X o u hu Ξ hΞ hRic
      (by positivity : 0 < 2 * ((m : ℝ) + 2))
    let L : ℝ := max L0 (max ((m : ℝ) + 1) (u o + 1))
    have hlarge : (m : ℝ) + 1 ≤ L := (le_max_left _ _).trans (le_max_right _ _)
    have ho : u o < L := by
      have hh : u o + 1 ≤ L := (le_max_right _ _).trans (le_max_right _ _)
      linarith
    obtain ⟨h, U, hsol⟩ := hExists L (le_max_left _ _) ho
    have htime : 2 * ((m : ℝ) + 2) / 2 = (m : ℝ) + 2 := by ring
    rw [htime] at hsol
    exact ⟨L, ho, h, U, hlarge, hsol⟩
  choose L ho h U hlarge hsol using hex
  refine ⟨L, ho, h, U, ?_, fun m => ⟨hlarge m, hsol m⟩⟩
  apply tendsto_atTop.2
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt b
  filter_upwards [eventually_ge_atTop N] with m hm
  have hcast : (N : ℝ) ≤ m := by exact_mod_cast hm
  linarith [hlarge m]

end Yau.NodeProofs.F01Aux
