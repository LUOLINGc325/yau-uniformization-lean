import Yau.Proofs.P06ContinuousHeat

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs
open Yau.LeafProofs.L19Aux Yau.LeafProofs.L18Aux Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual bounded continuous-initial solution retains its original
L19 scalar heat representation after subtracting the value at infinity. -/
theorem continuousInitialHeat_exists_representation (hn : 0 < n) (g : SmoothMetric M)
    (hK : IsKahler g) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : M.Carrier → ℝ) (c : ℝ) (hcont : Continuous (fun x => f x - c))
    (hcompact : HasCompactSupport (fun x => f x - c)) :
    ∃ u, IsContinuousInitialScalarHeat g.form f u ∧
      ∃ hf0 : MemLp (fun x => f x - c) 2 μ, ∀ t, 0 < t →
        (fun x => u t x - c) =ᵐ[μ] scalarHeatFamily g μ hμ t (hf0.toLp (fun x => f x - c)) := by
  let f0 : M.Carrier → ℝ := fun x => f x - c
  letI : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  have hf0 : MemLp f0 2 μ := hcont.memLp_of_hasCompactSupport hcompact
  let fL : Lp ℝ 2 μ := hf0.toLp f0
  let v : M.Carrier → ℝ → ℝ := scalarClassicalHeat hn g hK μ hμ fL
  let u : ℝ → M.Carrier → ℝ := fun t x => if t ≤ 0 then f x else v x t + c
  have hv : SmoothSpaceTime v (Set.Ioi 0) := scalarClassicalHeat_smooth hn g hK μ hμ fL
  have hshift : SmoothSpaceTime (fun y s => v y s + c) (Set.Ioi 0) := by
    intro a
    exact (hv a).add contDiffOn_const
  have hu (t : ℝ) (ht : 0 < t) : u t = fun x => v x t + c := by
    funext x
    simp only [u, not_le_of_gt ht, ↓reduceIte]
  have hvs (t : ℝ) (ht : 0 < t) : SmoothFn (fun x => v x t) := smoothSpaceTime_slice hv ht
  have htrace : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ,
      0 < t → t < δ → ∀ x, |v x t - f0 x| < ε := by
    apply scalarHeat_uniform_initial_of_compact_approximations g hK μ hμ f0 fL
      hf0.coeFn_toLp (continuousCompact_core_approx g μ hμ hcont hcompact)
    · intro t ht
      exact continuous_of_smoothFn (hvs t ht)
    · intro t ht
      exact scalarClassicalHeat_ae hn g hK μ hμ fL ht
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hcompact
  have hbound (x : M.Carrier) (t : ℝ) (ht : 0 < t) : |v x t| ≤ max B 0 := by
    apply scalarClassicalHeat_linf hn g hK μ hμ fL (le_max_right _ _)
    · filter_upwards [hf0.coeFn_toLp] with y hy
      rw [hy]
      exact (hB y).trans (le_max_left _ _)
    · exact ht
  have hclass : IsContinuousInitialScalarHeat g.form f u := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x
      simp only [u, le_refl, ↓reduceIte]
    · intro a
      apply (hshift a).congr
      intro p hp
      simp only [u, not_le_of_gt (show 0 < p.2 from hp.2), ↓reduceIte]
    · intro x t ht
      rw [hu t ht, laplacian_add_const g.form (hvs t ht) c x]
      apply (scalarClassicalHeat_hasDerivAt hn g hK μ hμ fL x ht).add_const c
        |>.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp only [u, v, not_le_of_gt (show 0 < s from hs), ↓reduceIte]
    · intro T _hT
      refine ⟨max B 0 + |c|, by positivity, ?_⟩
      intro x t ht _htT
      rw [hu t ht]
      exact (abs_add_le _ _).trans (add_le_add (hbound x t ht) le_rfl)
    · intro K _hK ε hε
      obtain ⟨δ, hδ, hδtrace⟩ := htrace ε hε
      refine ⟨δ, hδ, ?_⟩
      intro t ht htδ x _hxK
      rw [hu t ht]
      have hx := (hδtrace t ht htδ x).le
      convert hx using 1 <;> congr 1 <;> dsimp only [f0] <;> ring
  refine ⟨u, hclass, hf0, ?_⟩
  intro t ht
  simpa only [hu t ht, add_sub_cancel_right] using
    (scalarClassicalHeat_ae hn g hK μ hμ fL ht)


end Yau.NodeProofs.P06Aux
