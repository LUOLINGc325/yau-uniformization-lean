import Yau.Proofs.P06Geometry
import Yau.LeafProofs.L19HeatClassicalCore

/-! Existence in the original continuous-initial scalar heat class.  The
evolution is the already constructed L19 scalar semigroup on f-c, followed by
addition of the actual constant value at infinity. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs
open Yau.LeafProofs.L19Aux Yau.LeafProofs.L18Aux Yau.LeafProofs.L12Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Uniform compact smooth approximation of a continuous compact datum on
the original manifold, in the actual scalar energy core. -/
theorem continuousCompact_core_approx (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {f : M.Carrier → ℝ}
    (hf : Continuous f) (hcf : HasCompactSupport f) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ScalarEnergyDomain g μ hμ,
      ∀ x, |f x - k x| < ε := by
  letI := manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := manifold_locallyCompact M
  intro ε hε
  obtain ⟨k, hk, hksupport⟩ := hf.exists_contMDiff_approx
    𝓘(ℝ, ComplexVector n) ⊤ (ε := fun _ => ε) continuous_const (fun _ => hε)
  refine ⟨⟨k, Yau.LeafProofs.L12Aux.smoothFn_of_contMDiff_real k k.contMDiff,
    hcf.mono hksupport⟩, ?_⟩
  intro x
  simpa only [Real.dist_eq, abs_sub_comm] using hk x

/-- All rough data in P06 have an evolution with exactly the independent
PDE, finite-time bound, and continuous initial trace required by the target.
The Hessian conclusion and uniqueness are separate obligations. -/
theorem continuousInitialHeat_exists (hn : 0 < n) (g : SmoothMetric M)
    (hK : IsKahler g) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (f : M.Carrier → ℝ) (hf : LipschitzForMetric g.form f)
    (hcf : ConstantOutsideCompact f) :
    ∃ u, IsContinuousInitialScalarHeat g.form f u := by
  obtain ⟨c, hcont, hcompact⟩ := compactExterior_difference g hf hcf
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
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
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

end Yau.NodeProofs.P06Aux
