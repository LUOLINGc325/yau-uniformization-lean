import Yau.Proofs.P06HodgeRegularityCalculus
import Yau.Proofs.P06HodgeRegularityForward

/-! Genuine weak gradients obtained from compact smooth graph approximants
of a finite divergence system with L² value and flux sources. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E α ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype α] [Fintype ι]

/-- Smooth compact approximants satisfying the actual finite system provide
L² weak derivatives of their raw L² limit. The source may be any L² value
plus divergence of an L² flux; no deficiency relation is imposed. -/
theorem regularitySystem_exists_weak_gradient
    (ν : Measure E) [ν.IsAddHaarMeasure] (v : ι → E)
    (a : α → α → ι → ι → E → ℝ) (B : α → α → ι → E → ℝ)
    (C : α → α → E → ℝ) (U f : ℕ → E → α → ℝ)
    (g : ℕ → E → α → ι → ℝ) (u0 f0 : E → α → ℝ) (g0 : E → α → ι → ℝ)
    (K : Set E) (hK : IsCompact K)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    (hC : ∀ r c, Continuous (C r c))
    (hU : ∀ m c, ContDiff ℝ ∞ (fun z => U m z c))
    (hUK : ∀ m c, tsupport (fun z => U m z c) ⊆ K)
    (hf : ∀ m r, Continuous (fun z => f m z r))
    (hg : ∀ m r i, ContDiff ℝ ∞ (fun z => g m z r i))
    (hf2 : ∀ m r, MemLp (fun z => f m z r) 2 ν)
    (hg2 : ∀ m r i, MemLp (fun z => g m z r i) 2 ν)
    (hu02 : ∀ r, MemLp (fun z => u0 z r) 2 ν)
    (hf02 : ∀ r, MemLp (fun z => f0 z r) 2 ν)
    (hg02 : ∀ r i, MemLp (fun z => g0 z r i) 2 ν)
    (ell b c : ℝ) (hell : 0 < ell) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hboundB : ∀ z ∈ K, ∀ r s i, |B r s i z| ≤ b)
    (hboundC : ∀ z ∈ K, ∀ r s, |C r s z| ≤ c)
    (hcoercive : ∀ z ∈ K, ∀ ξ : (ι × α) → ℝ,
      ell * ∑ p, (ξ p)^2 ≤ ∑ r, ∑ s, ∑ i, ∑ j,
        a r s i j z * ξ (j,s) * ξ (i,r))
    (heq : ∀ m z r, divergenceSystemApply v a B C (U m) z r =
      f m z r + ∑ i, fderiv ℝ (fun y => g m y r i) z (v i))
    (hUt : ∀ r, Tendsto (fun m => ∫ z, ‖U m z r - u0 z r‖^2 ∂ν) atTop (𝓝 0))
    (hft : ∀ r, Tendsto (fun m => ∫ z, ‖f m z r - f0 z r‖^2 ∂ν) atTop (𝓝 0))
    (hgt : ∀ r i, Tendsto (fun m => ∫ z, ‖g m z r i - g0 z r i‖^2 ∂ν) atTop (𝓝 0)) :
    ∃ D : E → ι × α → ℝ,
      (∀ q, MemLp (fun z => D z q) 2 ν) ∧
      (∀ q, tsupport (fun z => D z q) ⊆ K) ∧
      (∀ q, Tendsto (fun m => ∫ z,
        ‖DivergenceEnergy.derivative v (U m) z q - D z q‖^2 ∂ν) atTop (𝓝 0)) ∧
      ∀ i r, regularityWeakDeriv ν Set.univ (v i) (fun z => u0 z r)
        (fun z => D z (i,r)) := by
  have hcU (m : ℕ) (r : α) : HasCompactSupport (fun z => U m z r) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hUK m r)
  have hU2 (m : ℕ) (r : α) : MemLp (fun z => U m z r) 2 ν :=
    (hU m r).continuous.memLp_of_hasCompactSupport (hcU m r)
  have ht := DivergenceEnergy.gradient_pair_sq_tendsto_zero ν v a B C U f g K hK
    ha hB hC hU hUK hf hg hf2 hg2 ell b c hell hb hc hboundB hboundC hcoercive heq
    (DivergenceEnergy.pair_valueSq_tendsto_zero ν U u0 hU2 hu02 hUt)
    (DivergenceEnergy.pair_valueSq_tendsto_zero ν f f0 hf2 hf02 hft)
    (DivergenceEnergy.pair_valueSq_tendsto_zero ν
      (fun m z (q : ι × α) => g m z q.2 q.1) (fun z (q : ι × α) => g0 z q.2 q.1)
      (fun m q => hg2 m q.2 q.1) (fun q => hg02 q.2 q.1) (fun q => hgt q.2 q.1))
  obtain ⟨D, hD, hDK, hDlim⟩ := exists_compact_gradient_limits ν v U hU K hK hUK ht
  refine ⟨D, hD, hDK, hDlim, ?_⟩
  intro i r
  exact regularityWeakDeriv_of_smooth_limits ν (v i) (fun m z => U m z r)
    (fun z => u0 z r) (fun z => D z (i,r)) (fun m => hU m r) (fun m => hcU m r)
    (hu02 r) (hD (i,r)) (hUt r) (hDlim (i,r))

end Yau.NodeProofs.P06Aux
