import Yau.Proofs.F04ExhaustionLimitRegularity
import Yau.Proofs.F04DominatedInitialRegularity

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- A compact smooth cutoff of the ACTUAL source has a genuine global
 classical potential. Every weak solution, chart regularization, domain
 order, exhaustion supremum and closed-face regularity is constructed.
 One M and the original finite records are retained, as is positive-time
 regularity on the larger horizon for later cutoff-source limits. -/
theorem flow_compact_source_classical_potential
    {n : ℕ} (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (hTS : T < S)
    (q : Pt X → ℝ) (hq : SmoothFn q) (hqRange : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (hcq : HasCompactSupport q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ (v : ℕ → STF X) (z : STF X),
      (∀ j, IsFiniteClassicalPotential X h ρ μ hμ S hS q M (potentialDomain u j) (v j)) ∧
      (∀ x t, t ∈ Icc 0 S → Tendsto (fun j => v j x t) atTop (𝓝 (z x t))) ∧
      (∀ x t, t ∈ Icc 0 S → 0 ≤ z x t ∧ z x t ≤ ρ x t ∧ z x t ≤ M*t) ∧
      (∀ x, z x 0 = 0) ∧ SmoothSpaceTime z (Ioo 0 S) ∧
      (∀ x t, t ∈ Ioo 0 S → heatOp h (Icc 0 S) z x t = q x * source X h x t) ∧
      SmoothSpaceTime z (Icc 0 T) ∧
      (∀ x t, t ∈ Icc 0 T → heatOp h (Icc 0 T) z x t = q x * source X h x t) := by
  obtain ⟨M,hM,v,z,hData,_hMono,hTend,hBound,_hLe,h0⟩ :=
    flow_finite_exhaustion_potential_limit hn X o h U P ρ hloc μ hμ u hu hS q hq hqRange hcq
  obtain ⟨hPos,hPDE⟩ := flow_finite_potential_limit_positive_regularization hn X o h U P ρ hloc
    μ hμ u hu hS q hq v z hData hTend
  obtain ⟨hClosed,hClosedEq⟩ := flow_dominated_initial_regularization hn X o h U P ρ hloc
    hS hT hTS q hq z hPos h0 (fun x t ht => ⟨(hBound x t (Ioo_subset_Icc_self ht)).1,
      (hBound x t (Ioo_subset_Icc_self ht)).2.1⟩) hPDE
  exact ⟨M,hM,v,z,hData,hTend,hBound,h0,hPos,hPDE,hClosed,hClosedEq⟩

/-- Source ordering passes through the ACTUAL finite records and their
 pointwise limits. The larger finite domain index is shifted by ONE, so
 no unproved same-boundary weak trace identification is used. -/
theorem finite_potential_limits_source_le
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {S : ℝ} (hS : 0 < S) {q r : Pt X → ℝ} (hqr : ∀ x, q x ≤ r x) {M N : ℝ}
    (v w : ℕ → STF X) (z a : STF X)
    (hv : ∀ j, IsFiniteClassicalPotential X h ρ μ hμ S hS q M (potentialDomain u j) (v j))
    (hw : ∀ j, IsFiniteClassicalPotential X h ρ μ hμ S hS r N (potentialDomain u j) (w j))
    (hz : ∀ x t, t ∈ Icc 0 S → Tendsto (fun j => v j x t) atTop (𝓝 (z x t)))
    (ha : ∀ x t, t ∈ Icc 0 S → Tendsto (fun j => w j x t) atTop (𝓝 (a x t))) :
    ∀ x t, t ∈ Icc 0 S → z x t ≤ a x t := by
  intro x t ht
  apply le_of_tendsto_of_tendsto' (hz x t ht) ((ha x t ht).comp (tendsto_add_atTop_nat 1))
  intro j
  exact finite_potential_data_le X o h U P ρ hloc μ hμ hS hqr
    (potentialDomain_open X o u hu j) (potentialDomain_compact_closure X o u hu j)
    (potentialDomain_open X o u hu (j+1)) (potentialDomain_closure_succ X o u hu j)
    (hv j) (hw (j+1)) x t ht

end Yau.F04Proof
