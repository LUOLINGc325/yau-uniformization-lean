import Yau.Proofs.F01AControlledSlabEstimates
import Yau.Proofs.F01ANativeTerminalPasting

/-! Fixed-approximant continuation by the supremum of genuine existence
intervals. The common comparison constant comes from the actual controlled
estimate, and the endpoint is obtained from the proved native extension. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

/-- A controlled approximant with a witness-independent finite sandwich
reaches the entire prescribed closed horizon. -/
theorem controlled_native_horizon_from_sandwich (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) {L : ℝ} (ho : u o < L)
    {H : ℝ} (hH : 0 < H) :
    let N := sublevelManifold X.manifold u hu.1 o L ho
    let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
    (∃ C : ℝ, 1 ≤ C ∧ ∀ T, 0 < T → T ≤ H → ∀ h U,
      NativePotentialSlab α T h U → ∀ x t, t ∈ Icc 0 T →
        (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat α x).PosSemidef ∧
        ((C : ℂ) • gMat α x - gMat (h t) x).PosSemidef) →
    ∃ (h : ℝ → HermitianField N) (U : N.Carrier → ℝ → ℝ),
      NativePotentialSlab α H h U := by
  classical
  dsimp only
  intro hcommon
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
  obtain ⟨hα, hBG, hComplete⟩ := controlled_background_geometry X o u hu ho
  obtain ⟨T, C, h, U, hT, hTuple⟩ := exists_native_short_time_tuple α hα hComplete hBG
  let E := controlledExistenceTimes X o u hu ho H
  have hne : E.Nonempty := by
    refine ⟨min T H, lt_min hT hH, min_le_right _ _, h, U, ?_⟩
    exact nativePotentialSlab_iff_exists_tuple.mpr ⟨C, hTuple.restrict (min_le_left _ _)⟩
  have hsup := positive_sup_of_existence_times E hne
    (fun T hT => hT.1) (fun T hT => hT.2.1)
  let Tstar := sSup E
  have hTstar : 0 < Tstar := hsup.1
  obtain ⟨hstar, Ustar, hpartial⟩ :=
    controlled_unique_partial_at_sup X o u hu ho H hne hcommon
  obtain ⟨A⟩ := Yau.LeafProofs.L17Aux.exists_boundedChartFamily α hBG
  obtain ⟨ε, hε, hbar, Ubar, hbarSol, hhbar, hUbar⟩ :=
    native_partial_solution_extends α hα A hTstar hstar Ustar hpartial
  apply closed_horizon_of_sup_extension
    (fun T => ∃ (h : ℝ → HermitianField N) (U : N.Carrier → ℝ → ℝ),
      NativePotentialSlab α T h U) H hne
  · intro T S hST hsol
    obtain ⟨h, U, hsol⟩ := hsol
    exact ⟨h, U, nativePotentialSlab_restrict hsol hST⟩
  · refine ⟨Tstar + ε, ?_, hbar, Ubar, hbarSol⟩
    change Tstar < Tstar + ε
    linarith

/-- The exact controlled horizon producer: the level threshold precedes the
approximation level, and the actual solution witnesses are chosen last. -/
theorem controlled_approximation_exists_to_horizon
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef)
    {D : ℝ} (hD : 0 < D) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ ho : u o < L,
      let N := sublevelManifold X.manifold u hu.1 o L ho
      let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
      ∃ (h : ℝ → HermitianField N) (U : N.Carrier → ℝ → ℝ),
        NativePotentialSlab α (D / 2) h U := by
  obtain ⟨L0, hL0, hcommon⟩ := controlled_slab_common_sandwich X o u hu Ξ hΞ hRic hD
  refine ⟨L0, hL0, ?_⟩
  intro L hL ho
  exact controlled_native_horizon_from_sandwich X o u hu ho
    (by positivity : 0 < D / 2) (hcommon L hL ho)

end Yau.NodeProofs.F01Aux
