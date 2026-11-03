import Yau.Proofs.P06TraceHilbertScalarCore

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.TraceHilbert
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarEnergy_green_laplacian (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (u : ScalarEnergySpace g μ hμ) (k : ScalarEnergyDomain g μ hμ) :
    scalarClosedEnergy g μ hμ u k =
      -inner ℝ (scalarEnergyL2 g μ hμ u)
        (scalarEnergyDomainL2 g μ hμ (laplaceTest g μ hμ k)) := by
  have he : scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k) =
      scalarEnergyDomainL2 g μ hμ k - scalarEnergyDomainL2 g μ hμ (laplaceTest g μ hμ k) := by
    apply Lp.ext
    filter_upwards [scalarEnergyDomainL2_coe g μ hμ (scalarEnergyGreenTest g μ hμ k),
      scalarEnergyDomainL2_coe g μ hμ k,
      scalarEnergyDomainL2_coe g μ hμ (laplaceTest g μ hμ k),
      Lp.coeFn_sub (scalarEnergyDomainL2 g μ hμ k)
        (scalarEnergyDomainL2 g μ hμ (laplaceTest g μ hμ k))] with x hG hk hL hsub
    rw [hG, hsub, Pi.sub_apply, hk, hL]
    rfl
  rw [scalarClosedEnergy, scalarEnergyL2_green g hk μ hμ u k,
    scalarEnergyL2_coe, he, inner_sub_right]
  ring

theorem scalarHeat_strongPath (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (f : Lp ℝ 2 μ) (t : ℝ) (ht : 0 < t) :
    ∃ w, HasDerivAt (fun s => scalarLift g μ (scalarHeatFamily g μ hμ s f)) w t ∧
      (scalarLift g μ (scalarHeatFamily g μ hμ t f), (-2 : ℝ) • w) ∈
        (hodgeCoreOperator g μ hμ 0).closure.graph := by
  let d := scalarHeatFamily g μ hμ t f - scalarHeatInverse g μ hμ t f
  refine ⟨scalarLift g μ d, (scalarLift g μ).hasFDerivAt.comp_hasDerivAt t
    (scalarHeatFamily_apply_hasDerivAt g μ hμ ht f), ?_⟩
  have hg := scalar_closed_graph_of_tests g μ hμ hk
    (scalarHeatFamily g μ hμ t f) ((-2 : ℝ) • d) (by
      intro k
      have he := scalarEnergy_green_laplacian g μ hμ hk (scalarHeatEnergy g μ hμ t f) k
      rw [scalarHeatEnergy_L2 g μ hμ ht, scalarHeatEnergy_weak g μ hμ ht,
        inner_sub_left, scalarEnergyL2_coe] at he
      simp only [inner_smul_left, conj_trivial, d, inner_sub_left]
      linarith)
  simpa only [map_smul] using hg

/-- Degree-zero Hodge heat at the original clock is the actual scalar
energy heat, through the proved L² isometry. The factor two is retained
in the generator graph and cancels the Hodge `t/2` clock. -/
theorem scalarHeat_eq_hodgeHeat (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (f : Lp ℝ 2 μ) (t : ℝ) (ht : 0 ≤ t) :
    scalarLift g μ (scalarHeatFamily g μ hμ t f) =
      hodgeHeatHilbert g μ hμ 0 t (scalarLift g μ f) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [scalarHeatFamily_zero, hodgeHeatHilbert_zero, one_apply_eq_self]
  apply hodgeStrongPath_eq_heat g μ hμ 0 (scalarLift g μ f)
    (fun s => scalarLift g μ (scalarHeatFamily g μ hμ s f))
    (scalarHeat_strongPath g μ hμ hk f)
  · exact (scalarLift g μ).continuous.continuousAt.tendsto.comp
      ((scalarHeatFamily_tendsto_zero g μ hμ f).mono_left
        (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self))
  · exact ht

end Yau.NodeProofs.P06Aux.TraceHilbert
