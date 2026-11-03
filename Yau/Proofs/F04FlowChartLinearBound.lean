import Yau.Proofs.F04FlowLinearComparison
import Yau.Proofs.F04SmoothChartOrder
import Yau.Proofs.F04CompactCylinderL2
import Yau.Proofs.F04VariationalNonnegative

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.Proofs.F03Aux Yau.MassTargetStatements Yau.LeafProofs.L19Aux
variable {n : ℕ}

local instance (X : KahlerManifold n) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (O : Set (Pt X)) :
    CompleteSpace (DirichletEnergy X.metric μ hμ O) := dirichletEnergy_completeSpace X.metric μ hμ O

/-- The ORIGINAL weak Mt bound becomes a true EVERY-POINT bound for the
 actual smooth chart representative. The constant M is independent of
 the finite supported domain when its source bound is. -/
theorem flow_variational_smooth_chart_linear_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (Ω K : Set (Pt X)) (hΩ : IsOpen Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    {S C α shift M : ℝ} (hS : 0 < S) (hM : 0 ≤ M)
    (B : ℝ → DirichletEnergy X.metric μ hμ Ω →L[ℝ] EnergyDual (DirichletEnergy X.metric μ hμ Ω))
    (hForm : IntrinsicFormBinding X.metric.form μ Ω h S C α shift
      (dirichletL2 X.metric μ hμ Ω) (energyRepresentative X.metric μ hμ Ω) B)
    (f : ℝ → FixedPivot μ Ω) (uE : ℝ → DirichletEnergy X.metric μ hμ Ω)
    (wE : ℝ → EnergyDual (DirichletEnergy X.metric μ hμ Ω)) (A : ℝ → FixedPivot μ Ω)
    (hSol : VariationalSolution μ Ω S (dirichletL2 X.metric μ hμ Ω) B f uE wE A)
    (hSrc : ∀ᵐ t ∂volume.restrict (Ioo 0 S), ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f t x ∧ f t x ≤ M)
    (c : Pt X) {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω)
    {u uc : Point n → ℝ} (hu : MemLp u 2 (productVolume O (Ioo 0 S)))
    (huc : ContDiffOn ℝ ∞ uc (O ×ˢ Ioo 0 S))
    (hAE : u =ᵐ[productVolume O (Ioo 0 S)] uc)
    (hSlices : ∀ᵐ t ∂volume.restrict (Ioo 0 S),
      (fun z => u (z,t)) =ᵐ[volume.restrict O]
        scalarEnergy_chartRestrictionCLM X.metric μ hμ c hO hOC hOt (scalarEnergyL2 X.metric μ hμ (uE t).val)) :
    ∀ q ∈ O ×ˢ Ioo 0 S, 0 ≤ uc q ∧ uc q ≤ M*q.2 := by
  have hLo := variationalSolution_nonnegative X.metric X.kahler_metric μ hμ Ω hΩ h hS B hForm
    f uE wE A hSol (hSrc.mono (fun _ ht => ht.mono (fun _ hx => hx.1)))
  have hUp := flow_variationalSolution_le_linear X o h U P ρ hloc μ hμ Ω K hΩ hK hΩK hS hM B hForm
    f uE wE A hSol (hSrc.mono (fun _ ht => ht.mono (fun _ hx => hx.2)))
  have ha : ∀ᵐ t ∂volume.restrict (Ioo 0 S), ∀ᵐ x ∂μ.restrict Ω,
      0 ≤ A t x ∧ A t x ≤ M*t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    filter_upwards [hLo t (Ioo_subset_Icc_self ht),hUp t (Ioo_subset_Icc_self ht)] with x hl hu
    exact ⟨hl,hu⟩
  have hr : MemLp (fun q : Point n => M*q.2) 2 (productVolume O (Ioo 0 S)) :=
    continuousOn_compactCylinder_memLp hO hOC (continuous_const.mul continuous_snd).continuousOn
  exact smooth_supported_energy_chart_bounds X.metric μ hμ Ω hΩ.measurableSet c hO hOC hOt hMap
    uE A (fun _ t => M*t) hu hr hSlices hSol.2.2.2.2.1 ha hAE huc.continuousOn
    (continuous_const.mul continuous_snd).continuousOn

end Yau.F04Proof
