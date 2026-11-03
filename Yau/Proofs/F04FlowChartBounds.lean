import Yau.Proofs.F04SmoothChartOrder
import Yau.Proofs.F04CompactCylinderL2
import Yau.Proofs.F04FlowRhoComparison
import Yau.Proofs.F04VariationalNonnegative
import Yau.Proofs.F04RhoInitialGrowth

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.ParabolicCandidates Yau.Proofs.F03Aux
  Yau.MassTargetStatements Yau.LeafProofs.L19Aux Yau.LeafProofs.L16Aux Yau.LeafProofs.L12Aux
variable {n : ℕ}

local instance (X : KahlerManifold n) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (Ω : Set (Pt X)) :
    CompleteSpace (DirichletEnergy X.metric μ hμ Ω) := dirichletEnergy_completeSpace X.metric μ hμ Ω

/-- The original physical rho compact estimate gives genuine compact
 chart growth to EVERY nonnegative classical function below that rho. -/
theorem flow_chart_rho_dominated_compact_growth
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S : ℝ} (hS : 0 < S)
    (c : Pt X) {O : Set (Space n)} (hOt : O ⊆ chartTarget c) {u : Point n → ℝ}
    (hu : ∀ q ∈ O ×ˢ Ioo 0 S, 0 ≤ u q ∧ u q ≤ ρ (chartInv c q.1) q.2) :
    ∀ Z : Set (Space n), IsOpen Z → IsCompact (closure Z) → closure Z ⊆ O →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Z, ∀ t ∈ Ioo 0 S, |u (x,t)| ≤ C*t := by
  intro Z _hZ hZC hZO
  have hi : ContinuousOn (chartInv c) (closure Z) := fun z hz =>
    (contMDiffAt_chartInv_real c z (hOt (hZO hz))).continuousAt.continuousWithinAt
  obtain ⟨C,hC,hCb⟩ := flow_rho_compact_initial_growth X o h U P ρ hloc hS
    (chartInv c '' closure Z) (hZC.image_of_continuousOn hi)
  refine ⟨C,hC,?_⟩
  intro x hx t ht
  have hb := hu (x,t) ⟨hZO (subset_closure hx),ht⟩
  rw [abs_of_nonneg hb.1]
  exact hb.2.trans ((le_abs_self _).trans (hCb (chartInv c x) ⟨x,subset_closure hx,rfl⟩ t
    (Ioo_subset_Icc_self ht)))

/-- The ORIGINAL continuous variational trace bounds imply pointwise
 0<=uc<=the SAME supplied rho for its actual smooth chart representative,
 and hence the ACTUAL compact linear growth needed for initial regularity.
 No classical bound or initial growth is an input. -/
theorem flow_variational_smooth_chart_bounds
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (Ω K : Set (Pt X)) (hΩ : IsOpen Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    {S C α shift : ℝ} (hS : 0 < S)
    (B : ℝ → DirichletEnergy X.metric μ hμ Ω →L[ℝ]
      EnergyDual (DirichletEnergy X.metric μ hμ Ω))
    (hForm : IntrinsicFormBinding X.metric.form μ Ω h S C α shift
      (dirichletL2 X.metric μ hμ Ω) (energyRepresentative X.metric μ hμ Ω) B)
    (f : ℝ → FixedPivot μ Ω) (uE : ℝ → DirichletEnergy X.metric μ hμ Ω)
    (wE : ℝ → EnergyDual (DirichletEnergy X.metric μ hμ Ω)) (A : ℝ → FixedPivot μ Ω)
    (hSol : VariationalSolution μ Ω S (dirichletL2 X.metric μ hμ Ω) B f uE wE A)
    (hSrc : ∀ᵐ t ∂volume.restrict (Ioo 0 S), ∀ᵐ x ∂μ.restrict Ω,
      0 ≤ f t x ∧ f t x ≤ source X h x t)
    (c : Pt X) {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω)
    {u uc : Point n → ℝ} (hu : MemLp u 2 (productVolume O (Ioo 0 S)))
    (huc : ContDiffOn ℝ ∞ uc (O ×ˢ Ioo 0 S))
    (hAE : u =ᵐ[productVolume O (Ioo 0 S)] uc)
    (hSlices : ∀ᵐ t ∂volume.restrict (Ioo 0 S),
      (fun z => u (z,t)) =ᵐ[volume.restrict O]
        scalarEnergy_chartRestrictionCLM X.metric μ hμ c hO hOC hOt (scalarEnergyL2 X.metric μ hμ (uE t).val)) :
    (∀ q ∈ O ×ˢ Ioo 0 S, 0 ≤ uc q ∧ uc q ≤ ρ (chartInv c q.1) q.2) ∧
    (∀ Z : Set (Space n), IsOpen Z → IsCompact (closure Z) → closure Z ⊆ O →
      ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ Z, ∀ t ∈ Ioo 0 S, |uc (x,t)| ≤ D*t) := by
  have hLo := variationalSolution_nonnegative X.metric X.kahler_metric μ hμ Ω hΩ h hS B hForm
    f uE wE A hSol (hSrc.mono (fun _ ht => ht.mono (fun _ hx => hx.1)))
  have hUp := flow_variationalSolution_le_rho X o h U P ρ hloc μ hμ Ω K hΩ hK hΩK hS B hForm
    f uE wE A hSol (hSrc.mono (fun _ ht => ht.mono (fun _ hx => hx.2)))
  have ha : ∀ᵐ t ∂volume.restrict (Ioo 0 S), ∀ᵐ x ∂μ.restrict Ω,
      0 ≤ A t x ∧ A t x ≤ ρ x t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    filter_upwards [hLo t (Ioo_subset_Icc_self ht),hUp t (Ioo_subset_Icc_self ht)] with x hl hu
    exact ⟨hl,hu⟩
  have hρ : ContDiffOn ℝ ∞ (fun q : Point n => ρ (chartInv c q.1) q.2) (chartTarget c ×ˢ Icc 0 S) :=
    (hloc.2.2.2.1 c).mono (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hρL : MemLp (fun q : Point n => ρ (chartInv c q.1) q.2) 2 (productVolume O (Ioo 0 S)) :=
    continuousOn_compactCylinder_memLp hO hOC (hρ.continuousOn.mono (prod_mono hOt (Subset.refl _)))
  have hb := smooth_supported_energy_chart_bounds X.metric μ hμ Ω hΩ.measurableSet c hO hOC hOt hMap
    uE A ρ hu hρL hSlices hSol.2.2.2.2.1 ha hAE huc.continuousOn
    (hρ.continuousOn.mono (prod_mono (subset_closure.trans hOt) Ioo_subset_Icc_self))
  exact ⟨hb,flow_chart_rho_dominated_compact_growth X o h U P ρ hloc hS c
    (subset_closure.trans hOt) hb⟩

end Yau.F04Proof
