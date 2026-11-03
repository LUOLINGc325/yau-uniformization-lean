import Yau.Proofs.F04FlowSmoothComparison
import Yau.Proofs.F04PhysicalCutoffSmooth
import Yau.Proofs.F04PhysicalHeatLocality

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Proofs.F03Aux Yau.MassTargetStatements Yau.HeatConcreteBindings
variable {n : ℕ}

local instance (X : KahlerManifold n) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (O : Set (Pt X)) :
    CompleteSpace (DirichletEnergy X.metric μ hμ O) := dirichletEnergy_completeSpace X.metric μ hμ O

/-- An actual classical supersolution on a larger open domain dominates
 the original smaller-domain weak trace when the smaller closure is compact
 inside it. The globally smooth comparison profile is constructed with a
 genuine interior cutoff; no boundary regularity of the raw larger solution
 is assumed. -/
theorem flow_variationalSolution_le_regional
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O Γ : Set (Pt X)) (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hΓ : IsOpen Γ) (hOΓ : closure O ⊆ Γ)
    {T C α shift : ℝ} (hT : 0 < T)
    (B : ℝ → DirichletEnergy X.metric μ hμ O →L[ℝ] EnergyDual (DirichletEnergy X.metric μ hμ O))
    (hForm : IntrinsicFormBinding X.metric.form μ O h T C α shift
      (dirichletL2 X.metric μ hμ O) (energyRepresentative X.metric μ hμ O) B)
    (f : ℝ → FixedPivot μ O) (u : ℝ → DirichletEnergy X.metric μ hμ O)
    (w : ℝ → EnergyDual (DirichletEnergy X.metric μ hμ O)) (a : ℝ → FixedPivot μ O)
    (hSol : VariationalSolution μ O T (dirichletL2 X.metric μ hμ O) B f u w a)
    (v : STF X)
    (hv : ∀ c, ContDiffOn ℝ ∞ (fun p : Yau.Parabolic.Point n => v (chartInv c p.1) p.2)
      ((chartTarget c ∩ chartInv c ⁻¹' Γ) ×ˢ Icc 0 T))
    (hv0 : ∀ x t, t ∈ Icc 0 T → 0 ≤ v x t)
    (hSrc : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ᵐ x ∂μ.restrict O,
      f t x ≤ heatOp h (Icc 0 T) v x t) :
    ∀ t ∈ Icc 0 T, ∀ᵐ x ∂μ.restrict O, a t x ≤ v x t := by
  obtain ⟨ψ,N,hψ,_hcψ,hψΓ,hN,hON,_hNΓ,hψOne,hψRange⟩ :=
    exists_supported_smooth_cutoff (closure O) Γ hOC hΓ hOΓ
  let z : STF X := fun x t => ψ x * v x t
  have hz : SmoothSpaceTime z (Icc 0 T) := physical_spatial_cutoff_smooth hΓ hψ hψΓ hv
  have hz0 (x : Pt X) (t : ℝ) (ht : t ∈ Icc 0 T) : 0 ≤ z x t :=
    mul_nonneg (hψRange x).1 (hv0 x t ht)
  have he : EqOn (fun p : Pt X × ℝ => z p.1 p.2) (fun p => v p.1 p.2) (N ×ˢ Icc 0 T) := by
    intro p hp
    change ψ p.1 * v p.1 p.2 = v p.1 p.2
    rw [hψOne p.1 hp.1,one_mul]
  have hSup : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ᵐ x ∂μ.restrict O,
      f t x ≤ heatOp h (Icc 0 T) z x t := by
    filter_upwards [hSrc,ae_restrict_mem measurableSet_Ioo] with t ht htI
    filter_upwards [ht,ae_restrict_mem hO.measurableSet] with x hfx hx
    rw [physical_heatOp_congr_of_eqOn X h hN he (hON (subset_closure hx)) (Ioo_subset_Icc_self htI)]
    exact hfx
  have hc := flow_variationalSolution_le_smooth X o h U P ρ hloc μ hμ O (closure O) hO hOC
    subset_closure hT B hForm f u w a hSol z hz hz0 hSup
  intro t ht
  filter_upwards [hc t ht,ae_restrict_mem hO.measurableSet] with x hax hx
  change a t x ≤ ψ x * v x t at hax
  rwa [hψOne x (hON (subset_closure hx)),one_mul] at hax

end Yau.F04Proof
