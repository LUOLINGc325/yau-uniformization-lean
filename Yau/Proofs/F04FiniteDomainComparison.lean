import Yau.Proofs.F04RegionalComparison
import Yau.Proofs.F04RegionalContinuity
import Yau.Proofs.F04VariationalRestriction

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Proofs.F03Aux Yau.MassTargetStatements Yau.HeatConcreteBindings
variable {n : ℕ}

local instance (X : KahlerManifold n) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (O : Set (Pt X)) :
    CompleteSpace (DirichletEnergy X.metric μ hμ O) := dirichletEnergy_completeSpace X.metric μ hμ O

/-- Genuine finite-domain physical potentials are ordered across nested
 domains and ordered cutoff sources. This uses the original smaller-domain
 weak trace on its larger horizon, actually restricts it, and compares with
 a constructed interior cutoff of the larger classical potential. -/
theorem finite_classical_potential_domain_source_le
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O Γ : Set (Pt X)) (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hΓ : IsOpen Γ) (hOΓ : closure O ⊆ Γ)
    {T C shift : ℝ} (hT : 0 < T)
    (B : ℝ → DirichletEnergy X.metric μ hμ O →L[ℝ] EnergyDual (DirichletEnergy X.metric μ hμ O))
    (hForm : IntrinsicFormBinding X.metric.form μ O h (2*T) C (1/2) shift
      (dirichletL2 X.metric μ hμ O) (energyRepresentative X.metric μ hμ O) B)
    (f : ℝ → FixedPivot μ O) (u : ℝ → DirichletEnergy X.metric μ hμ O)
    (w : ℝ → EnergyDual (DirichletEnergy X.metric μ hμ O)) (A : ℝ → FixedPivot μ O)
    (hSol : VariationalSolution μ O (2*T) (dirichletL2 X.metric μ hμ O) B f u w A)
    (q r : Pt X → ℝ) (hqr : ∀ x, q x ≤ r x)
    (hF : ∀ t, (f t : Pt X → ℝ) =ᵐ[μ.restrict O]
      (fun x => q x * source X h x (timeClamp (2*T) (by positivity) t)))
    (v z : STF X)
    (hv : ∀ c, ContDiffOn ℝ ∞ (fun p : Yau.Parabolic.Point n => v (chartInv c p.1) p.2)
      ((chartTarget c ∩ chartInv c ⁻¹' O) ×ˢ Icc 0 T))
    (hTrace : ∀ t ∈ Icc 0 T, (fun x => v x t) =ᵐ[μ.restrict O] (A t : Pt X → ℝ))
    (hvOff : ∀ x ∉ O, ∀ t, v x t = 0)
    (hz : ∀ c, ContDiffOn ℝ ∞ (fun p : Yau.Parabolic.Point n => z (chartInv c p.1) p.2)
      ((chartTarget c ∩ chartInv c ⁻¹' Γ) ×ˢ Icc 0 T))
    (hz0 : ∀ x t, t ∈ Icc 0 T → 0 ≤ z x t)
    (hPDE : ∀ x ∈ Γ, ∀ t ∈ Icc 0 T, heatOp h (Icc 0 T) z x t = r x * source X h x t) :
    ∀ x t, t ∈ Icc 0 T → v x t ≤ z x t := by
  have hTS : T ≤ 2*T := by linarith
  have hFormT := intrinsicFormBinding_restrict_horizon X.metric.form μ O h hTS
    (dirichletL2 X.metric μ hμ O) (energyRepresentative X.metric μ hμ O) B hForm
  have hSolT := variationalSolution_restrict_horizon μ O hTS
    (dirichletL2 X.metric μ hμ O) B f u w A hSol
  have hSrc : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ᵐ x ∂μ.restrict O,
      f t x ≤ heatOp h (Icc 0 T) z x t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htC := Ioo_subset_Icc_self ht
    have ht2 : t ∈ Icc 0 (2*T) := ⟨htC.1,htC.2.trans hTS⟩
    filter_upwards [hF t,ae_restrict_mem hO.measurableSet] with x hfx hx
    rw [hfx,timeClamp_eq_of_mem (2*T) (by positivity) ht2,hPDE x (hOΓ (subset_closure hx)) t htC]
    exact mul_le_mul_of_nonneg_right (hqr x) (source_nonneg o h U P ρ hloc x t htC.1)
  have hCompare := flow_variationalSolution_le_regional X o h U P ρ hloc μ hμ O Γ hO hOC hΓ hOΓ hT
    B hFormT f u w A hSolT z hz hz0 hSrc
  have hvc := smooth_regional_continuousOn hv
  have hzc := smooth_regional_continuousOn hz
  intro x t ht
  by_cases hx : x ∈ O
  · have hOrder : (fun y => v y t) ≤ᵐ[μ.restrict O] (fun y => z y t) := by
      filter_upwards [hTrace t ht,hCompare t ht] with y hvy hay
      rw [hvy]
      exact hay
    have hvct : ContinuousOn (fun y => v y t) O :=
      hvc.comp (continuousOn_id.prodMk continuousOn_const) (fun y hy => ⟨hy,ht⟩)
    have hzct : ContinuousOn (fun y => z y t) O :=
      hzc.comp (continuousOn_id.prodMk continuousOn_const) (fun y hy => ⟨hOΓ (subset_closure hy),ht⟩)
    exact physical_continuousOn_le_of_ae_le X.metric μ hμ hO hvct hzct hOrder x hx
  · rw [hvOff x hx t]
    exact hz0 x t ht

end Yau.F04Proof
