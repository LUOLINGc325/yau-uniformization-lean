import Yau.Proofs.F03ExhaustionCore
import Yau.Proofs.F03L2RestrictionPairing

/-! Genuine supported resolvents converge in the original ambient energy norm. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ Ω) := dirichletEnergy_completeSpace g μ hμ Ω

def dirichletAmbientResolventEnergy (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) :
    Lp ℝ 2 μ →L[ℝ] ScalarEnergySpace g μ hμ :=
  (dirichletEnergySubmodule g μ hμ Ω).subtypeL.comp
    ((dirichletL2 g μ hμ Ω).adjoint.comp (l2Restriction μ Ω))

theorem dirichletAmbientResolventEnergy_eq_projection (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (f : Lp ℝ 2 μ) :
    dirichletAmbientResolventEnergy g μ hμ Ω f=
      (dirichletEnergySubmodule g μ hμ Ω).starProjection ((scalarEnergyL2 g μ hμ).adjoint f) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((dirichletL2 g μ hμ Ω).adjoint (l2Restriction μ Ω f)).property
  intro w hw
  let v : DirichletEnergy g μ hμ Ω := ⟨w,hw⟩
  have hleft : inner ℝ ((scalarEnergyL2 g μ hμ).adjoint f) w=
      inner ℝ f (scalarEnergyL2 g μ hμ w) := ContinuousLinearMap.adjoint_inner_left _ _ _
  have hright : inner ℝ
      (((dirichletL2 g μ hμ Ω).adjoint (l2Restriction μ Ω f)) : ScalarEnergySpace g μ hμ) w=
      inner ℝ (l2Restriction μ Ω f) (dirichletL2 g μ hμ Ω v) := by
    change inner ℝ ((dirichletL2 g μ hμ Ω).adjoint (l2Restriction μ Ω f)) v=_
    exact ContinuousLinearMap.adjoint_inner_left _ _ _
  have hp := l2ZeroExtension_inner_left μ Ω hΩ (dirichletL2 g μ hμ Ω v) f
  rw [dirichletL2_zeroExtension g μ hμ Ω hΩ v] at hp
  have hpair : inner ℝ f (scalarEnergyL2 g μ hμ w)=
      inner ℝ (l2Restriction μ Ω f) (dirichletL2 g μ hμ Ω v) := by
    calc
      _ = inner ℝ (scalarEnergyL2 g μ hμ w) f := real_inner_comm _ _
      _ = inner ℝ (dirichletL2 g μ hμ Ω v) (l2Restriction μ Ω f) := hp
      _ = _ := real_inner_comm _ _
  rw [inner_sub_left,hleft,hright,hpair,sub_self]

theorem dirichletAmbientResolventEnergy_exhaustion_tendsto (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O : ℕ → Set M.Carrier} (hO : SmoothExhaustion O) (f : Lp ℝ 2 μ) :
    Tendsto (fun j => dirichletAmbientResolventEnergy g μ hμ (O j) f) atTop
      (𝓝 ((scalarEnergyL2 g μ hμ).adjoint f)) := by
  let u := (scalarEnergyL2 g μ hμ).adjoint f
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [smoothExhaustion_energy_approx g μ hμ hO u hε] with j hj
  obtain ⟨v,hv⟩ := hj
  calc
    dist (dirichletAmbientResolventEnergy g μ hμ (O j) f) u =
        dist u ((dirichletEnergySubmodule g μ hμ (O j)).starProjection u) := by
      rw [dirichletAmbientResolventEnergy_eq_projection g μ hμ (O j) (hO.1 j).1.measurableSet f,
        dist_comm]
    _ = Metric.infDist u (dirichletEnergySubmodule g μ hμ (O j)) :=
      Submodule.dist_starProjection_eq_infDist _ _
    _ ≤ dist u v.val := Metric.infDist_le_dist_of_mem v.property
    _ < ε := by rw [dist_eq_norm,norm_sub_rev];exact hv

end Yau.Proofs.F03Aux
