import Yau.Proofs.V03BoundaryCostSmooth
import Yau.Proofs.V03RadialTrace
import Yau.Proofs.V03AverageContinuity
import Yau.Proofs.V03RadialEnergy

/-! Radial convergence of the actual boundary cost and penalized
functional, for every real penalty coefficient. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem boundaryCost_radial_tendsto {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    Tendsto (fun r : ℝ => boundaryCost d j (radialVariationDisc F r))
      (𝓝[Set.Icc 0 1] 1) (𝓝 (boundaryCost d j F)) := by
  have hUniform := radial_trace_tendstoUniformlyOn (b := boundaryDensity d j F)
    (fun θ => (admissible_boundaryDensity_contDiffWithinAt hd hF
      (circlePoint_mem_closedBall θ) (hF.2.2.2.2.2.2.2.1 θ)).continuousWithinAt)
  have hC := (radial_boundaryDensity_contDiff_eventually hd hF).mono fun r hr => hr.continuous
  have hbase := (admissible_boundaryDensity_circle_contDiff hd hF).continuous
  exact circleAverage_tendsto_of_uniform
    (fun r : ℝ => fun θ => boundaryDensity d j F ((r : ℂ) * circlePoint θ))
    (fun θ => boundaryDensity d j F (circlePoint θ)) hC hbase hUniform

theorem penalizedFunctional_radial_tendsto {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (ε : ℝ) :
    Tendsto (fun r : ℝ => penalizedFunctional d j ε (radialVariationDisc F r))
      (𝓝[Set.Icc 0 1] 1) (𝓝 (penalizedFunctional d j ε F)) := by
  have hb := boundaryCost_radial_tendsto hd hF
  have he := (radial_energy_toReal_tendsto hd hF).const_mul ε
  have ht := (hb.add he).sub_const (d.test (F.f 0) F.s)
  simpa only [penalizedFunctional, radialVariationDisc, mul_zero] using ht

end Yau.Blueprint.V03Proof
