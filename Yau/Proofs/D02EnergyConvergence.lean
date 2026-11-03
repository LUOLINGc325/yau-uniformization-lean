import Yau.Proofs.D02HolomorphicLimit
import Yau.Proofs.D02AreaDensity

/-! First-derivative convergence in one genuine chart yields convergence
of the original Hermitian energy density, for the same target metric. -/

open scoped Topology Manifold ContDiff
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

theorem physicalCurveDerivative_eq_fixed_chart {n : ℕ} {M : ComplexManifold n}
    {f : ℂ → M.Carrier} {z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ) (ComplexModel n) f z)
    (p : M.Carrier) (hp : f z ∈ (extChartAt (ComplexModel n) p).source) :
    physicalCurveDerivative f z = chartVec p (f z) (deriv (fun w => chartPt p (f w)) z) := by
  have hca : MDifferentiableAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) (chartPt p) (f z) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hp)
  have hc := mfderiv_comp_apply z hca hf ((tangentSpaceCastModel 𝓘(ℂ, ℂ) z).symm 1)
  rw [mfderiv_eq_fderiv] at hc
  have hcoords : tangentCoords p (f z) (physicalCurveDerivative f z) =
      deriv (fun w => chartPt p (f w)) z := by
    rw [← fderiv_apply_one_eq_deriv]
    exact hc.symm
  rw [← hcoords]
  exact (chartVec_tangentCoords p (f z) hp _).symm

def curveEnergyDensity {n : ℕ} {M : ComplexManifold n} (g : HermitianField M)
    (f : ℂ → M.Carrier) (z : ℂ) : ℝ :=
  2 * hermitianNormSq (g (f z)) (physicalCurveDerivative f z)

theorem curveEnergyDensity_eq_chart {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) {f : ℂ → M.Carrier} {z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ) (ComplexModel n) f z)
    (p : M.Carrier) (hp : f z ∈ (extChartAt (ComplexModel n) p).source) :
    curveEnergyDensity g f z = 2 * hermitianChartNormSq g p (chartPt p (f z))
      (deriv (fun w => chartPt p (f w)) z) := by
  rw [curveEnergyDensity, physicalCurveDerivative_eq_fixed_chart hf p hp,
    hermitianChartNormSq_at_point g p (f z) hp]

theorem curveEnergyDensity_tendsto {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {O : Set ℂ} (hO : IsOpen O)
    (fs : ℕ → ℂ → M.Carrier) (f : ℂ → M.Carrier)
    (hfs : ∀ j, ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ (fs j) O)
    (hf : ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f O)
    (hconv : letI := L12Aux.inducedMetricSpace g; TendstoLocallyUniformlyOn fs f atTop O)
    {x : ℂ} (hx : x ∈ O) :
    Tendsto (fun j => curveEnergyDensity g.form (fs j) x) atTop (𝓝 (curveEnergyDensity g.form f x)) := by
  letI := L12Aux.inducedMetricSpace g
  obtain ⟨R, hR, _, _, hchart, _, _, hderiv⟩ :=
    holomorphic_limit_fixed_chart g hO fs f hfs hf.continuousOn hconv hx
  let p := f x
  have htarget : chartPt p (f x) ∈ chartTarget p := mem_extChartAt_target p
  have hpair : Tendsto (fun j => (chartPt p (fs j x), deriv (fun w => chartPt p (fs j w)) x)) atTop
      (𝓝 (chartPt p (f x), deriv (fun w => chartPt p (f w)) x)) := by
    apply Tendsto.prodMk_nhds
    · exact ((continuousOn_extChartAt (I := ComplexModel n) p).continuousAt
        (extChartAt_source_mem_nhds p)).tendsto.comp (hconv.tendsto_at hx)
    · exact hderiv.tendsto_at (mem_ball_self hR)
  have hpt : (chartPt p (f x), deriv (fun w => chartPt p (f w)) x) ∈ cotangentTarget p :=
    ⟨htarget, mem_univ _⟩
  have hopen : IsOpen (cotangentTarget p) :=
    (isOpen_extChartAt_target (I := ComplexModel n) p).prod isOpen_univ
  have hQ : ContinuousAt (fun q : CotangentCoord n => hermitianChartNormSq g.form p q.1 q.2)
      (chartPt p (f x), deriv (fun w => chartPt p (f w)) x) :=
    (hermitianChartNormSq_contDiffOn g p).continuousOn.continuousAt (hopen.mem_nhds hpt)
  have ht := (hQ.tendsto.comp hpair).const_mul (2 : ℝ)
  have hfinal := curveEnergyDensity_eq_chart g.form
    ((hf.contMDiffAt (hO.mem_nhds hx)).mdifferentiableAt (by simp)) p (mem_extChartAt_source p)
  have hseq : (fun j => curveEnergyDensity g.form (fs j) x) =ᶠ[atTop]
      (fun j => 2 * hermitianChartNormSq g.form p (chartPt p (fs j x))
        (deriv (fun w => chartPt p (fs j w)) x)) := by
    filter_upwards [hchart] with j hj
    exact curveEnergyDensity_eq_chart g.form
      (((hfs j).contMDiffAt (hO.mem_nhds hx)).mdifferentiableAt (by simp)) p
      (hj (mem_closedBall_self hR.le))
  simpa only [hfinal] using ht.congr' hseq.symm

end Yau.NodeProofs.D02Aux
