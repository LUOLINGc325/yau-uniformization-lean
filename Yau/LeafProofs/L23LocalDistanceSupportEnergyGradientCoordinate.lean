import Yau.LeafProofs.L23LocalDistanceSupportEnergyMajorant

/-! Actual first density variation for the prescribed u-times-parallel variation field. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

theorem chartEnergy_parallelVariation_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (Z : ℝ × ℝ → ComplexVector n) (P : ℝ → ComplexVector n) (u : ℝ)
    (hZ : ContDiffAt ℝ 2 Z (0,u))
    (hz : Z (0,u) ∈ chartTarget c)
    (hvar : ∀ᶠ s in 𝓝 u, deriv (fun r => Z (r,s)) 0 = s • P s)
    (hP : HasDerivAt P (-chartChristoffelBilin h c (Z (0,u))
      (deriv (fun s => Z (0,s)) u) (P u)) u) :
    HasDerivAt (fun r => realMetricInChart h c (Z (r,u))
      (deriv (fun s => Z (r,s)) u) (deriv (fun s => Z (r,s)) u))
      (2*realMetricInChart h c (Z (0,u)) (deriv (fun s => Z (0,s)) u) (P u)) 0 := by
  let T := fun p : ℝ × ℝ => fderiv ℝ Z p (0,1)
  have HT : ContDiffAt ℝ 1 T (0,u) := (hZ.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hdiff : ∀ᶠ p in 𝓝 ((0,u) : ℝ × ℝ), DifferentiableAt ℝ Z p :=
    (hZ.eventually (by norm_num)).mono (fun p hp => hp.differentiableAt (by norm_num))
  have htime : ∀ᶠ p in 𝓝 ((0,u) : ℝ × ℝ), HasDerivAt (fun s => Z (p.1,s)) (T p) p.2 := by
    filter_upwards [hdiff] with p hp
    exact hp.hasFDerivAt.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have HT0 : T (0,u) = deriv (fun s => Z (0,s)) u := htime.self_of_nhds.deriv.symm
  have HM := mixed_parameter_velocity_hasDerivAt hZ htime
  have HJ : HasDerivAt (fun s => deriv (fun r => Z (r,s)) 0)
      (P u+u • (-chartChristoffelBilin h c (Z (0,u)) (deriv (fun s => Z (0,s)) u) (P u))) u := by
    simpa only [one_smul,id_eq,add_comm] using ((hasDerivAt_id u).smul hP).congr_of_eventuallyEq hvar
  have HMvalue := HM.unique HJ
  have HTr : HasDerivAt (fun r => T (r,u))
      (P u+u • (-chartChristoffelBilin h c (Z (0,u)) (deriv (fun s => Z (0,s)) u) (P u))) 0 := by
    have H := ((HT.comp (0 : ℝ) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)).hasDerivAt
    change HasDerivAt (fun r => T (r,u)) (deriv (fun r => T (r,u)) 0) 0 at H
    rwa [HMvalue] at H
  have HZr : HasDerivAt (fun r => Z (r,u)) (u • P u) 0 := by
    have H := ((hZ.comp (0 : ℝ) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)).hasDerivAt
    change HasDerivAt (fun r => Z (r,u)) (deriv (fun r => Z (r,u)) 0) 0 at H
    rwa [hvar.self_of_nhds] at H
  have H := chartEnergy_variation_hasDerivAt h hh c hz HZr HTr
  rw [HT0] at H
  have Hcancel : P u+u • (-chartChristoffelBilin h c (Z (0,u)) (deriv (fun s => Z (0,s)) u) (P u))+
      chartChristoffelBilin h c (Z (0,u)) (u • P u) (deriv (fun s => Z (0,s)) u) = P u := by
    rw [map_smul,ContinuousLinearMap.smul_apply,chartChristoffelBilin_symm h c (Z (0,u)) (P u)]
    simp only [smul_neg]
    abel
  rw [Hcancel] at H
  have Hline : ContinuousAt (fun r : ℝ => (r,u)) 0 := continuousAt_id.prodMk continuousAt_const
  apply H.congr_of_eventuallyEq
  filter_upwards [Hline.eventually htime] with r hr
  rw [← hr.deriv]

end Yau.LeafProofs.L23Aux
