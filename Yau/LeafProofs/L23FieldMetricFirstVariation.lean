import Yau.LeafProofs.L23FieldMetricNormalEndpoint

/-! Actual coordinate metric first variation and mixed parameter derivatives. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem realMetricInChart_pairing_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    {z a b : ℝ → ComplexVector n} {t : ℝ} {u a' b' : ComplexVector n}
    (hz : z t ∈ chartTarget c) (hzu : HasDerivAt z u t)
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => realMetricInChart h c (z s) (a s) (b s))
      (realMetricInChart h c (z t) (a'+chartChristoffelBilin h c (z t) u (a t)) (b t) +
        realMetricInChart h c (z t) (a t) (b'+chartChristoffelBilin h c (z t) u (b t))) t := by
  have hB := ((realMetricInChart_smooth h hh c).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hDB : HasDerivAt (fun s => realMetricInChart h c (z s))
      (fderiv ℝ (realMetricInChart h c) (z t) u) t := by
    simpa only [Function.comp_def] using hB.hasFDerivAt.comp_hasDerivAt t hzu
  have H := (hDB.clm_apply ha).clm_apply hb
  convert H using 1
  simp only [ContinuousLinearMap.add_apply,map_add]
  rw [realMetricInChart_connection_compatibility h hh c (z t) hz u (a t) (b t)]
  ring

theorem chartGeodesic_pairing_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    {z T J : ℝ → ComplexVector n} {t : ℝ} {J' : ComplexVector n}
    (hz : z t ∈ chartTarget c) (hzu : HasDerivAt z (T t) t)
    (hT : HasDerivAt T (-chartChristoffelBilin h c (z t) (T t) (T t)) t)
    (hJ : HasDerivAt J J' t) :
    HasDerivAt (fun s => realMetricInChart h c (z s) (T s) (J s))
      (realMetricInChart h c (z t) (T t) (J'+chartChristoffelBilin h c (z t) (T t) (J t))) t := by
  simpa only [neg_add_cancel,map_zero,ContinuousLinearMap.zero_apply,zero_add] using
    realMetricInChart_pairing_hasDerivAt h hh c hz hzu hT hJ

theorem chartEnergy_variation_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    {z T : ℝ → ComplexVector n} {t : ℝ} {J T' : ComplexVector n}
    (hz : z t ∈ chartTarget c) (hzu : HasDerivAt z J t) (hT : HasDerivAt T T' t) :
    HasDerivAt (fun s => realMetricInChart h c (z s) (T s) (T s))
      (2*realMetricInChart h c (z t) (T t)
        (T'+chartChristoffelBilin h c (z t) J (T t))) t := by
  have H := realMetricInChart_pairing_hasDerivAt h hh c hz hzu hT hT
  convert H using 1
  rw [realMetricInChart_symm h c (z t) (T'+chartChristoffelBilin h c (z t) J (T t)) (T t)]
  ring

theorem fixedMetric_velocityQuadratic_hasDerivAt
    (h : HermitianField M) (c : M.Carrier) (z v w : ComplexVector n) :
    HasDerivAt (fun r : ℝ => realMetricInChart h c z (v+r • w) (v+r • w))
      (2*realMetricInChart h c z v w) 0 := by
  have hv : HasDerivAt (fun r : ℝ => v+r • w) w 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v using 1 <;> simp
  have H := ((hasDerivAt_const (0 : ℝ) (realMetricInChart h c z)).clm_apply hv).clm_apply hv
  convert! H using 1
  simp only [zero_smul,add_zero,ContinuousLinearMap.zero_apply,zero_add]
  rw [realMetricInChart_symm h c z w v]
  ring

theorem mixed_parameter_velocity_hasDerivAt
    {Z T : ℝ × ℝ → ComplexVector n} {t : ℝ}
    (hZ : ContDiffAt ℝ 2 Z (0,t))
    (hT : ∀ᶠ p in 𝓝 ((0,t) : ℝ × ℝ),
      HasDerivAt (fun u => Z (p.1,u)) (T p) p.2) :
    HasDerivAt (fun u => deriv (fun r => Z (r,u)) 0)
      (deriv (fun r => T (r,t)) 0) t := by
  have hD : DifferentiableAt ℝ (fderiv ℝ Z) (0,t) :=
    (hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have Htime := hD.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t))
  have Hr := hD.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) t))
  have HJ : HasDerivAt (fun u => fderiv ℝ Z (0,u) (1,0))
      (fderiv ℝ (fderiv ℝ Z) (0,t) (0,1) (1,0)) t := by
    convert! Htime.clm_apply (hasDerivAt_const t ((1,0) : ℝ × ℝ)) using 1 <;> simp
  have HT : HasDerivAt (fun r => fderiv ℝ Z (r,t) (0,1))
      (fderiv ℝ (fderiv ℝ Z) (0,t) (1,0) (0,1)) 0 := by
    convert! Hr.clm_apply (hasDerivAt_const (0 : ℝ) ((0,1) : ℝ × ℝ)) using 1 <;> simp
  have hdiff : ∀ᶠ p in 𝓝 ((0,t) : ℝ × ℝ), DifferentiableAt ℝ Z p :=
    (hZ.eventually (by norm_num)).mono (fun p hp => hp.differentiableAt (by norm_num))
  have hlineR : ContinuousAt (fun r : ℝ => (r,t)) 0 := continuousAt_id.prodMk continuousAt_const
  have hlineT : ContinuousAt (fun u : ℝ => ((0 : ℝ),u)) t := continuousAt_const.prodMk continuousAt_id
  have hEqT : (fun r => fderiv ℝ Z (r,t) (0,1)) =ᶠ[𝓝 (0 : ℝ)] (fun r => T (r,t)) := by
    filter_upwards [hlineR.eventually hdiff,hlineR.eventually hT] with r hr hrT
    have H := hr.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t r).prodMk (hasDerivAt_id t))
    exact H.unique hrT
  have hEqJ : (fun u => fderiv ℝ Z (0,u) (1,0)) =ᶠ[𝓝 t]
      (fun u => deriv (fun r => Z (r,u)) 0) := by
    filter_upwards [hlineT.eventually hdiff] with u hu
    exact (hu.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) u))).deriv.symm
  have hvalue : fderiv ℝ (fderiv ℝ Z) (0,t) (0,1) (1,0) =
      deriv (fun r => T (r,t)) 0 := by
    calc
      _ = fderiv ℝ (fderiv ℝ Z) (0,t) (1,0) (0,1) :=
        hZ.isSymmSndFDerivAt (by norm_num) (0,1) (1,0)
      _ = deriv (fun r => fderiv ℝ Z (r,t) (0,1)) 0 := HT.deriv.symm
      _ = _ := hEqT.deriv_eq
  rw [hvalue] at HJ
  exact HJ.congr_of_eventuallyEq hEqJ.symm

end Yau.LeafProofs.L23Aux
