import Yau.LeafProofs.L12MinimizingDomain

/-! Uniqueness of a minimizing radial vector before its genuine cut endpoint. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

set_option backward.isDefEq.respectTransparency false in
/-- A radial geodesic minimizing beyond its endpoint is the unique minimizing
radial geodesic to that endpoint. -/
theorem realExponentialMap_eq_imp_eq_of_mem_strictMinimizingVectors
    (g : SmoothMetric M) (x : M.Carrier)
    {v w : TangentSpace 𝓘(ℝ, ComplexVector n) x}
    (hv : v ∈ realStrictMinimizingVectors g x)
    (hw : w ∈ realMinimizingVectors g x)
    (he : realExponentialMap g x v = realExponentialMap g x w) : v = w := by
  letI := manifold_realSmooth M
  letI := inducedMetricSpace g
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  have hvmin := realStrictMinimizingVectors_subset g x hv
  change dist x (realExponentialMap g x v) = ‖v‖ at hvmin
  change dist x (realExponentialMap g x w) = ‖w‖ at hw
  have hnorm : ‖w‖ = ‖v‖ := by rw [← hw, ← he, hvmin]
  by_cases hv0 : ‖v‖ = 0
  · have hve : v = 0 := norm_eq_zero.mp hv0
    have hwe : w = 0 := norm_eq_zero.mp (hnorm.trans hv0)
    exact hve.trans hwe.symm
  have hL : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
  obtain ⟨q, hq⟩ := hv
  let s : ℝ := q.val
  have hs : 1 < s := by
    dsimp only [s]
    exact_mod_cast q.property
  have hbig : dist x (realExponentialMap g x (s • v)) = s * ‖v‖ := by
    change dist x (realExponentialMap g x (s • v)) = ‖s • v‖ at hq
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hs)] using hq
  let pV : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨x, v⟩
  let pW : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨x, w⟩
  let PV := realGeodesicFlow g pV 1
  let PW := realGeodesicFlow g pW 1
  let b := PV.proj
  let V : TangentSpace 𝓘(ℝ, ComplexVector n) b := PV.2
  let W : TangentSpace 𝓘(ℝ, ComplexVector n) b :=
    realFrameCLM b b (realTangentCoords b PW.proj PW.2)
  have hbase : PW.proj = b := he.symm
  have hPW : PW = (⟨b, W⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := by
    apply realTangentPoint_eq_of_coords hbase
    · rw [hbase]
      exact mem_chart_source _ _
    · exact (realTangentCoords_realFrameCLM b b (mem_chart_source _ _) _).symm
  have hV : ‖V‖ = ‖v‖ := realGeodesicFlow_velocity_norm g pV 1
  have hW : ‖W‖ = ‖v‖ :=
    (realNorm_of_totalSpace_eq g hPW).symm.trans
      ((realGeodesicFlow_velocity_norm g pW 1).trans hnorm)
  let u := ‖v‖⁻¹ • W
  let z := ‖v‖⁻¹ • V
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hL, hW, inv_mul_cancel₀ hv0]
  have hz : ‖z‖ = 1 := by
    dsimp only [z]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hL, hV, inv_mul_cancel₀ hv0]
  have hcorner : ∀ᶠ h : ℝ in 𝓝[>] 0,
      inducedDistance g.form (realExponentialMap g b ((-h) • u))
        (realExponentialMap g b (h • z)) = 2 * h := by
    have hmargin : 0 < (s - 1) * ‖v‖ := mul_pos (sub_pos.mpr hs) hL
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hL),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hmargin)] with h hh hhL hhs
    change 0 < h at hh
    change h < ‖v‖ at hhL
    change h < (s - 1) * ‖v‖ at hhs
    have ht : 0 < h / ‖v‖ := div_pos hh hL
    have ht1 : h / ‖v‖ < 1 := (div_lt_one hL).mpr hhL
    have hts : h / ‖v‖ < s - 1 := (div_lt_iff₀ hL).mpr hhs
    let zBack := realExponentialMap g b ((-h) • u)
    let zForward := realExponentialMap g b (h • z)
    have hback : zBack = realExponentialMap g x ((1 - h / ‖v‖) • w) := by
      change realExponentialMap g b ((-h) • (‖v‖⁻¹ • W)) = _
      rw [smul_smul, realExponentialMap_smul]
      change (realGeodesicFlow g (⟨b, W⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
        (-h * ‖v‖⁻¹)).proj = _
      rw [← hPW, ← realGeodesicFlow_add, realExponentialMap_smul]
      congr 2
      ring
    have hforward : zForward = realExponentialMap g x ((1 + h / ‖v‖) • v) := by
      change realExponentialMap g (realGeodesicFlow g pV 1).proj
        (h • (‖v‖⁻¹ • (realGeodesicFlow g pV 1).2)) = _
      rw [smul_smul, realExponentialMap_centered_flow, realExponentialMap_smul]
      congr 2
    have hxback : dist x zBack ≤ (1 - h / ‖v‖) * ‖v‖ := by
      rw [hback]
      change inducedDistance g.form x (realExponentialMap g x ((1 - h / ‖v‖) • w)) ≤ _
      have hb := inducedDistance_realExponentialMap_le g x ((1 - h / ‖v‖) • w)
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht1), hnorm] using hb
    have htail : dist zForward (realExponentialMap g x (s • v)) ≤
        ‖v‖ * (s - (1 + h / ‖v‖)) := by
      rw [hforward]
      change inducedDistance g.form (realExponentialMap g x ((1 + h / ‖v‖) • v))
        (realExponentialMap g x (s • v)) ≤ _
      have hb := realExponentialMap_base_dist_le g x v (1 + h / ‖v‖) s
      simpa only [abs_of_pos (show 0 < s - (1 + h / ‖v‖) by linarith)] using hb
    have hcancel : h / ‖v‖ * ‖v‖ = h := div_mul_cancel₀ h hv0
    have hlow : 2 * h ≤ dist zBack zForward := by
      have h1 := dist_triangle x zBack (realExponentialMap g x (s • v))
      have h2 := dist_triangle zBack zForward (realExponentialMap g x (s • v))
      nlinarith
    have hbb : dist b zBack ≤ h := by
      change inducedDistance g.form b (realExponentialMap g b ((-h) • u)) ≤ h
      have hb := inducedDistance_realExponentialMap_le g b ((-h) • u)
      simpa only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hh, hu, mul_one] using hb
    have hbf : dist b zForward ≤ h := by
      change inducedDistance g.form b (realExponentialMap g b (h • z)) ≤ h
      have hb := inducedDistance_realExponentialMap_le g b (h • z)
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hh, hz, mul_one] using hb
    have hup : dist zBack zForward ≤ 2 * h := by
      have hb := dist_triangle zBack b zForward
      rw [dist_comm zBack b] at hb
      linarith
    exact le_antisymm hup hlow
  have huz : u = z := realExponential_no_corner g b u z hu hz hcorner
  have hWV : W = V := by
    have hh := congrArg (fun a : TangentSpace 𝓘(ℝ, ComplexVector n) b => ‖v‖ • a) huz
    simpa only [u, z, smul_smul, mul_inv_cancel₀ hv0, one_smul] using hh
  have hphase : PW = PV := by
    rw [hPW, hWV]
  have hinit : pW = pV := by
    have hh := congrArg (fun p => realGeodesicFlow g p (-1)) hphase
    simpa only [PW, PV, realGeodesicFlow_neg] using hh
  have hh := congrArg
    (fun p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => realTangentCoords x p.proj p.2) hinit
  simpa only [pW, pV, realTangentCoords_self] using hh.symm

theorem realExponentialMap_injOn_strictMinimizingVectors (g : SmoothMetric M) (x : M.Carrier) :
    Set.InjOn (realExponentialMap g x) (realStrictMinimizingVectors g x) := by
  intro v hv w hw he
  exact realExponentialMap_eq_imp_eq_of_mem_strictMinimizingVectors g x hv
    (realStrictMinimizingVectors_subset g x hw) he

end Yau.LeafProofs.L12Aux
