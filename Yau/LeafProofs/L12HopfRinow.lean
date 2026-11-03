import Yau.LeafProofs.L12NormalDistance
import Yau.LeafProofs.L12NoCorner

/-! Genuine minimizing exponential realization for the original complete
length metric, using local Gauss minimality, exact radial points,
no corners, and continuous induction along the actual geodesic. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

theorem realGeodesicFlow_velocity_norm (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    ‖(realGeodesicFlow g p t).2‖ = ‖p.2‖ := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  have h := realGeodesicFlow_energy g p t
  rw [realTangentEnergy_eq_norm_sq, realTangentEnergy_eq_norm_sq] at h
  nlinarith [norm_nonneg (realGeodesicFlow g p t).2, norm_nonneg p.2]

theorem realGeodesicFlow_base_dist_le (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s t : ℝ) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => underlyingRealTangentNormedAddCommGroup g.form z
    inducedDistance g.form (realGeodesicFlow g p s).proj (realGeodesicFlow g p t).proj ≤
      ‖p.2‖ * |t - s| := by
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  have h := realGeodesicFlow_distFrom_le g (realGeodesicFlow g p s) (t - s)
  have heq : realGeodesicFlow g (realGeodesicFlow g p s) (t - s) = realGeodesicFlow g p t := by
    rw [← realGeodesicFlow_add, add_sub_cancel]
  rw [heq, realGeodesicFlow_energy, realTangentEnergy_eq_norm_sq, Real.sqrt_sq (norm_nonneg p.2)] at h
  exact h

theorem realExponentialMap_base_dist_le (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) (s t : ℝ) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    inducedDistance g.form (realExponentialMap g x (s • v)) (realExponentialMap g x (t • v)) ≤
      ‖v‖ * |t - s| := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  rw [realExponentialMap_smul, realExponentialMap_smul]
  exact realGeodesicFlow_base_dist_le g (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) s t

theorem realExponentialMap_centered_flow (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (s t : ℝ) :
    realExponentialMap g (realGeodesicFlow g p s).proj (t • (realGeodesicFlow g p s).2) =
      (realGeodesicFlow g p (s + t)).proj := by
  rw [realExponentialMap_smul, ← realGeodesicFlow_add]

theorem exists_initial_unit_realExponential_ray (g : SmoothMetric M) (x y : M.Carrier)
    (hD : 0 < inducedDistance g.form x y) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    ∃ u : TangentSpace 𝓘(ℝ, ComplexVector n) x, ‖u‖ = 1 ∧ ∃ a : ℝ,
      0 < a ∧ a < inducedDistance g.form x y ∧
      inducedDistance g.form (realExponentialMap g x (a • u)) y = inducedDistance g.form x y - a := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  obtain ⟨ρ, hρ, hlocal⟩ := exists_local_minimizing_realExponential g x
  obtain ⟨a, ha, haMin⟩ := exists_between (lt_min hρ hD)
  have haρ := haMin.trans_le (min_le_left _ _)
  have haD := haMin.trans_le (min_le_right _ _)
  obtain ⟨z, hxz, hzy⟩ := exists_exact_radial g x y ha.le haD.le
  obtain ⟨w, hwExp, hwNorm⟩ := hlocal z (hxz.trans_lt haρ)
  rw [hxz] at hwNorm
  let u := a⁻¹ • w
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha, hwNorm, inv_mul_cancel₀ ha.ne']
  have hscale : a • u = w := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  refine ⟨u, hu, a, ha, haD, ?_⟩
  rw [hscale, hwExp]
  exact hzy

/-- A minimizing radial equality continues forward on the same actual
unit-speed geodesic: exact radial points and no corners force the direction. -/
theorem realExponential_unit_ray_extend (g : SmoothMetric M) (x y : M.Carrier)
    (u : TangentSpace 𝓘(ℝ, ComplexVector n) x) (t : ℝ) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    ‖u‖ = 1 → 0 < t → t < inducedDistance g.form x y →
    inducedDistance g.form (realExponentialMap g x (t • u)) y = inducedDistance g.form x y - t →
    ∃ s ∈ Set.Ioc t (inducedDistance g.form x y),
      inducedDistance g.form (realExponentialMap g x (s • u)) y = inducedDistance g.form x y - s := by
  letI := manifold_realSmooth M
  letI := inducedMetricSpace g
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  intro hu ht htD htail
  let p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨x, u⟩
  let b := (realGeodesicFlow g p t).proj
  let ub := (realGeodesicFlow g p t).2
  rw [realExponentialMap_smul] at htail
  change dist b y = dist x y - t at htail
  have hub : ‖ub‖ = 1 := (realGeodesicFlow_velocity_norm g p t).trans hu
  obtain ⟨ρ, hρ, hlocal⟩ := exists_local_minimizing_realExponential g b
  obtain ⟨r, hr, hrMin⟩ := exists_between (lt_min hρ (sub_pos.mpr htD))
  have hrρ := hrMin.trans_le (min_le_left _ _)
  have hrD := hrMin.trans_le (min_le_right _ _)
  have hrby : r ≤ inducedDistance g.form b y := by change r ≤ dist b y; rw [htail]; exact hrD.le
  obtain ⟨q, hbq, hqy⟩ := exists_exact_radial g b y hr.le hrby
  obtain ⟨w, hwExp, hwNorm⟩ := hlocal q (hbq.trans_lt hrρ)
  rw [hbq] at hwNorm
  let v := r⁻¹ • w
  have hv : ‖v‖ = 1 := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hwNorm, inv_mul_cancel₀ hr.ne']
  have hqExp : realExponentialMap g b (r • v) = q := by
    dsimp only [v]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    exact hwExp
  have hqy' : dist q y = dist x y - t - r := by
    change dist q y = dist b y - r at hqy
    rwa [htail] at hqy
  have hcorner : ∀ᶠ h : ℝ in 𝓝[>] 0,
      inducedDistance g.form (realExponentialMap g b ((-h) • ub))
        (realExponentialMap g b (h • v)) = 2 * h := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)] with h hh hht hhr
    change 0 < h at hh
    change h < t at hht
    change h < r at hhr
    let zBack := realExponentialMap g b ((-h) • ub)
    let zForward := realExponentialMap g b (h • v)
    have hback : zBack = realExponentialMap g x ((t - h) • u) := by
      change realExponentialMap g (realGeodesicFlow g p t).proj
        ((-h) • (realGeodesicFlow g p t).2) = _
      rw [realExponentialMap_centered_flow, realExponentialMap_smul]
      congr 1
    have hxback : dist x zBack ≤ t - h := by
      rw [hback]
      change inducedDistance g.form x (realExponentialMap g x ((t - h) • u)) ≤ t - h
      have h := inducedDistance_realExponentialMap_le g x ((t - h) • u)
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hht), hu, mul_one] using h
    have hfq : dist zForward q ≤ r - h := by
      have h := realExponentialMap_base_dist_le g b v h r
      rw [hqExp, hv, one_mul, abs_of_pos (sub_pos.mpr hhr)] at h
      exact h
    have hlow : 2 * h ≤ dist zBack zForward := by
      have h1 := dist_triangle x zBack y
      have h2 := dist_triangle zBack zForward y
      have h3 := dist_triangle zForward q y
      linarith
    have hbb : dist b zBack ≤ h := by
      change inducedDistance g.form b (realExponentialMap g b ((-h) • ub)) ≤ h
      have h := inducedDistance_realExponentialMap_le g b ((-h) • ub)
      simpa only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hh, hub, mul_one] using h
    have hbf : dist b zForward ≤ h := by
      change inducedDistance g.form b (realExponentialMap g b (h • v)) ≤ h
      have h := inducedDistance_realExponentialMap_le g b (h • v)
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hh, hv, mul_one] using h
    have hup : dist zBack zForward ≤ 2 * h := by
      have h := dist_triangle zBack b zForward
      rw [dist_comm zBack b] at h
      linarith
    exact le_antisymm hup hlow
  have huv : ub = v := realExponential_no_corner g b ub v hub hv hcorner
  have hqNext : realExponentialMap g x ((t + r) • u) = q := by
    rw [realExponentialMap_smul, realGeodesicFlow_add]
    change (realGeodesicFlow g (realGeodesicFlow g p t) r).proj = q
    rw [← realExponentialMap_smul]
    change realExponentialMap g b (r • ub) = q
    rw [huv]
    exact hqExp
  refine ⟨t + r, ⟨by linarith, by linarith⟩, ?_⟩
  rw [hqNext]
  change dist q y = dist x y - (t + r)
  linarith

/-- Genuine Hopf--Rinow realization for the original project length
metric: every point is reached by the actual complete exponential with
physical initial norm equal to its original length distance. -/
theorem exists_minimizing_realExponential (g : SmoothMetric M) (x y : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    ∃ v : TangentSpace 𝓘(ℝ, ComplexVector n) x,
      realExponentialMap g x v = y ∧ ‖v‖ = inducedDistance g.form x y := by
  letI := manifold_realSmooth M
  letI := inducedMetricSpace g
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentInnerProductSpace g.form z
  by_cases hxy : x = y
  · subst y
    refine ⟨0, realExponentialMap_zero g x, ?_⟩
    rw [norm_zero]
    exact (g.induced_distance_eq_zero.mpr rfl).symm
  have hD : 0 < inducedDistance g.form x y := by
    change 0 < dist x y
    exact dist_pos.mpr hxy
  let D := inducedDistance g.form x y
  obtain ⟨u, hu, a, ha, haD, hstart⟩ := exists_initial_unit_realExponential_ray g x y hD
  let γ := fun t : ℝ => realExponentialMap g x (t • u)
  let S : Set ℝ := {t | inducedDistance g.form (γ t) y = D - t}
  have hγ : Continuous γ := (realExponentialMap_radial_contMDiff g x u).continuous
  have hdist : Continuous (fun t => inducedDistance g.form (γ t) y) :=
    hγ.dist continuous_const
  have hS : IsClosed S := isClosed_eq hdist (continuous_const.sub continuous_id)
  have hEnd : D ∈ S :=
    (hS.inter isClosed_Icc).mem_of_ge_of_forall_exists_gt hstart haD.le (by
      intro t ht
      obtain ⟨s, hs, hse⟩ := realExponential_unit_ray_extend g x y u t hu
        (ha.trans_le ht.2.1) ht.2.2 ht.1
      exact ⟨s, hse, hs⟩)
  have heq : γ D = y := by
    apply g.induced_distance_eq_zero.mp
    simpa only [S, Set.mem_setOf_eq, sub_self] using hEnd
  refine ⟨D • u, heq, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hD, hu, mul_one]

theorem realExponentialMap_surjective (g : SmoothMetric M) (x : M.Carrier) :
    Function.Surjective (realExponentialMap g x) := by
  intro y
  obtain ⟨v, hv, _⟩ := exists_minimizing_realExponential g x y
  exact ⟨v, hv⟩

/-- The genuine distance ball is exactly the image of the physical
initial-velocity ball under the actual complete exponential. -/
theorem distBall_eq_realExponential_image_ball (g : SmoothMetric M) (x : M.Carrier)
    {r : ℝ} (hr : 0 < r) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    distBall g.form x r = realExponentialMap g x '' Metric.ball (0 : TangentSpace 𝓘(ℝ, ComplexVector n) x) r := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  ext y
  constructor
  · intro hy
    change ENNReal.ofReal (inducedDistance g.form x y) < ENNReal.ofReal r at hy
    have hd := (ENNReal.ofReal_lt_ofReal_iff hr).mp hy
    obtain ⟨v, hv, hnorm⟩ := exists_minimizing_realExponential g x y
    refine ⟨v, ?_, hv⟩
    simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hd
  · rintro ⟨v, hv, rfl⟩
    have hn : ‖v‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hv
    change ENNReal.ofReal (inducedDistance g.form x (realExponentialMap g x v)) < ENNReal.ofReal r
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr ((inducedDistance_realExponentialMap_le g x v).trans_lt hn)

theorem closedDistanceBall_eq_realExponential_image (g : SmoothMetric M) (x : M.Carrier) (R : ℝ) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    {y | inducedDistance g.form x y ≤ R} =
      realExponentialMap g x '' {v : TangentSpace 𝓘(ℝ, ComplexVector n) x | ‖v‖ ≤ R} := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  ext y
  constructor
  · intro hy
    obtain ⟨v, hv, hnorm⟩ := exists_minimizing_realExponential g x y
    exact ⟨v, by change ‖v‖ ≤ R; rw [hnorm]; exact hy, hv⟩
  · rintro ⟨v, hv, rfl⟩
    exact (inducedDistance_realExponentialMap_le g x v).trans hv

end Yau.LeafProofs.L12Aux
