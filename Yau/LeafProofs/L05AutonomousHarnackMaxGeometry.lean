import Yau.LeafProofs.L05AutonomousHarnackMean

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def autoBoundaryDistance {n : ℕ} (z : Point n) : ℝ :=
  min (1-‖z.1‖) (Real.sqrt (z.2+1))

theorem autoBoundaryDistance_continuous (n : ℕ) : Continuous (autoBoundaryDistance (n := n)) := by
  unfold autoBoundaryDistance
  fun_prop

theorem autoBoundaryDistance_nonneg {n : ℕ} {z : Point n} (hz : z∈unitClosed n) :
    0≤ autoBoundaryDistance z := by
  apply le_min
  · have hh : ‖z.1‖≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
    linarith only [hh]
  · exact Real.sqrt_nonneg _

theorem autoBoundaryDistance_time {n : ℕ} {z : Point n} (hz : z∈unitClosed n) :
    (autoBoundaryDistance z)^2≤ z.2+1 := by
  have hD := autoBoundaryDistance_nonneg hz
  have htime : (-1 : ℝ)≤ z.2 := hz.2.1
  have hs := (sq_le_sq₀ hD (Real.sqrt_nonneg (z.2+1))).mpr (min_le_right (1-‖z.1‖) (Real.sqrt (z.2+1)))
  rwa [Real.sq_sqrt (by linarith only [htime])] at hs

theorem autoBoundaryDistance_half {n : ℕ} {z : Point n} (hz : z∈backward (1/2)) :
    1/2≤ autoBoundaryDistance z := by
  apply le_min
  · have hh : ‖z.1‖< 1/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hz.1
    linarith only [hh]
  · have ht : -(1/2 : ℝ)^2< z.2 := hz.2.1
    exact Real.le_sqrt_of_sq_le (by linarith only [ht] : (1/2 : ℝ)^2≤ z.2+1)

/-- The full closed backward cylinder stays inside the source and keeps a fixed fraction of D. -/
theorem autoBoundaryDistance_cylinder {n : ℕ} {z : Point n} (hz : z∈unitClosed n)
    {kappa : ℝ} (hk : 0< kappa) (hk1 : kappa< 1) (hD : 0< autoBoundaryDistance z) :
    autoClosed z.1 (kappa*autoBoundaryDistance z) z.2⊆unitClosed n ∧
    ∀ q∈autoClosed z.1 (kappa*autoBoundaryDistance z) z.2,
      (1-kappa)*autoBoundaryDistance z≤ autoBoundaryDistance q := by
  let D := autoBoundaryDistance z
  have hDz : D≤ 1-‖z.1‖ := min_le_left _ _
  have hDt : D^2≤ z.2+1 := autoBoundaryDistance_time hz
  have hB : 0< (1-kappa)*D := mul_pos (sub_pos.mpr hk1) hD
  have hbound (q : Point n) (hq : q∈autoClosed z.1 (kappa*D) z.2) :
      (1-kappa)*D≤ 1-‖q.1‖ ∧ ((1-kappa)*D)^2≤ q.2+1 := by
    have hdist : ‖q.1-z.1‖≤ kappa*D := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hq.1
    have hn := norm_add_le (q.1-z.1) z.1
    rw [sub_add_cancel] at hn
    have ht : z.2-(kappa*D)^2≤ q.2 := hq.2.1
    constructor
    · nlinarith only [hdist,hn,hDz]
    · have hp := mul_nonneg (mul_nonneg hk.le (sub_nonneg.mpr hk1.le)) (sq_nonneg D)
      nlinarith only [ht,hDt,hp]
  constructor
  · intro q hq
    have hh := hbound q hq
    constructor
    · change dist q.1 0≤ 1
      rw [dist_zero_right]
      linarith only [hh.1,hB.le]
    · change (-1 : ℝ)≤ q.2 ∧ q.2≤ 0
      constructor
      · nlinarith only [hh.2,sq_nonneg ((1-kappa)*D)]
      · exact hq.2.2.trans hz.2.2
  · intro q hq
    have hh := hbound q hq
    exact le_min hh.1 (Real.le_sqrt_of_sq_le hh.2)

/-- Compactness is used only to obtain an actual weighted maximum for each continuous w. -/
theorem auto_boundary_weight_maximizer {n : ℕ} {beta : ℝ} (hbeta : 0< beta)
    {w : Point n → ℝ} (hw : ContinuousOn w (unitClosed n)) :
    ∃ z∈unitClosed n, ∀ q∈unitClosed n,
      (autoBoundaryDistance q)^beta*max (w q) 0≤ (autoBoundaryDistance z)^beta*max (w z) 0 := by
  have hc : IsCompact (unitClosed n) := (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  have hn : (unitClosed n).Nonempty := by
    refine ⟨(0,0),?_⟩
    change dist (0 : Space n) 0≤ 1 ∧ (-1 : ℝ)≤ 0 ∧ (0 : ℝ)≤ 0
    simp only [dist_self]
    norm_num
  have hweight : ContinuousOn (fun q => (autoBoundaryDistance q)^beta*max (w q) 0) (unitClosed n) :=
    ((autoBoundaryDistance_continuous n).continuousOn.rpow_const (fun _ _ => Or.inr hbeta.le)).mul
      (hw.sup continuousOn_const)
  obtain ⟨z,hz,hm⟩ := hc.exists_isMaxOn hn hweight
  exact ⟨z,hz,hm⟩

/-- Explicit radius fraction chosen before the candidate and its weighted maximum. -/
theorem auto_harnack_kappa {beta eps : ℝ} (hbeta : 0< beta) (heps : 0< eps) :
    ∃ kappa : ℝ, 0< kappa ∧ kappa< 1 ∧ (1-kappa)^(-beta)=1+eps := by
  let t := (1+eps)^(-1/beta)
  have hbase : 1< 1+eps := by linarith only [heps]
  have ht : 0< t := Real.rpow_pos_of_pos (by linarith only [hbase] : 0< 1+eps) _
  have ht1 : t< 1 := Real.rpow_lt_one_of_one_lt_of_neg hbase (div_neg_of_neg_of_pos (by norm_num) hbeta)
  refine ⟨1-t,by linarith only [ht1],by linarith only [ht],?_⟩
  rw [sub_sub_cancel]
  dsimp only [t]
  rw [← Real.rpow_mul (by linarith only [hbase] : 0≤ 1+eps),
    show (-1/beta)*(-beta)=1 by field_simp [hbeta.ne'],Real.rpow_one]

/-- The genuine weighted maximum controls w on its actual D-scaled backward cylinder. -/
theorem auto_weighted_maximum_envelope {n : ℕ} {beta kappa : ℝ}
    (hbeta : 0< beta) (hk : 0< kappa) (hk1 : kappa< 1) {w : Point n → ℝ} {z : Point n}
    (hz : z∈unitClosed n) (hD : 0< autoBoundaryDistance z) (hwz : 0< w z)
    (hmax : ∀ q∈unitClosed n,
      (autoBoundaryDistance q)^beta*max (w q) 0≤ (autoBoundaryDistance z)^beta*max (w z) 0) :
    ∀ q∈autoClosed z.1 (kappa*autoBoundaryDistance z) z.2,
      w q≤ (1-kappa)^(-beta)*w z := by
  have hgeo := autoBoundaryDistance_cylinder hz hk hk1 hD
  have hDp : 0< (autoBoundaryDistance z)^beta := Real.rpow_pos_of_pos hD _
  have hBp : 0< (1-kappa)^beta := Real.rpow_pos_of_pos (sub_pos.mpr hk1) _
  intro q hq
  have hlo := Real.rpow_le_rpow (mul_nonneg (sub_nonneg.mpr hk1.le) hD.le) (hgeo.2 q hq) hbeta.le
  rw [Real.mul_rpow (sub_nonneg.mpr hk1.le) hD.le] at hlo
  have hh := (mul_le_mul_of_nonneg_right hlo (le_max_right (w q) 0)).trans (hmax q (hgeo.1 hq))
  rw [max_eq_left hwz.le] at hh
  have hs : (1-kappa)^beta*max (w q) 0≤ w z := by
    apply (mul_le_mul_iff_of_pos_left hDp).mp
    convert hh using 1
    ring
  calc
    w q ≤ max (w q) 0 := le_max_left _ _
    _ ≤ w z/((1-kappa)^beta) := (le_div_iff₀ hBp).mpr (by simpa only [mul_comm] using hs)
    _ = (1-kappa)^(-beta)*w z := by
      rw [Real.rpow_neg (sub_nonneg.mpr hk1.le),div_eq_mul_inv]
      ring

end Yau.LeafProofs.L05AutonomousAux
