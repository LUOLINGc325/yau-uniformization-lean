import Yau.LeafProofs.L16DeGiorgiSobolev

open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

local instance dgIntermediateValue_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance dgIntermediateValue_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- The three fixed cylinders of the direct intermediate-layer argument. -/
def dgEarlyCylinder (n : ℕ) : Set (Point n) := Metric.ball 0 1 ×ˢ Ioo (-3) (-2)
def dgLateCylinder (n : ℕ) : Set (Point n) := Metric.ball 0 1 ×ˢ Ioo (-1) 0
def dgMiddleCylinder (n : ℕ) : Set (Point n) := Metric.ball 0 (7/4) ×ˢ Ioo (-3) 0

/-- The first crossing of 2H and last preceding crossing of H give a genuine
closed interval on which the actual continuous mean remains in [H,2H]. -/
theorem dg_mean_crossing_interval {h : ℝ → ℝ} {s t H : ℝ} (hst : s < t)
    (hH : 0 < H) (hc : ContinuousOn h (Icc s t)) (hs : h s < H) (ht : 2*H < h t) :
    ∃ a b : ℝ, a ∈ Icc s t ∧ b ∈ Icc s t ∧ a < b ∧ h a = H ∧ h b = 2*H ∧
      ∀ r ∈ Icc a b, H ≤ h r ∧ h r ≤ 2*H := by
  let K₂ := Icc s t ∩ h ⁻¹' {2*H}
  have hK₂closed : IsClosed K₂ := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hK₂compact : IsCompact K₂ := isCompact_Icc.of_isClosed_subset hK₂closed inter_subset_left
  obtain ⟨b₀,hb₀,hb₀eq⟩ := intermediate_value_Icc hst.le hc
    (show 2*H ∈ Icc (h s) (h t) by constructor <;> linarith)
  obtain ⟨b,hb⟩ := hK₂compact.exists_isLeast (show K₂.Nonempty from ⟨b₀,hb₀,hb₀eq⟩)
  have hbtime : b ∈ Icc s t := hb.1.1
  have hbeq : h b = 2*H := hb.1.2
  have hcb : ContinuousOn h (Icc s b) := hc.mono (Icc_subset_Icc le_rfl hbtime.2)
  let K₁ := Icc s b ∩ h ⁻¹' {H}
  have hK₁closed : IsClosed K₁ := hcb.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hK₁compact : IsCompact K₁ := isCompact_Icc.of_isClosed_subset hK₁closed inter_subset_left
  obtain ⟨a₀,ha₀,ha₀eq⟩ := intermediate_value_Icc hbtime.1 hcb
    (show H ∈ Icc (h s) (h b) by constructor <;> linarith)
  obtain ⟨a,ha⟩ := hK₁compact.exists_isGreatest (show K₁.Nonempty from ⟨a₀,ha₀,ha₀eq⟩)
  have hatime : a ∈ Icc s b := ha.1.1
  have haeq : h a = H := ha.1.2
  have hab : a < b := lt_of_le_of_ne hatime.2 (by intro he; rw [he,hbeq] at haeq; linarith)
  refine ⟨a,b,⟨hatime.1,hatime.2.trans hbtime.2⟩,hbtime,hab,haeq,hbeq,?_⟩
  intro r hr
  constructor
  · by_contra hlow
    have hlow' : h r < H := lt_of_not_ge hlow
    obtain ⟨q,hq,hqeq⟩ := intermediate_value_Ioo hr.2
      (hc.mono (Icc_subset_Icc (hatime.1.trans hr.1) hbtime.2))
      (show H ∈ Ioo (h r) (h b) by constructor <;> linarith)
    have hqa : q ≤ a := ha.2 ⟨⟨hatime.1.trans (hr.1.trans hq.1.le),hq.2.le⟩,hqeq⟩
    linarith [hr.1,hq.1]
  · by_contra hhigh
    have hhigh' : 2*H < h r := lt_of_not_ge hhigh
    obtain ⟨q,hq,hqeq⟩ := intermediate_value_Ioo (hatime.1.trans hr.1)
      (hc.mono (Icc_subset_Icc le_rfl (hr.2.trans hbtime.2)))
      (show 2*H ∈ Ioo (h s) (h r) by constructor <;> linarith)
    have hbq : b ≤ q := hb.2 ⟨⟨hq.1.le,hq.2.le.trans (hr.2.trans hbtime.2)⟩,hqeq⟩
    linarith [hr.2,hq.2]

/-- A one-sided square-root increment forces a positive duration for an actual
upward crossing. No reverse time modulus is required. -/
theorem dg_crossing_duration {h : ℝ → ℝ} {a b H A : ℝ} (hab : a < b)
    (hH : 0 < H) (hA : 0 < A) (ha : h a = H) (hb : h b = 2*H)
    (hinc : h b-h a ≤ A*Real.sqrt (b-a)) : (H/A)^2 ≤ b-a := by
  have hh : H/A ≤ Real.sqrt (b-a) := (div_le_iff₀ hA).mpr (by rw [ha,hb] at hinc; nlinarith)
  have hs := pow_le_pow_left₀ (div_nonneg hH.le hA.le) hh 2
  simpa only [Real.sq_sqrt (sub_nonneg.mpr hab.le)] using hs

/-- Fubini for the real measure of actual measurable time slices of a finite
cylinder subset. In particular every slice integral used below is genuine. -/
theorem dg_integral_slice_measure {n : ℕ} {B : Set (Space n)} {J : Set ℝ} {S : Set (Point n)}
    (_hB : MeasurableSet B) (_hJ : MeasurableSet J) (hS : MeasurableSet S)
    (hBfin : volume B < ⊤) (hJfin : volume J < ⊤) (hsub : S ⊆ B ×ˢ J) :
    Integrable (fun t => volume.real {x : Space n | (x,t) ∈ S}) (volume.restrict J) ∧
    (∫ t in J, volume.real {x : Space n | (x,t) ∈ S}) = volume.real S := by
  let μB : Measure (Space n) := volume.restrict B
  let μJ : Measure ℝ := volume.restrict J
  let : IsFiniteMeasure μB := ⟨by simpa only [μB,Measure.restrict_apply_univ] using hBfin⟩
  let : IsFiniteMeasure μJ := ⟨by simpa only [μJ,Measure.restrict_apply_univ] using hJfin⟩
  let q : Point n → ℝ := S.indicator (fun _ => 1)
  have hq : Integrable q (μB.prod μJ) := (integrable_const (1:ℝ)).indicator hS
  have hSlice (t : ℝ) : (∫ x, q (x,t) ∂μB) = volume.real {x : Space n | (x,t) ∈ S} := by
    have hm : MeasurableSet {x : Space n | (x,t) ∈ S} := hS.preimage (measurable_id.prodMk measurable_const)
    have hst : {x : Space n | (x,t) ∈ S} ⊆ B := fun x hx => (hsub hx).1
    change (∫ x, ({x : Space n | (x,t) ∈ S}).indicator (fun _ => (1:ℝ)) x ∂μB) = _
    rw [integral_indicator hm,integral_const]
    simp only [μB,Measure.real,Measure.restrict_apply_univ,Measure.restrict_apply hm,inter_eq_left.mpr hst,smul_eq_mul,mul_one]
  have hqI : Integrable (fun t => volume.real {x : Space n | (x,t) ∈ S}) μJ :=
    hq.integral_prod_right.congr (.of_forall hSlice)
  refine ⟨hqI,?_⟩
  calc
    _ = ∫ t, ∫ x, q (x,t) ∂μB ∂μJ := by simp only [hSlice,μJ]
    _ = ∫ z, q z ∂μB.prod μJ := (integral_prod_symm q hq).symm
    _ = volume.real S := by
      rw [show μB.prod μJ = volume.restrict (B ×ˢ J) from (dg_productVolume_eq_restrict B J)]
      dsimp only [q]
      rw [integral_indicator hS,integral_const]
      simp only [Measure.real,Measure.restrict_restrict hS,inter_eq_left.mpr hsub,
        Measure.restrict_apply_univ,smul_eq_mul,mul_one]


/-- Fixed buffered smooth ball cutoffs exist also in real dimension 2n=2. -/
theorem dg_intermediate_ball_cutoff {n : ℕ} {r R : ℝ} (_hr : 0 < r) (hrR : r < R) :
    ∃ φ : Space n → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Metric.ball 0 R ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      ∀ x ∈ Metric.ball 0 r, φ x = 1 := by
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp [ρ]; linarith
  have hρR : ρ < R := by dsimp [ρ]; linarith
  obtain ⟨φ,hφ,hRange,hSupport,hOne⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : Space n) ρ))
    (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : Space n) r))
    (Metric.closedBall_subset_ball hrρ)
  have hts : tsupport φ ⊆ Metric.closedBall 0 ρ := by
    apply closure_minimal _ Metric.isClosed_closedBall
    rw [hSupport]
    exact Metric.ball_subset_closedBall
  have hcφ : HasCompactSupport φ := (isCompact_closedBall 0 ρ).of_isClosed_subset (isClosed_tsupport φ) hts
  refine ⟨φ,hφ,hcφ,hts.trans (Metric.closedBall_subset_ball hρR),fun x => hRange ⟨x,rfl⟩,?_⟩
  exact fun x hx => (hOne x).mp (Metric.ball_subset_closedBall hx)

/-- Normalized Caccioppoli yields a numerical positive-part energy budget on
MID, chosen before every coefficient and solution. No negative-part bound occurs. -/
theorem dg_intermediate_energy_bound {n : ℕ} (hn : 0 < n) {ν L : ℝ}
    (hν : 0 < ν) (hνL : ν ≤ L) :
    ∃ E : ℝ, 0 < E ∧ ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
      (f u : Point n → ℝ),
      DGClassicalFields (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0) A c f u →
      ClassicalDivEq (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0) A c f u →
      DGUniformBounds (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0) A c f ν L 1 1 →
      ContinuousOn u (Metric.ball (0 : Space n) 2 ×ˢ Icc (-7/2) 0) →
      (∀ z ∈ Metric.ball (0 : Space n) 2 ×ˢ Icc (-7/2) 0, u z ≤ 1) →
      Integrable (fun z => dgGradientSq (dgTruncationGradient 1 0 u z))
        (productVolume (Metric.ball 0 (7/4)) (Ioo (-3) 0)) ∧
      dgCylinderIntegral (Metric.ball 0 (7/4)) (-3) 0
        (fun z => dgGradientSq (dgTruncationGradient 1 0 u z)) ≤ E := by
  obtain ⟨χ,hχ,hcχ,hχO,hχrange,hχone⟩ := dg_intermediate_ball_cutoff (n := n)
    (by norm_num : (0:ℝ) < 7/4) (by norm_num : (7/4:ℝ) < 2)
  obtain ⟨C,hC,hCacc⟩ := dgTruncation_caccioppoli n hn ν L 1 hν hνL (by norm_num)
  let O : Set (Space n) := Metric.ball 0 2
  let ζ : Point n → ℝ := fun z => χ z.1
  let V : ℝ := volume.real O
  let J : ℝ := ∫ x in O, dgGradientSq (fun i => d χ x i)
  let B : ℝ := C*((7/2)*(J+V))+C*((7/2)*V)+C*V
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hJ0 : 0 ≤ J := integral_nonneg (fun x => dgGradientSq_nonneg _)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨1+B/ν,by positivity,?_⟩
  intro A c f u hf hpde hb hu hupper
  let μ := productVolume O (Ioo (-7/2) 0)
  let : IsFiniteMeasure μ := ⟨dg_cylinder_measure_lt_top 0 2 (-7/2) 0⟩
  let : IsFiniteMeasure (volume.restrict O) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top : volume (Metric.ball (0 : Space n) 2) < ⊤)⟩
  have hζ : DGSpatialCutoff O (-7/2) 0 ζ := by
    refine ⟨hχ.comp contDiff_fst,fun z _ => hχrange z.1,tsupport χ,hcχ,hχO,?_⟩
    intro z _ hz
    change χ z.1 = 0
    exact image_eq_zero_of_notMem_tsupport hz
  obtain ⟨hH,hX,hQ,hSlice,_hProduct,_hProductBound⟩ := hCacc 1 (by norm_num)
    0 2 (-4) 0 (-7/2) 0 (by norm_num) (by norm_num) (by norm_num) le_rfl
    A c f u ζ hf hpde hb hu hζ 1 0 (Or.inl rfl)
  let v := dgTruncation 1 0 u
  have hv (z : Point n) (hz : z ∈ O ×ˢ Icc (-7/2) 0) : 0 ≤ v z ∧ v z ≤ 1 := by
    dsimp [v,dgTruncation,dgPositivePart]
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (by simpa only [one_mul,sub_zero] using hupper z hz)
  have hζG (z : Point n) : dgGradient ζ z = fun i => d χ z.1 i := rfl
  have hζt (z : Point n) : deriv (fun t => ζ (z.1,t)) z.2 = 0 := by simp [ζ]
  have hζsq (x : Space n) : 0 ≤ (χ x)^2 ∧ (χ x)^2 ≤ 1 := by
    have hh := hχrange x
    exact ⟨sq_nonneg _,by nlinarith only [hh.1,hh.2]⟩
  have hmem : ∀ᵐ z ∂μ, z ∈ O ×ˢ Icc (-7/2) 0 := by
    rw [show μ = volume.restrict (O ×ˢ Ioo (-7/2) 0) from dg_productVolume_eq_restrict O _]
    filter_upwards [ae_restrict_mem (Metric.isOpen_ball.prod isOpen_Ioo).measurableSet] with z hz
    exact ⟨hz.1,Ioo_subset_Icc_self hz.2⟩
  have hTest := dg_test_product_integrable Metric.isOpen_ball hχ hcχ hχO (s := (-7/2)) (t := 0)
  have hJint : Integrable (fun x => dgGradientSq (fun i => d χ x i)) (volume.restrict O) := by
    have hh := (((hχ.continuous_fderiv (by simp)).norm.pow 2).continuousOn.integrableOn_compact (μ := volume)
      (isCompact_closedBall (0 : Space n) 2)).mono_set Metric.ball_subset_closedBall
    exact hh.congr (.of_forall fun x => dg_fderiv_norm_sq χ x)
  have hW : Integrable (fun z : Point n => dgGradientSq (fun i => d χ z.1 i)+1) μ := hTest.2.2.add (integrable_const _)
  have hXb : dgCylinderIntegral O (-7/2) 0 (dgTruncationCutoffError 1 0 u ζ) ≤ (7/2)*(J+V) := by
    calc
      _ ≤ ∫ z, (dgGradientSq (fun i => d χ z.1 i)+1) ∂μ := by
        apply integral_mono_ae hX hW
        filter_upwards [hmem] with z hz
        have hvb := hv z hz
        have hvsq : (v z)^2 ≤ 1 := by nlinarith only [hvb.1,hvb.2]
        have hg0 := dgGradientSq_nonneg (fun i => d χ z.1 i)
        have hh := hζsq z.1
        dsimp only [dgTruncationCutoffError]
        rw [hζt,abs_zero,zero_add,hζG]
        change (v z)^2*(dgGradientSq (fun i => d χ z.1 i)+(χ z.1)^2) ≤ _
        exact (mul_le_mul_of_nonneg_right hvsq (add_nonneg hg0 hh.1)).trans (by nlinarith only [hh.2])
      _ = _ := by
        have hh := dg_spatial_time_integral O (by norm_num : (-7/2:ℝ) ≤ 0)
          (fun x => dgGradientSq (fun i => d χ x i)+1)
        rw [integral_add hJint (integrable_const _)] at hh
        rw [show (0:ℝ)-(-7/2) = 7/2 by norm_num] at hh
        simpa only [dgCylinderIntegral,μ,integral_const,smul_eq_mul,Measure.real,
          Measure.restrict_apply_univ,mul_one,J,V] using hh
  have hQb : dgCylinderIntegral O (-7/2) 0 (dgTruncationForcingDensity 1 0 u ζ) ≤ (7/2)*V := by
    calc
      _ ≤ ∫ _z, (1:ℝ) ∂μ := by
        apply integral_mono_ae hQ (integrable_const _)
        filter_upwards [hmem] with z hz
        have hvb := hv z hz
        have hh := hζsq z.1
        change v z*(χ z.1)^2 ≤ 1
        exact (mul_le_mul_of_nonneg_right hvb.2 hh.1).trans (by simpa only [one_mul] using hh.2)
      _ = _ := by
        have hh := dg_spatial_time_integral O (by norm_num : (-7/2:ℝ) ≤ 0) (fun _ => (1:ℝ))
        simpa only [dgCylinderIntegral,μ,V,Measure.real,integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,sub_neg_eq_add,neg_div,neg_neg,zero_add] using hh
  have hInitial : dgSliceEnergy O v ζ (-7/2) ≤ V := by
    apply (integral_mono_ae (hSlice (-7/2) ⟨le_rfl,by norm_num⟩).1 (integrable_const (1:ℝ)) ?_).trans_eq
      (by simp [V,Measure.real,O])
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hh := hζsq x
    have hvb := hv (x,-7/2) ⟨hx,le_rfl,by norm_num⟩
    change (v (x,-7/2))^2*(χ x)^2 ≤ 1
    have hvsq : (v (x,-7/2))^2 ≤ 1 := by nlinarith only [hvb.1,hvb.2]
    exact (mul_le_mul_of_nonneg_right hvsq hh.1).trans (by simpa only [one_mul] using hh.2)
  have hHb : ν*dgCylinderIntegral O (-7/2) 0 (dgTruncationEnergyDensity 1 0 u ζ) ≤ B := by
    have hh := (hSlice (-7/2) ⟨le_rfl,by norm_num⟩).2
    have hS0 : 0 ≤ dgSliceEnergy O v ζ (-7/2) := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hBB := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hXb hC.le)
      (mul_le_mul_of_nonneg_left hQb hC.le)) (mul_le_mul_of_nonneg_left hInitial hC.le)
    dsimp only [B] at hBB ⊢
    simp only [mul_one] at hh
    linarith only [hh,hBB,hS0]
  let μm := productVolume (Metric.ball (0 : Space n) (7/4)) (Ioo (-3) 0)
  have hμ : μm ≤ μ := by
    rw [show μm = volume.restrict (Metric.ball (0 : Space n) (7/4) ×ˢ Ioo (-3) 0) from dg_productVolume_eq_restrict _ _,
      show μ = volume.restrict (O ×ˢ Ioo (-7/2) 0) from dg_productVolume_eq_restrict _ _]
    exact Measure.restrict_mono (Set.prod_mono (Metric.ball_subset_ball (by norm_num))
      (Ioo_subset_Ioo (by norm_num) le_rfl)) le_rfl
  have hEq : dgTruncationEnergyDensity 1 0 u ζ =ᵐ[μm]
      fun z => dgGradientSq (dgTruncationGradient 1 0 u z) := by
    rw [show μm = volume.restrict (Metric.ball (0 : Space n) (7/4) ×ˢ Ioo (-3) 0) from dg_productVolume_eq_restrict _ _]
    filter_upwards [ae_restrict_mem (Metric.isOpen_ball.prod isOpen_Ioo).measurableSet] with z hz
    simp only [dgTruncationEnergyDensity,ζ,hχone z.1 hz.1,one_pow,mul_one]
  refine ⟨(hH.mono_measure hμ).congr hEq,?_⟩
  have hle := integral_mono_measure hμ (.of_forall fun z =>
    mul_nonneg (dgGradientSq_nonneg _) (sq_nonneg _)) hH
  change (∫ z, dgTruncationEnergyDensity 1 0 u ζ z ∂μm) ≤
    ∫ z, dgTruncationEnergyDensity 1 0 u ζ z ∂μ at hle
  rw [integral_congr_ae hEq] at hle
  have hh : dgCylinderIntegral O (-7/2) 0 (dgTruncationEnergyDensity 1 0 u ζ) ≤ B/ν :=
    (le_div_iff₀ hν).mpr (by nlinarith only [hHb])
  exact hle.trans (hh.trans (by linarith))


/-- A fixed positive spatial mean, its numerical energy budget and its one-sided
square-root time modulus, all chosen before the normalized candidate fields. -/
theorem dg_intermediate_mean_control {n : ℕ} (hn : 0 < n) {ν L : ℝ}
    (hν : 0 < ν) (hνL : ν ≤ L) :
    ∃ (φ : Space n → ℝ) (E A₀ : ℝ), ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Metric.ball 0 (3/2) ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x ∈ Metric.ball 0 1, φ x = 1) ∧ 0 < E ∧ 0 < A₀ ∧
      ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ),
      DGClassicalFields (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0) A c f u →
      ClassicalDivEq (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0) A c f u →
      DGUniformBounds (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0) A c f ν L 1 1 →
      ContinuousOn u (Metric.ball (0 : Space n) 2 ×ˢ Icc (-7/2) 0) →
      (∀ z ∈ Metric.ball (0 : Space n) 2 ×ˢ Icc (-7/2) 0, u z ≤ 1) →
      let O := Metric.ball (0 : Space n) (7/4)
      let h := dgTruncationMean O φ 1 0 u
      Integrable (fun z => dgGradientSq (dgTruncationGradient 1 0 u z)) (productVolume O (Ioo (-3) 0)) ∧
      dgCylinderIntegral O (-3) 0 (fun z => dgGradientSq (dgTruncationGradient 1 0 u z)) ≤ E ∧
      ContinuousOn h (Icc (-3) 0) ∧
      ∀ s ∈ Ioo (-3) 0, ∀ t ∈ Ioo (-3) 0, s < t → h t-h s ≤ A₀*Real.sqrt (t-s) := by
  obtain ⟨φ,hφ,hcφ,hφS,hφrange,hφone⟩ := dg_intermediate_ball_cutoff (n := n)
    (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)
  obtain ⟨E,hE,hEnergy⟩ := dg_intermediate_energy_bound hn hν hνL
  let O : Set (Space n) := Metric.ball 0 (7/4)
  have hφO : tsupport φ ⊆ O := hφS.trans (Metric.ball_subset_ball (by norm_num))
  let P := (L*dgTestGradientL2 O φ+dgTestL2 O φ)*Real.sqrt E
  let R := dgTestL1 O φ
  let A₀ := 1+P+R*Real.sqrt 3
  have hR0 : 0 ≤ R := integral_nonneg fun x => abs_nonneg _
  have hL0 : 0 ≤ L := hν.le.trans hνL
  have hP0 : 0 ≤ P := by dsimp [P,dgTestGradientL2,dgTestL2]; positivity
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  refine ⟨φ,E,A₀,hφ,hcφ,hφS,hφrange,hφone,hE,hA₀,?_⟩
  intro A c f u hf hpde hb hu hupper
  obtain ⟨hEI,hEB⟩ := hEnergy A c f u hf hpde hb hu hupper
  have hOU : O ×ˢ Ioo (-4:ℝ) 0 ⊆ Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4:ℝ) 0 :=
    Set.prod_mono (Metric.ball_subset_ball (by norm_num)) subset_rfl
  have hfO : DGClassicalFields (O ×ˢ Ioo (-4) 0) A c f u :=
    ⟨fun i j => (hf.1 i j).mono hOU,fun i => (hf.2.1 i).mono hOU,
      hf.2.2.1.mono hOU,hf.2.2.2.mono hOU⟩
  have hpdeO : ClassicalDivEq (O ×ˢ Ioo (-4) 0) A c f u := fun z hz => hpde z (hOU hz)
  have hbO : DGUniformBounds (O ×ˢ Ioo (-4) 0) A c f ν L 1 1 :=
    ⟨⟨hb.1.1,hb.1.2.1,fun z hz => hb.1.2.2 z (hOU hz)⟩,
      fun z hz => hb.2.1 z (hOU hz),fun z hz => hb.2.2 z (hOU hz)⟩
  have huO : ContinuousOn u (O ×ˢ Icc (-3) 0) := hu.mono
    (Set.prod_mono (Metric.ball_subset_ball (by norm_num)) (Icc_subset_Icc (by norm_num) le_rfl))
  have hcont := dgTruncationMean_continuousOn Metric.isOpen_ball huO hφ.continuous hcφ hφO 1 0
  refine ⟨hEI,hEB,hcont,?_⟩
  intro s hs t ht hst
  have huST : ContinuousOn u (O ×ˢ Icc s t) := huO.mono
    (Set.prod_mono subset_rfl (Icc_subset_Icc hs.1.le ht.2.le))
  obtain ⟨_hG,_hM,_hc,hInc⟩ := dgTruncation_mean n hn ν L 1 1 hν hνL (by norm_num) (by norm_num)
    0 (7/4) (-4) 0 s t (by norm_num) (by linarith [hs.1]) hst ht.2.le
    A c f u φ hfO hpdeO hbO huST hφ hcφ hφO (fun x => (hφrange x).1) 1 0 (Or.inl rfl)
  have hμ : productVolume O (Ioo s t) ≤ productVolume O (Ioo (-3) 0) := by
    rw [dg_productVolume_eq_restrict,dg_productVolume_eq_restrict]
    exact Measure.restrict_mono (Set.prod_mono subset_rfl (Ioo_subset_Ioo hs.1.le ht.2.le)) le_rfl
  have hEbst : dgCylinderIntegral O s t (fun z => dgGradientSq (dgTruncationGradient 1 0 u z)) ≤ E :=
    (integral_mono_measure hμ (.of_forall fun z => dgGradientSq_nonneg _) hEI).trans hEB
  have hh := hInc E hE.le (hEI.mono_measure hμ) hEbst
  simp only [one_mul] at hh
  have hdt : 0 ≤ t-s := sub_nonneg.mpr hst.le
  have hdt3 : t-s ≤ 3 := by linarith only [hs.1,ht.2]
  have hroot := Real.sqrt_le_sqrt hdt3
  have hlin : t-s ≤ Real.sqrt 3*Real.sqrt (t-s) := by
    calc
      _ = Real.sqrt (t-s)*Real.sqrt (t-s) := by rw [←sq,Real.sq_sqrt hdt]
      _ ≤ _ := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)
  have hlinR := mul_le_mul_of_nonneg_left hlin hR0
  change dgTruncationMean O φ 1 0 u t-dgTruncationMean O φ 1 0 u s ≤ A₀*Real.sqrt (t-s)
  calc
    _ ≤ P*Real.sqrt (t-s)+R*(t-s) := hh
    _ ≤ P*Real.sqrt (t-s)+R*(Real.sqrt 3*Real.sqrt (t-s)) := add_le_add le_rfl hlinR
    _ ≤ A₀*Real.sqrt (t-s) := by dsimp only [A₀]; nlinarith only [Real.sqrt_nonneg (t-s)]


/-- Real indicator integrals of subsets of the actual integration set. -/
theorem dg_indicator_subset_integral {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {B S : Set E} (hS : MeasurableSet S) (hSB : S ⊆ B) :
    (∫ x in B, S.indicator (fun _ => (1:ℝ)) x ∂μ) = μ.real S := by
  rw [integral_indicator hS,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,Measure.restrict_apply hS,
    inter_eq_left.mpr hSB,smul_eq_mul,mul_one]

theorem dg_local_sublevel_measurable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {O : Set E} (hO : IsOpen O) {g : E → ℝ}
    (hg : ContinuousOn g O) (a : ℝ) : MeasurableSet (O ∩ {x | g x ≤ a}) := by
  have hh := (hg.isOpen_inter_preimage hO (isOpen_Ioi : IsOpen (Ioi a))).measurableSet
  have he : O ∩ {x | g x ≤ a} = O \ (O ∩ g ⁻¹' Ioi a) := by
    ext x
    by_cases hx : x ∈ O <;> simp [hx,not_lt]
  rw [he]
  exact hO.measurableSet.diff hh

theorem dg_local_superlevel_measurable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {O : Set E} (hO : IsOpen O) {g : E → ℝ}
    (hg : ContinuousOn g O) (a : ℝ) : MeasurableSet (O ∩ {x | a ≤ g x}) := by
  have hh := (hg.isOpen_inter_preimage hO (isOpen_Iio : IsOpen (Iio a))).measurableSet
  have he : O ∩ {x | a ≤ g x} = O \ (O ∩ g ⁻¹' Iio a) := by
    ext x
    by_cases hx : x ∈ O <;> simp [hx,not_lt]
  rw [he]
  exact hO.measurableSet.diff hh

theorem dg_local_band_measurable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {O : Set E} (hO : IsOpen O) {g : E → ℝ}
    (hg : ContinuousOn g O) (a b : ℝ) : MeasurableSet (O ∩ {x | a < g x ∧ g x < b}) :=
  (hg.isOpen_inter_preimage hO isOpen_Ioo).measurableSet

/-- Qualitative local integrability has no quantitative derivative constant. -/
theorem dg_intermediate_inner_ball_integrable {n : ℕ} {g : Space n → ℝ}
    (hg : ContinuousOn g (Metric.ball (0 : Space n) 2)) :
    Integrable g (volume.restrict (Metric.ball (0 : Space n) (7/4))) := by
  have hclosed : Metric.closedBall (0 : Space n) (7/4) ⊆ Metric.ball 0 2 :=
    Metric.closedBall_subset_ball (by norm_num)
  exact ((hg.mono hclosed).integrableOn_compact (isCompact_closedBall 0 (7/4))).mono_set Metric.ball_subset_closedBall

theorem dg_positivePart_le_two_clamp {r : ℝ} (hr : r ≤ 1) :
    dgPositivePart r ≤ 2*dgClamp 0 (1/2) r := by
  by_cases hr0 : r ≤ 0
  · rw [dgPositivePart_of_nonpos hr0,dgClamp_zero (by norm_num) hr0,mul_zero]
  by_cases hrh : (1/2:ℝ) ≤ r
  · rw [dgPositivePart_of_nonneg (by linarith),dgClamp_gap (by norm_num) hrh]
    linarith
  · rw [dgPositivePart_of_nonneg (by linarith),dgClamp_middle ⟨lt_of_not_ge hr0,lt_of_not_ge hrh⟩]
    linarith

/-- The spatial zero-set inequality bounds the actual weighted positive mean
with the strict intermediate-band gradient. The zero set may be measured on B1. -/
theorem dg_intermediate_zero_mean_bound {n : ℕ} {g φ : Space n → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Metric.ball (0 : Space n) 2)) (hφ : ContDiff ℝ ∞ φ)
    (hφrange : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hupper : ∀ x ∈ Metric.ball (0 : Space n) 2, g x ≤ 1) :
    volume.real (Metric.ball (0 : Space n) 1 ∩ {x | g x ≤ 0})*
      (∫ x in Metric.ball (0 : Space n) (7/4), φ x*dgPositivePart (g x)) ≤
      2*((2:ℝ)^(2*n+1)*(7/4)*volume.real (Metric.ball (0 : Space n) (7/4)))*
        (∫ x in Metric.ball (0 : Space n) (7/4) ∩ {x | 0 < g x ∧ g x < 1/2}, ‖fderiv ℝ g x‖) := by
  let O : Set (Space n) := Metric.ball 0 (7/4)
  let Z₁ := Metric.ball (0 : Space n) 1 ∩ {x | g x ≤ 0}
  let Z₇ := O ∩ {x | g x ≤ 0}
  have hZ₁0 : 0 ≤ volume.real Z₁ := ENNReal.toReal_nonneg
  have hCap0 : 0 ≤ ∫ x in O, dgClamp 0 (1/2) (g x) :=
    integral_nonneg fun x => (dgClamp_bounds (by norm_num) (g x)).1
  have hCapI : Integrable (fun x => dgClamp 0 (1/2) (g x)) (volume.restrict O) :=
    dg_intermediate_inner_ball_integrable ((dgClamp_continuous 0 (1/2)).comp_continuousOn hg.continuousOn)
  have hMeanI : Integrable (fun x => φ x*dgPositivePart (g x)) (volume.restrict O) :=
    dg_intermediate_inner_ball_integrable (hφ.continuous.continuousOn.mul
      (dgPositivePart_lipschitz.continuous.comp_continuousOn hg.continuousOn))
  have hMean : (∫ x in O, φ x*dgPositivePart (g x)) ≤ 2*(∫ x in O, dgClamp 0 (1/2) (g x)) := by
    rw [←integral_const_mul]
    apply integral_mono_ae hMeanI (hCapI.const_mul 2)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hx₂ : x ∈ Metric.ball (0 : Space n) 2 := Metric.ball_subset_ball (by norm_num) hx
    exact ((mul_le_mul_of_nonneg_right (hφrange x).2 (dgPositivePart_nonneg _)).trans_eq (one_mul _)).trans
      (dg_positivePart_le_two_clamp (hupper x hx₂))
  have hZsub : volume.real Z₁ ≤ volume.real Z₇ :=
    measureReal_mono (Set.inter_subset_inter_left _ (Metric.ball_subset_ball (by norm_num)))
      ((measure_mono inter_subset_left).trans_lt (measure_ball_lt_top : volume O < ⊤)).ne
  have hP := dg_ball_clamp_zero_set_poincare_local Metric.isOpen_ball (0 : Space n)
    (by norm_num : (0:ℝ) < 7/4) (Metric.closedBall_subset_ball (by norm_num : (7/4:ℝ) < 2)) hg
    (by norm_num : (0:ℝ) < 1/2)
  calc
    _ ≤ volume.real Z₁*(2*(∫ x in O, dgClamp 0 (1/2) (g x))) := mul_le_mul_of_nonneg_left hMean hZ₁0
    _ ≤ volume.real Z₇*(2*(∫ x in O, dgClamp 0 (1/2) (g x))) :=
      mul_le_mul_of_nonneg_right hZsub (mul_nonneg (by norm_num) hCap0)
    _ = 2*(volume.real Z₇*(∫ x in O, dgClamp 0 (1/2) (g x))) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hP (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)


/-- Integrating a genuine level-set lower bound against a finite measure. -/
theorem dg_mass_le_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {q : X → ℝ} {S : Set X} {a : ℝ} (hS : MeasurableSet S) (hq : Integrable q μ)
    (hq0 : ∀ x, 0 ≤ q x) (ha : ∀ x ∈ S, a ≤ q x) : a*μ.real S ≤ ∫ x, q x ∂μ := by
  calc
    _ = ∫ x, S.indicator (fun _ => a) x ∂μ := by
      rw [integral_indicator hS,integral_const]
      simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
      ring
    _ ≤ _ := by
      apply integral_mono_ae ((integrable_const a).indicator hS) hq
      exact .of_forall fun x => by
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx]; exact ha x hx
        · rw [Set.indicator_of_notMem hx]; exact hq0 x

/-- Actual spatial masses controlling a positive weighted mean. The negative
part is used only through the zero-set partition, never through its magnitude. -/
theorem dg_intermediate_spatial_masses {n : ℕ} {g φ : Space n → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Metric.ball (0 : Space n) 2)) (hφ : ContDiff ℝ ∞ φ)
    (hφrange : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) (hφS : tsupport φ ⊆ Metric.ball 0 (3/2))
    (hφone : ∀ x ∈ Metric.ball (0 : Space n) 1, φ x = 1)
    (hupper : ∀ x ∈ Metric.ball (0 : Space n) 2, g x ≤ 1) :
    let O := Metric.ball (0 : Space n) (7/4)
    let Z := Metric.ball (0 : Space n) 1 ∩ {x | g x ≤ 0}
    let M := O ∩ {x | 0 < g x ∧ g x < 1/2}
    let H₁ := Metric.ball (0 : Space n) 1 ∩ {x | 1/2 ≤ g x}
    let H₃ := Metric.ball (0 : Space n) (3/2) ∩ {x | 1/2 ≤ g x}
    let h := ∫ x in O, φ x*dgPositivePart (g x)
    (1/2)*volume.real H₁ ≤ h ∧
    volume.real (Metric.ball (0 : Space n) 1) ≤ volume.real Z+volume.real M+volume.real H₁ ∧
    h ≤ volume.real H₃+(1/2)*volume.real M := by
  let O : Set (Space n) := Metric.ball 0 (7/4)
  let Z := Metric.ball (0 : Space n) 1 ∩ {x | g x ≤ 0}
  let M := O ∩ {x | 0 < g x ∧ g x < 1/2}
  let H₁ := Metric.ball (0 : Space n) 1 ∩ {x | 1/2 ≤ g x}
  let H₃ := Metric.ball (0 : Space n) (3/2) ∩ {x | 1/2 ≤ g x}
  let q : Space n → ℝ := fun x => φ x*dgPositivePart (g x)
  let μ : Measure (Space n) := volume.restrict O
  let : IsFiniteMeasure μ := ⟨by simpa only [μ,Measure.restrict_apply_univ] using
    (measure_ball_lt_top : volume (Metric.ball (0 : Space n) (7/4)) < ⊤)⟩
  have hH₁ : MeasurableSet H₁ := dg_local_superlevel_measurable Metric.isOpen_ball
    (hg.continuousOn.mono (Metric.ball_subset_ball (by norm_num))) (1/2)
  have hH₃ : MeasurableSet H₃ := dg_local_superlevel_measurable Metric.isOpen_ball
    (hg.continuousOn.mono (Metric.ball_subset_ball (by norm_num))) (1/2)
  have hM : MeasurableSet M := dg_local_band_measurable Metric.isOpen_ball
    (hg.continuousOn.mono (Metric.ball_subset_ball (by norm_num))) 0 (1/2)
  have hH₁O : H₁ ⊆ O := fun x hx => Metric.ball_subset_ball (by norm_num) hx.1
  have hH₃O : H₃ ⊆ O := fun x hx => Metric.ball_subset_ball (by norm_num) hx.1
  have hMO : M ⊆ O := inter_subset_left
  have hqI : Integrable q μ := dg_intermediate_inner_ball_integrable
    (hφ.continuous.continuousOn.mul (dgPositivePart_lipschitz.continuous.comp_continuousOn hg.continuousOn))
  have hq0 (x : Space n) : 0 ≤ q x := mul_nonneg (hφrange x).1 (dgPositivePart_nonneg _)
  have hHigh := dg_mass_le_integral hH₁ hqI hq0 (a := (1/2:ℝ)) (fun x hx => by
    change 1/2 ≤ φ x*dgPositivePart (g x)
    rw [hφone x hx.1,one_mul,dgPositivePart_of_nonneg (by linarith only [show (1/2:ℝ) ≤ g x from hx.2] : 0 ≤ g x)]
    exact hx.2)
  have hMass₁ : μ.real H₁ = volume.real H₁ := by
    simp only [μ,measureReal_restrict_apply hH₁,inter_eq_left.mpr hH₁O]
  rw [hMass₁] at hHigh
  refine ⟨hHigh,?_,?_⟩
  · have hPart : Metric.ball (0 : Space n) 1 = (Z ∪ M ∪ H₁) ∩ Metric.ball 0 1 := by
      ext x
      constructor
      · intro hx
        refine ⟨?_,hx⟩
        by_cases hz : g x ≤ 0
        · exact Or.inl (Or.inl ⟨hx,hz⟩)
        by_cases hm : g x < 1/2
        · exact Or.inl (Or.inr ⟨Metric.ball_subset_ball (by norm_num) hx,lt_of_not_ge hz,hm⟩)
        · exact Or.inr ⟨hx,le_of_not_gt hm⟩
      · exact fun hx => hx.2
    have hFin : volume (Z ∪ M ∪ H₁) ≠ ⊤ :=
      ((measure_mono (show Z ∪ M ∪ H₁ ⊆ O from fun x hx => by
        rcases hx with (hx | hx) | hx
        · exact Metric.ball_subset_ball (by norm_num) hx.1
        · exact hx.1
        · exact hH₁O hx)).trans_lt measure_ball_lt_top).ne
    calc
      _ ≤ volume.real (Z ∪ M ∪ H₁) := measureReal_mono (by rw [hPart]; exact inter_subset_left) hFin
      _ ≤ volume.real (Z ∪ M)+volume.real H₁ := measureReal_union_le _ _
      _ ≤ _ := add_le_add (measureReal_union_le _ _) le_rfl
  · have hHI : Integrable (H₃.indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator hH₃
    have hMI : Integrable (M.indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator hM
    calc
      _ ≤ ∫ x, (H₃.indicator (fun _ => (1:ℝ)) x+(1/2)*M.indicator (fun _ => (1:ℝ)) x) ∂μ := by
        apply integral_mono_ae hqI (hHI.add (hMI.const_mul (1/2)))
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        change φ x*dgPositivePart (g x) ≤ H₃.indicator (fun _ => (1:ℝ)) x+(1/2)*M.indicator (fun _ => (1:ℝ)) x
        by_cases hx0 : g x ≤ 0
        · rw [dgPositivePart_of_nonpos hx0,mul_zero]
          exact add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mul_nonneg (by norm_num) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
        by_cases hxh : g x < 1/2
        · have hxM : x ∈ M := ⟨hx,lt_of_not_ge hx0,hxh⟩
          have hxH : x ∉ H₃ := fun hh => (not_le_of_gt hxh) hh.2
          rw [Set.indicator_of_notMem hxH,Set.indicator_of_mem hxM,zero_add,mul_one,
            dgPositivePart_of_nonneg (le_of_lt (lt_of_not_ge hx0))]
          exact ((mul_le_mul_of_nonneg_right (hφrange x).2 (le_of_lt (lt_of_not_ge hx0))).trans_eq (one_mul _)).trans hxh.le
        · by_cases hxS : x ∈ Metric.ball (0 : Space n) (3/2)
          · have hxH : x ∈ H₃ := ⟨hxS,le_of_not_gt hxh⟩
            have hxM : x ∉ M := fun hh => hxh hh.2.2
            rw [Set.indicator_of_mem hxH,Set.indicator_of_notMem hxM,mul_zero,add_zero,
              dgPositivePart_of_nonneg (le_of_lt (lt_of_not_ge hx0))]
            have hx₂ : x ∈ Metric.ball (0 : Space n) 2 := Metric.ball_subset_ball (by norm_num) hx
            exact ((mul_le_mul_of_nonneg_right (hφrange x).2 (le_of_lt (lt_of_not_ge hx0))).trans_eq (one_mul _)).trans (hupper x hx₂)
          · have hφ0 : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hxS (hφS hh))
            rw [hφ0,zero_mul]
            exact add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mul_nonneg (by norm_num) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
      _ = _ := by
        rw [integral_add hHI (hMI.const_mul (1/2)),integral_const_mul]
        rw [show (∫ x, H₃.indicator (fun _ => (1:ℝ)) x ∂μ) = volume.real H₃ from dg_indicator_subset_integral hH₃ hH₃O,
          show (∫ x, M.indicator (fun _ => (1:ℝ)) x ∂μ) = volume.real M from dg_indicator_subset_integral hM hMO]

/-- When a true mean lies in [H,2H] and the middle slice is small, relative
Poincare forces a dimension-controlled amount of strict-band gradient. -/
theorem dg_intermediate_window_gradient {n : ℕ} {g φ : Space n → ℝ} {H : ℝ}
    (hH : 0 < H) (hsmall : 32*H ≤ volume.real (Metric.ball (0 : Space n) 1))
    (hg : ContDiffOn ℝ ∞ g (Metric.ball (0 : Space n) 2)) (hφ : ContDiff ℝ ∞ φ)
    (hφrange : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) (hφS : tsupport φ ⊆ Metric.ball 0 (3/2))
    (hφone : ∀ x ∈ Metric.ball (0 : Space n) 1, φ x = 1)
    (hupper : ∀ x ∈ Metric.ball (0 : Space n) 2, g x ≤ 1)
    (hmean : H ≤ ∫ x in Metric.ball (0 : Space n) (7/4), φ x*dgPositivePart (g x))
    (hmean' : (∫ x in Metric.ball (0 : Space n) (7/4), φ x*dgPositivePart (g x)) ≤ 2*H)
    (hmid : volume.real (Metric.ball (0 : Space n) (7/4) ∩ {x | 0 < g x ∧ g x < 1/2}) ≤ H)
    (hmid' : volume.real (Metric.ball (0 : Space n) (7/4) ∩ {x | 0 < g x ∧ g x < 1/2}) ≤
      volume.real (Metric.ball (0 : Space n) 1)/4) :
    volume.real (Metric.ball (0 : Space n) 1)*H/8 ≤
      ((2:ℝ)^(2*n+1)*(7/4)*volume.real (Metric.ball (0 : Space n) (7/4)))*
        (∫ x in Metric.ball (0 : Space n) (7/4) ∩ {x | 0 < g x ∧ g x < 1/2}, ‖fderiv ℝ g x‖) := by
  obtain ⟨hHigh,hPart,hMean⟩ := dg_intermediate_spatial_masses hg hφ hφrange hφS hφone hupper
  have hZero : volume.real (Metric.ball (0 : Space n) 1)/2 ≤
      volume.real (Metric.ball (0 : Space n) 1 ∩ {x | g x ≤ 0}) := by
    linarith only [hHigh,hPart,hmean',hsmall,hmid',hH]
  have hUpper : H/2 ≤ volume.real (Metric.ball (0 : Space n) (3/2) ∩ {x | 1/2 ≤ g x}) := by
    linarith only [hMean,hmean,hmid]
  have hZsub : volume.real (Metric.ball (0 : Space n) 1 ∩ {x | g x ≤ 0}) ≤
      volume.real (Metric.ball (0 : Space n) (7/4) ∩ {x | g x ≤ 0}) :=
    measureReal_mono (Set.inter_subset_inter_left _ (Metric.ball_subset_ball (by norm_num)))
      ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have hUsub : volume.real (Metric.ball (0 : Space n) (3/2) ∩ {x | 1/2 ≤ g x}) ≤
      volume.real (Metric.ball (0 : Space n) (7/4) ∩ {x | 1/2 ≤ g x}) :=
    measureReal_mono (Set.inter_subset_inter_left _ (Metric.ball_subset_ball (by norm_num)))
      ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have hProd := mul_le_mul (hZero.trans hZsub) (hUpper.trans hUsub)
    (by linarith only [hH] : (0:ℝ) ≤ H/2) (ENNReal.toReal_nonneg : 0 ≤ volume.real (Metric.ball (0 : Space n) (7/4) ∩ {x | g x ≤ 0}))
  have hP := dg_ball_relative_poincare_local Metric.isOpen_ball (0 : Space n)
    (by norm_num : (0:ℝ) < 7/4) (Metric.closedBall_subset_ball (by norm_num : (7/4:ℝ) < 2)) hg
    (by norm_num : (0:ℝ) < 1/2)
  calc
    _ = (1/2)*((volume.real (Metric.ball (0 : Space n) 1)/2)*(H/2)) := by ring
    _ ≤ (1/2)*(volume.real (Metric.ball (0 : Space n) (7/4) ∩ {x | g x ≤ 0})*
        volume.real (Metric.ball (0 : Space n) (7/4) ∩ {x | 1/2 ≤ g x})) :=
      mul_le_mul_of_nonneg_left hProd (by norm_num)
    _ ≤ _ := by simpa only [sub_zero,mul_assoc] using hP


/-- A quantitative one-variable form of the direct mean-crossing argument.
Its ordinary spatial inequalities will be discharged below by the actual DG
zero-set and relative estimates; it assumes no middle-layer measure conclusion. -/
theorem dg_direct_mean_crossing_bound {V E A K α β : ℝ}
    (hV : 0 < V) (hE : 0 < E) (hA : 0 < A) (hK : 0 < K) (hα : 0 < α) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h z m g : ℝ → ℝ) (η : ℝ), 0 ≤ η →
      ContinuousOn h (Icc (-3) 0) →
      (∀ s ∈ Ioo (-3) 0, ∀ t ∈ Ioo (-3) 0, s < t → h t-h s ≤ A*Real.sqrt (t-s)) →
      Integrable z (volume.restrict (Ioo (-3) (-2))) →
      Integrable m (volume.restrict (Ioo (-3) 0)) →
      Integrable g (volume.restrict (Ioo (-3) 0)) →
      (∀ t ∈ Ioo (-3) (-2), 0 ≤ z t) →
      (∀ t ∈ Ioo (-3) 0, 0 ≤ m t ∧ 0 ≤ g t) →
      α*V ≤ (∫ t in Ioo (-3) (-2), z t) →
      β*V/2 ≤ (∫ t in Ioo (-1) 0, h t) →
      (∀ t ∈ Ioo (-3) (-2), z t*h t ≤ 2*K*g t) →
      (∀ H : ℝ, 0 < H → 32*H ≤ V → ∀ t ∈ Ioo (-3) 0,
        H ≤ h t → h t ≤ 2*H → m t ≤ H → m t ≤ V/4 → V*H/(8*K) ≤ g t) →
      (∫ t in Ioo (-3) 0, m t) ≤ η →
      (∫ t in Ioo (-3) 0, g t) ≤ Real.sqrt E*Real.sqrt η → δ ≤ η := by
  let H : ℝ := min (β*V/64) (min (V/64) 1)
  have hH : 0 < H := by dsimp [H]; positivity
  have hHβ : H ≤ β*V/64 := min_le_left _ _
  have hHV : 32*H ≤ V := by
    have hh : H ≤ V/64 := (min_le_right _ _).trans (min_le_left _ _)
    linarith only [hh,hV]
  let κ := min H (V/4)
  let Δ := (H/A)^2
  let q := V*H/(8*K)
  let P := (H/2)*(α*V)
  let c₁ := P/(4*K*(Real.sqrt E+1))
  let c₂ := (q*Δ)/(4*(Real.sqrt E+1))
  let δ := min (c₁^2) (min (c₂^2) (κ*Δ/4))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 < c₂ := by dsimp [c₂]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  intro h z m g η _hη0 hcont hinc hzI hmI hgI hz0 hmg0 hzEarly hhLate hzero hwindow hmBound hgBound
  by_contra hδle
  have hηδ : η < δ := lt_of_not_ge hδle
  have hη₁ : η < c₁^2 := hηδ.trans_le (min_le_left _ _)
  have hη₂ : η < c₂^2 := hηδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hη₃ : η < κ*Δ/4 := hηδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hroot₁ : Real.sqrt η < c₁ := (Real.sqrt_lt' hc₁).mpr hη₁
  have hroot₂ : Real.sqrt η < c₂ := (Real.sqrt_lt' hc₂).mpr hη₂
  have hμEarly : volume.restrict (Ioo (-3:ℝ) (-2)) ≤ volume.restrict (Ioo (-3:ℝ) 0) :=
    Measure.restrict_mono (Ioo_subset_Ioo le_rfl (by norm_num)) le_rfl
  have hgEarlyI := hgI.mono_measure hμEarly
  have hgEarly : (∫ t in Ioo (-3) (-2), g t) ≤ Real.sqrt E*Real.sqrt η :=
    (integral_mono_measure hμEarly (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact (hmg0 t ht).2) hgI).trans hgBound
  have hsmallEarly : 2*K*(Real.sqrt E*Real.sqrt η) < P := by
    have hden : 0 < 4*K*(Real.sqrt E+1) := by positivity
    have hh : Real.sqrt η*(4*K*(Real.sqrt E+1)) < P := (lt_div_iff₀ hden).mp hroot₁
    have hCoeff : 2*K*Real.sqrt E ≤ 4*K*(Real.sqrt E+1) := by
      nlinarith only [hK,mul_nonneg hK.le (Real.sqrt_nonneg E)]
    calc
      _ = (2*K*Real.sqrt E)*Real.sqrt η := by ring
      _ ≤ (4*K*(Real.sqrt E+1))*Real.sqrt η := mul_le_mul_of_nonneg_right hCoeff (Real.sqrt_nonneg _)
      _ < _ := by simpa only [mul_comm] using hh
  have hsExists : ∃ s ∈ Ioo (-3:ℝ) (-2), h s < H/2 := by
    by_contra hn
    push Not at hn
    let : IsFiniteMeasure (volume.restrict (Ioo (-3:ℝ) (-2))) := ⟨by simp⟩
    have hpoint : ∀ᵐ t ∂volume.restrict (Ioo (-3:ℝ) (-2)), (H/2)*z t ≤ (2*K)*g t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      calc
        _ = z t*(H/2) := by ring
        _ ≤ z t*h t := mul_le_mul_of_nonneg_left (hn t ht) (hz0 t ht)
        _ ≤ _ := hzero t ht
    have hh := integral_mono_ae (hzI.const_mul (H/2)) (hgEarlyI.const_mul (2*K)) hpoint
    rw [integral_const_mul,integral_const_mul] at hh
    have hPbound : P ≤ 2*K*(Real.sqrt E*Real.sqrt η) := calc
      _ ≤ (H/2)*(∫ t in Ioo (-3) (-2), z t) := mul_le_mul_of_nonneg_left hzEarly (by positivity)
      _ ≤ (2*K)*(∫ t in Ioo (-3) (-2), g t) := hh
      _ ≤ _ := mul_le_mul_of_nonneg_left hgEarly (by positivity)
    exact (not_lt_of_ge hPbound) hsmallEarly
  obtain ⟨s,hs,hsH⟩ := hsExists
  have hhI : IntegrableOn h (Icc (-3:ℝ) 0) volume := hcont.integrableOn_compact isCompact_Icc
  have hhLateI : Integrable h (volume.restrict (Ioo (-1:ℝ) 0)) :=
    hhI.mono_set (fun t ht => ⟨by linarith only [ht.1],ht.2.le⟩)
  have htExists : ∃ t ∈ Ioo (-1:ℝ) 0, 4*H < h t := by
    by_contra hn
    push Not at hn
    let : IsFiniteMeasure (volume.restrict (Ioo (-1:ℝ) 0)) := ⟨by simp⟩
    have hh : (∫ t in Ioo (-1) 0, h t) ≤ 4*H := by
      calc
        _ ≤ ∫ _t in Ioo (-1:ℝ) 0, (4*H) := by
          apply integral_mono_ae hhLateI (integrable_const _)
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          exact hn t ht
        _ = _ := by simp [Measure.real]
    have hβV : 0 < β*V := mul_pos hβ hV
    linarith only [hhLate,hh,hHβ,hβV]
  obtain ⟨t,ht,htH⟩ := htExists
  have hst : s < t := by linarith only [hs.2,ht.1]
  have hcontST : ContinuousOn h (Icc s t) := hcont.mono
    (Icc_subset_Icc hs.1.le ht.2.le)
  obtain ⟨a,b,ha,hb,hab,haH,hbH,hBand⟩ := dg_mean_crossing_interval hst hH hcontST
    (by linarith only [hsH,hH]) (by linarith only [htH,hH])
  have haJ : a ∈ Ioo (-3:ℝ) 0 := ⟨hs.1.trans_le ha.1,ha.2.trans_lt ht.2⟩
  have hbJ : b ∈ Ioo (-3:ℝ) 0 := ⟨hs.1.trans_le hb.1,hb.2.trans_lt ht.2⟩
  have hDuration : Δ ≤ b-a := dg_crossing_duration hab hH hA haH hbH (hinc a haJ b hbJ hab)
  have hJsub : Ioo a b ⊆ Ioo (-3:ℝ) 0 := Ioo_subset_Ioo haJ.1.le hbJ.2.le
  have hμJ : volume.restrict (Ioo a b) ≤ volume.restrict (Ioo (-3:ℝ) 0) := Measure.restrict_mono hJsub le_rfl
  let : IsFiniteMeasure (volume.restrict (Ioo a b)) := ⟨by simp⟩
  have hgJI := hgI.mono_measure hμJ
  have hmJI := hmI.mono_measure hμJ
  have hPoint : ∀ᵐ r ∂volume.restrict (Ioo a b), q ≤ g r+(q/κ)*m r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hrJ := hJsub hr
    have hrBand := hBand r (Ioo_subset_Icc_self hr)
    have hqκ : 0 ≤ q/κ := div_nonneg hq.le hκ.le
    by_cases hm : m r ≤ κ
    · have hh := hwindow H hH hHV r hrJ hrBand.1 hrBand.2
        (hm.trans (min_le_left _ _)) (hm.trans (min_le_right _ _))
      exact hh.trans (le_add_of_nonneg_right (mul_nonneg hqκ (hmg0 r hrJ).1))
    · have hh : q ≤ (q/κ)*m r := calc
        _ = (q/κ)*κ := by rw [div_mul_cancel₀ _ hκ.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hm)) hqκ
      exact hh.trans (le_add_of_nonneg_left (hmg0 r hrJ).2)
  have hIntegral : q*(b-a) ≤ (∫ r in Ioo a b, g r)+(q/κ)*(∫ r in Ioo a b, m r) := by
    have hh := integral_mono_ae (integrable_const q) (hgJI.add (hmJI.const_mul (q/κ))) hPoint
    simp only [Pi.add_apply] at hh
    rw [integral_add hgJI (hmJI.const_mul (q/κ)),integral_const_mul] at hh
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le),smul_eq_mul,mul_comm] using hh
  have hgJ : (∫ r in Ioo a b, g r) ≤ Real.sqrt E*Real.sqrt η :=
    (integral_mono_measure hμJ (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (hmg0 r hr).2) hgI).trans hgBound
  have hmJ : (∫ r in Ioo a b, m r) ≤ η :=
    (integral_mono_measure hμJ (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (hmg0 r hr).1) hmI).trans hmBound
  have hContradict : q*Δ ≤ Real.sqrt E*Real.sqrt η+(q/κ)*η := calc
    _ ≤ q*(b-a) := mul_le_mul_of_nonneg_left hDuration hq.le
    _ ≤ _ := hIntegral
    _ ≤ _ := add_le_add hgJ (mul_le_mul_of_nonneg_left hmJ (div_nonneg hq.le hκ.le))
  have hSmall₁ : Real.sqrt E*Real.sqrt η < q*Δ/4 := by
    have hh : Real.sqrt η*(4*(Real.sqrt E+1)) < q*Δ :=
      (lt_div_iff₀ (by positivity : (0:ℝ) < 4*(Real.sqrt E+1))).mp hroot₂
    nlinarith only [hh,Real.sqrt_nonneg η]
  have hSmall₂ : (q/κ)*η < q*Δ/4 := calc
    _ < (q/κ)*(κ*Δ/4) := mul_lt_mul_of_pos_left hη₃ (div_pos hq hκ)
    _ = _ := by field_simp
  have hqΔ : 0 < q*Δ := mul_pos hq hΔ
  nlinarith only [hContradict,hSmall₁,hSmall₂,hqΔ]


/-- Every relevant actual spatial slice is smooth on the original open ball. -/
theorem dg_intermediate_slice_smooth {n : ℕ} {u : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0))
    {t : ℝ} (ht : t ∈ Ioo (-3) 0) :
    ContDiffOn ℝ ∞ (fun x : Space n => u (x,t)) (Metric.ball 0 2) := by
  have hmap : ContDiff ℝ ∞ (fun x : Space n => (x,t)) := contDiff_id.prodMk contDiff_const
  exact hu.comp hmap.contDiffOn (fun x hx => ⟨hx,by linarith only [ht.1],ht.2⟩)

/-- Actual strict middle-layer measure and gradient disintegrate in time.
Cauchy--Schwarz uses the true positive-part weak gradient and its proved energy. -/
theorem dg_intermediate_band_cauchy {n : ℕ} {u : Point n → ℝ} {E : ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0))
    (hEI : Integrable (fun z => dgGradientSq (dgTruncationGradient 1 0 u z))
      (productVolume (Metric.ball 0 (7/4)) (Ioo (-3) 0)))
    (hEB : dgCylinderIntegral (Metric.ball 0 (7/4)) (-3) 0
      (fun z => dgGradientSq (dgTruncationGradient 1 0 u z)) ≤ E) :
    let O := Metric.ball (0 : Space n) (7/4)
    let S := dgMiddleCylinder n ∩ {z | 0 < u z ∧ u z < 1/2}
    let m := fun t : ℝ => volume.real (O ∩ {x | 0 < u (x,t) ∧ u (x,t) < 1/2})
    let g := fun t : ℝ => ∫ x in O ∩ {x | 0 < u (x,t) ∧ u (x,t) < 1/2}, ‖fderiv ℝ (fun y => u (y,t)) x‖
    Integrable m (volume.restrict (Ioo (-3) 0)) ∧
    (∫ t in Ioo (-3) 0, m t) = volume.real S ∧
    Integrable g (volume.restrict (Ioo (-3) 0)) ∧
    (∫ t in Ioo (-3) 0, g t) ≤ Real.sqrt E*Real.sqrt (volume.real S) := by
  let O : Set (Space n) := Metric.ball 0 (7/4)
  let J : Set ℝ := Ioo (-3) 0
  let S := dgMiddleCylinder n ∩ {z | 0 < u z ∧ u z < 1/2}
  let m := fun t : ℝ => volume.real (O ∩ {x | 0 < u (x,t) ∧ u (x,t) < 1/2})
  let g := fun t : ℝ => ∫ x in O ∩ {x | 0 < u (x,t) ∧ u (x,t) < 1/2}, ‖fderiv ℝ (fun y => u (y,t)) x‖
  let μ := productVolume O J
  let : IsFiniteMeasure μ := ⟨dg_cylinder_measure_lt_top 0 (7/4) (-3) 0⟩
  have hMU : dgMiddleCylinder n ⊆ Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0 :=
    Set.prod_mono (Metric.ball_subset_ball (by norm_num)) (Ioo_subset_Ioo (by norm_num) le_rfl)
  have hMC : ContinuousOn u (dgMiddleCylinder n) := hu.continuousOn.mono hMU
  have hS : MeasurableSet S := dg_local_band_measurable (Metric.isOpen_ball.prod isOpen_Ioo) hMC 0 (1/2)
  have hsub : S ⊆ O ×ˢ J := inter_subset_left
  have hSlice (t : ℝ) (ht : t ∈ J) : {x : Space n | (x,t) ∈ S} =
      O ∩ {x | 0 < u (x,t) ∧ u (x,t) < 1/2} := by
    change t ∈ Ioo (-3:ℝ) 0 at ht
    ext x
    simp only [S,dgMiddleCylinder,O,mem_ofPred_eq,mem_inter_iff,mem_prod,ht,and_true]
  obtain ⟨hMassI,hMassEq⟩ := dg_integral_slice_measure measurableSet_ball measurableSet_Ioo hS
    measure_ball_lt_top (by simp [Real.volume_Ioo]) hsub
  have hmEq : (fun t => volume.real {x : Space n | (x,t) ∈ S}) =ᵐ[volume.restrict J] m := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [hSlice t ht]
  have hmI : Integrable m (volume.restrict J) := hMassI.congr hmEq
  have hmIntegral : (∫ t in J, m t) = volume.real S := by
    rw [←integral_congr_ae hmEq]
    exact hMassEq
  let p := dgTruncationGradientNorm 1 0 u
  let q : Point n → ℝ := S.indicator (fun _ => 1)
  have hp : AEStronglyMeasurable p μ := by
    rw [show μ = volume.restrict (dgMiddleCylinder n) from dg_productVolume_eq_restrict _ _]
    exact dgTruncationGradientNorm_aestronglyMeasurable (Metric.isOpen_ball.prod isOpen_Ioo) (hu.mono hMU) 1 0
  have hq : AEStronglyMeasurable q μ := (stronglyMeasurable_const.indicator hS).aestronglyMeasurable
  have hpEq (z : Point n) : (p z)^2 = dgGradientSq (dgTruncationGradient 1 0 u z) :=
    Real.sq_sqrt (dgGradientSq_nonneg _)
  have hqEq (z : Point n) : (q z)^2 = q z := by
    by_cases hz : z ∈ S <;> simp [q,hz]
  have hpI : Integrable (fun z => (p z)^2) μ := hEI.congr (.of_forall fun z => (hpEq z).symm)
  have hqI : Integrable q μ := (integrable_const (1:ℝ)).indicator hS
  have hq2I : Integrable (fun z => (q z)^2) μ := hqI.congr (.of_forall fun z => (hqEq z).symm)
  have hqIntegral : (∫ z, (q z)^2 ∂μ) = volume.real S := by
    rw [integral_congr_ae (.of_forall hqEq),show μ = volume.restrict (dgMiddleCylinder n) from dg_productVolume_eq_restrict _ _]
    exact dg_indicator_subset_integral hS inter_subset_left
  obtain ⟨hPQ,hBound⟩ := dg_integral_mul_cauchy hp hq (.of_forall fun z => Real.sqrt_nonneg _)
    (.of_forall fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) z) hpI hq2I
  have hTotal : (∫ z, p z*q z ∂μ) ≤ Real.sqrt E*Real.sqrt (volume.real S) := by
    rw [hqIntegral] at hBound
    have hPE : (∫ z, (p z)^2 ∂μ) ≤ E := by
      rw [integral_congr_ae (.of_forall hpEq)]
      exact hEB
    exact hBound.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hPE) (Real.sqrt_nonneg _))
  have hGradNorm (x : Space n) (t : ℝ) (hpos : 0 < u (x,t)) :
      p (x,t) = ‖fderiv ℝ (fun y => u (y,t)) x‖ := by
    have hVec : dgTruncationGradient 1 0 u (x,t) = fun i => d (fun y => u (y,t)) x i := by
      ext i
      simp only [dgTruncationGradient,one_mul,hpos,ite_true,dgGradient]
    dsimp only [p,dgTruncationGradientNorm]
    rw [hVec]
    exact (dg_fderiv_norm_eq_sqrt_gradientSq (fun y => u (y,t)) x).symm
  have hGradSlice (t : ℝ) (ht : t ∈ J) : (∫ x in O, p (x,t)*q (x,t)) = g t := by
    let B := O ∩ {x | 0 < u (x,t) ∧ u (x,t) < 1/2}
    have hB : MeasurableSet B := dg_local_band_measurable Metric.isOpen_ball
      ((dg_intermediate_slice_smooth hu ht).continuousOn.mono (Metric.ball_subset_ball (by norm_num))) 0 (1/2)
    have he : (fun x => p (x,t)*q (x,t)) =ᵐ[volume.restrict O]
        B.indicator (fun x => ‖fderiv ℝ (fun y => u (y,t)) x‖) := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      by_cases hxB : x ∈ B
      · have hxS : (x,t) ∈ S := ⟨⟨hx,ht⟩,hxB.2⟩
        rw [Set.indicator_of_mem hxB]
        simp only [q,Set.indicator_of_mem hxS,mul_one,hGradNorm x t hxB.2.1]
      · have hxS : (x,t) ∉ S := fun hh => hxB ⟨hx,hh.2⟩
        rw [Set.indicator_of_notMem hxB]
        simp only [q,Set.indicator_of_notMem hxS,mul_zero]
    rw [integral_congr_ae he,integral_indicator hB,Measure.restrict_restrict hB,
      inter_eq_left.mpr (show B ⊆ O from inter_subset_left)]
  have hGEq : (fun t => ∫ x in O, p (x,t)*q (x,t)) =ᵐ[volume.restrict J] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hGradSlice t ht
  have hgI : Integrable g (volume.restrict J) := hPQ.integral_prod_right.congr hGEq
  have hgIntegral : (∫ t in J, g t) = ∫ z, p z*q z ∂μ := by
    rw [←integral_congr_ae hGEq]
    exact (integral_prod_symm _ hPQ).symm
  exact ⟨hmI,hmIntegral,hgI,hgIntegral ▸ hTotal⟩


/-- The second De Giorgi measure lemma for the actual classical divergence
operator. The positive constant precedes every candidate field. Only the upper
bound u≤1 is used; the measured middle layer is literally the prescribed MID. -/
theorem dg_intermediate_value {n : ℕ} (hn : 0 < n) {ν L α β : ℝ}
    (hν : 0 < ν) (hνL : ν ≤ L) (hα : 0 < α) (_hα1 : α ≤ 1)
    (hβ : 0 < β) (_hβ1 : β ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ),
      DGClassicalFields (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0) A c f u →
      ClassicalDivEq (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0) A c f u →
      DGUniformBounds (Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0) A c f ν L 1 1 →
      ContinuousOn u (Metric.ball (0 : Space n) 2 ×ˢ Icc (-7/2) 0) →
      (∀ z ∈ Metric.ball (0 : Space n) 2 ×ˢ Ioc (-4) 0, u z ≤ 1) →
      α*volume.real (dgEarlyCylinder n) ≤ volume.real (dgEarlyCylinder n ∩ {z | u z ≤ 0}) →
      β*volume.real (dgLateCylinder n) ≤ volume.real (dgLateCylinder n ∩ {z | 1/2 ≤ u z}) →
      δ ≤ volume.real (dgMiddleCylinder n ∩ {z | 0 < u z ∧ u z < 1/2}) := by
  obtain ⟨φ,E,A₀,hφ,hcφ,hφS,hφrange,hφone,hE,hA₀,hControl⟩ := dg_intermediate_mean_control hn hν hνL
  let O : Set (Space n) := Metric.ball 0 (7/4)
  let V := volume.real (Metric.ball (0 : Space n) 1)
  have hBall (r : ℝ) (hr : 0 < r) : 0 < volume.real (Metric.ball (0 : Space n) r) :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 hr)) measure_ball_lt_top.ne
  have hV : 0 < V := hBall 1 (by norm_num)
  let K := (2:ℝ)^(2*n+1)*(7/4)*volume.real O
  have hW : 0 < volume.real O := hBall (7/4) (by norm_num)
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨δ,hδ,hCross⟩ := dg_direct_mean_crossing_bound hV hE hA₀ hK hα hβ
  refine ⟨δ,hδ,?_⟩
  intro A c f u hf hpde hb hu hupper hEarly hLate
  have hUpperClosed : ∀ z ∈ Metric.ball (0 : Space n) 2 ×ˢ Icc (-7/2) 0, u z ≤ 1 := by
    intro z hz
    exact hupper z ⟨hz.1,lt_of_lt_of_le (by norm_num : (-4:ℝ) < -7/2) hz.2.1,hz.2.2⟩
  obtain ⟨hEI,hEB,hcont,hinc⟩ := hControl A c f u hf hpde hb hu hUpperClosed
  let h := dgTruncationMean O φ 1 0 u
  let z := fun t : ℝ => volume.real (Metric.ball (0 : Space n) 1 ∩ {x | u (x,t) ≤ 0})
  let m := fun t : ℝ => volume.real (O ∩ {x | 0 < u (x,t) ∧ u (x,t) < 1/2})
  let g := fun t : ℝ => ∫ x in O ∩ {x | 0 < u (x,t) ∧ u (x,t) < 1/2}, ‖fderiv ℝ (fun y => u (y,t)) x‖
  let S := dgMiddleCylinder n ∩ {z | 0 < u z ∧ u z < 1/2}
  let η := volume.real S
  obtain ⟨hmI,hmIntegral,hgI,hgBound⟩ := dg_intermediate_band_cauchy hf.2.2.2 hEI hEB
  have hVal (t : ℝ) : h t = ∫ x in O, φ x*dgPositivePart (u (x,t)) := by
    simp only [h,dgTruncationMean,dgTruncation,one_mul,sub_zero]
  have hUpperSlice (t : ℝ) (ht : t ∈ Ioo (-3:ℝ) 0) (x : Space n) (hx : x ∈ Metric.ball (0 : Space n) 2) : u (x,t) ≤ 1 :=
    hupper (x,t) ⟨hx,by linarith only [ht.1],ht.2.le⟩
  have hEarlyU : dgEarlyCylinder n ⊆ Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0 :=
    Set.prod_mono (Metric.ball_subset_ball (by norm_num)) (Ioo_subset_Ioo (by norm_num) (by norm_num))
  have hLateU : dgLateCylinder n ⊆ Metric.ball (0 : Space n) 2 ×ˢ Ioo (-4) 0 :=
    Set.prod_mono (Metric.ball_subset_ball (by norm_num)) (Ioo_subset_Ioo (by norm_num) le_rfl)
  let Z := dgEarlyCylinder n ∩ {p | u p ≤ 0}
  let H := dgLateCylinder n ∩ {p | 1/2 ≤ u p}
  have hZ : MeasurableSet Z := dg_local_sublevel_measurable (Metric.isOpen_ball.prod isOpen_Ioo)
    (hf.2.2.2.continuousOn.mono hEarlyU) 0
  have hH : MeasurableSet H := dg_local_superlevel_measurable (Metric.isOpen_ball.prod isOpen_Ioo)
    (hf.2.2.2.continuousOn.mono hLateU) (1/2)
  have hZE (t : ℝ) (ht : t ∈ Ioo (-3:ℝ) (-2)) : {x : Space n | (x,t) ∈ Z} =
      Metric.ball (0 : Space n) 1 ∩ {x | u (x,t) ≤ 0} := by
    ext x
    simp only [Z,dgEarlyCylinder,mem_ofPred_eq,mem_inter_iff,mem_prod,ht,and_true]
  have hHE (t : ℝ) (ht : t ∈ Ioo (-1:ℝ) 0) : {x : Space n | (x,t) ∈ H} =
      Metric.ball (0 : Space n) 1 ∩ {x | 1/2 ≤ u (x,t)} := by
    ext x
    simp only [H,dgLateCylinder,mem_ofPred_eq,mem_inter_iff,mem_prod,ht,and_true]
  obtain ⟨hzMassI,hzMassEq⟩ := dg_integral_slice_measure measurableSet_ball measurableSet_Ioo hZ
    measure_ball_lt_top (by simp [Real.volume_Ioo]) (show Z ⊆ Metric.ball (0 : Space n) 1 ×ˢ Ioo (-3) (-2) from inter_subset_left)
  have hzEq : (fun t => volume.real {x : Space n | (x,t) ∈ Z}) =ᵐ[volume.restrict (Ioo (-3:ℝ) (-2))] z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [hZE t ht]
  have hzI : Integrable z (volume.restrict (Ioo (-3:ℝ) (-2))) := hzMassI.congr hzEq
  have hzIntegral : (∫ t in Ioo (-3:ℝ) (-2), z t) = volume.real Z := by
    rw [←integral_congr_ae hzEq]
    exact hzMassEq
  let l := fun t : ℝ => volume.real (Metric.ball (0 : Space n) 1 ∩ {x | 1/2 ≤ u (x,t)})
  obtain ⟨hlMassI,hlMassEq⟩ := dg_integral_slice_measure measurableSet_ball measurableSet_Ioo hH
    measure_ball_lt_top (by simp [Real.volume_Ioo]) (show H ⊆ Metric.ball (0 : Space n) 1 ×ˢ Ioo (-1) 0 from inter_subset_left)
  have hlEq : (fun t => volume.real {x : Space n | (x,t) ∈ H}) =ᵐ[volume.restrict (Ioo (-1:ℝ) 0)] l := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [hHE t ht]
  have hlI : Integrable l (volume.restrict (Ioo (-1:ℝ) 0)) := hlMassI.congr hlEq
  have hlIntegral : (∫ t in Ioo (-1:ℝ) 0, l t) = volume.real H := by
    rw [←integral_congr_ae hlEq]
    exact hlMassEq
  have hVolEarly : volume.real (dgEarlyCylinder n) = V := by
    change ((volume : Measure (Space n)).prod volume).real (Metric.ball 0 1 ×ˢ Ioo (-3:ℝ) (-2)) = V
    rw [measureReal_prod_prod]
    norm_num [Measure.real,V,Real.volume_Ioo]
  have hVolLate : volume.real (dgLateCylinder n) = V := by
    change ((volume : Measure (Space n)).prod volume).real (Metric.ball 0 1 ×ˢ Ioo (-1:ℝ) 0) = V
    rw [measureReal_prod_prod]
    norm_num [Measure.real,V,Real.volume_Ioo]
  have hzEarly : α*V ≤ ∫ t in Ioo (-3) (-2), z t := by
    rw [hzIntegral]
    simpa only [hVolEarly] using hEarly
  have hlLate : β*V ≤ ∫ t in Ioo (-1) 0, l t := by
    rw [hlIntegral]
    simpa only [hVolLate] using hLate
  have hLateMeanI : Integrable h (volume.restrict (Ioo (-1:ℝ) 0)) :=
    ((hcont.integrableOn_compact (μ := volume) isCompact_Icc)).mono_set
      (fun t ht => ⟨by linarith only [ht.1],ht.2.le⟩)
  have hLatePoint : ∀ᵐ t ∂volume.restrict (Ioo (-1:ℝ) 0), (1/2)*l t ≤ h t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htJ : t ∈ Ioo (-3:ℝ) 0 := ⟨by linarith only [ht.1],ht.2⟩
    have hh := (dg_intermediate_spatial_masses (dg_intermediate_slice_smooth hf.2.2.2 htJ)
      hφ hφrange hφS hφone (hUpperSlice t htJ)).1
    simpa only [hVal] using hh
  have hhLate : β*V/2 ≤ ∫ t in Ioo (-1) 0, h t := by
    have hh := integral_mono_ae (hlI.const_mul (1/2)) hLateMeanI hLatePoint
    rw [integral_const_mul] at hh
    calc
      _ = (1/2)*(β*V) := by ring
      _ ≤ (1/2)*(∫ t in Ioo (-1) 0, l t) := mul_le_mul_of_nonneg_left hlLate (by norm_num)
      _ ≤ _ := hh
  apply hCross h z m g η ENNReal.toReal_nonneg hcont hinc hzI hmI hgI
    (fun t _ => ENNReal.toReal_nonneg) (fun t _ => ⟨ENNReal.toReal_nonneg,integral_nonneg fun x => norm_nonneg _⟩)
    hzEarly hhLate
  · intro t ht
    have htJ : t ∈ Ioo (-3:ℝ) 0 := ⟨ht.1,by linarith only [ht.2]⟩
    have hh := dg_intermediate_zero_mean_bound (dg_intermediate_slice_smooth hf.2.2.2 htJ)
      hφ hφrange (hUpperSlice t htJ)
    simpa only [hVal,K,O] using hh
  · intro H₀ hH₀ hHsmall t ht hLo hHi hM hM'
    rw [hVal t] at hLo hHi
    have hh := dg_intermediate_window_gradient hH₀ hHsmall (dg_intermediate_slice_smooth hf.2.2.2 ht)
      hφ hφrange hφS hφone (hUpperSlice t ht) hLo hHi hM hM'
    have hdiv : (V*H₀/8)/K ≤ g t := (div_le_iff₀ hK).mpr (by simpa only [V,K,O,mul_comm] using hh)
    simpa only [div_div] using hdiv
  · exact hmIntegral.le
  · exact hgBound

end Yau.LeafProofs.L16Aux
