import Yau.LeafProofs.L05PucciHarnackAffineMeasure

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackCube {n : ℕ} (c : Space n) (r : ℝ) : Set (Space n) :=
  {x | ∀ i : Yau.RIdx n, -(r/2) ≤ inner ℝ (x-c) (Yau.realVec i) ∧
    inner ℝ (x-c) (Yau.realVec i) < r/2}

def harnackBox {n : ℕ} (c : Space n) (r a : ℝ) : Set (Point n) :=
  harnackCube c r ×ˢ Ioc a (a+r^2)

theorem harnack_cube_measurable {n : ℕ} (c : Space n) (r : ℝ) :
    MeasurableSet (harnackCube c r) := by
  unfold harnackCube
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have hCont : Continuous (fun x : Space n => inner ℝ (x-c) (Yau.realVec i)) := by fun_prop
  exact (isClosed_le continuous_const hCont).measurableSet.inter
    (isOpen_lt hCont continuous_const).measurableSet

theorem harnack_box_measurable {n : ℕ} (c : Space n) (r a : ℝ) :
    MeasurableSet (harnackBox c r a) :=
  (harnack_cube_measurable c r).prod measurableSet_Ioc

theorem harnack_cube_contains_ball {n : ℕ} (c : Space n) {r : ℝ} :
    Metric.ball c (r/2) ⊆ harnackCube c r := by
  intro x hx i
  have hx' : ‖x-c‖ < r/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have hn : ‖Yau.realVec i‖=1 := by
    simpa only [complexVector_realOrthonormalBasis_apply] using
      (complexVector_realOrthonormalBasis n).orthonormal.norm_eq_one i
  have h : |inner ℝ (x-c) (Yau.realVec i)| < r/2 := by
    calc
      _ ≤ ‖x-c‖*‖Yau.realVec i‖ := abs_real_inner_le_norm _ _
      _ < r/2 := by simpa only [hn,mul_one] using hx'
  exact ⟨(abs_lt.mp h).1.le,(abs_lt.mp h).2⟩

theorem harnack_cube_subset_closedBall {n : ℕ} (c : Space n) {r : ℝ} (hr : 0 ≤ r) :
    harnackCube c r ⊆ Metric.closedBall c (Real.sqrt (2*n)*r/2) := by
  intro x hx
  have hCoord (i : Yau.RIdx n) : (inner ℝ (Yau.realVec i) (x-c))^2 ≤ (r/2)^2 := by
    have hi := hx i
    rw [real_inner_comm] at hi
    nlinarith [sq_nonneg (inner ℝ (Yau.realVec i) (x-c)-r/2),
      sq_nonneg (inner ℝ (Yau.realVec i) (x-c)+r/2)]
  have hSum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hCoord i)
  have hNorm : ‖x-c‖^2 ≤ (2*n)*(r/2)^2 := by
    simpa only [pow_two,realVec_coordinates_norm_sq,Finset.sum_const,Finset.card_univ,
      Yau.RIdx,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,
      mul_comm (n : ℝ) 2] using hSum
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*n)
  have hs2 : (Real.sqrt (2*n)*r/2)^2=(2*n)*(r/2)^2 := by
    rw [div_pow,mul_pow,hs]
    ring
  have hp : 0 ≤ Real.sqrt (2*n)*r/2 := by positivity
  change dist x c ≤ Real.sqrt (2*n)*r/2
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x-c)]

theorem harnack_cube_measure_ne_top {n : ℕ} (c : Space n) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space n)) (harnackCube c r) ≠ ⊤ :=
  ne_top_of_le_ne_top (isCompact_closedBall c (Real.sqrt (2*n)*r/2)).measure_ne_top
    (measure_mono (harnack_cube_subset_closedBall c hr))

theorem harnack_cube_measure_pos {n : ℕ} (c : Space n) {r : ℝ} (hr : 0 < r) :
    0 < (volume : Measure (Space n)) (harnackCube c r) := by
  have hBall : 0 < (volume : Measure (Space n)) (Metric.ball c (r/2)) :=
    Metric.isOpen_ball.measure_pos volume ⟨c,Metric.mem_ball_self (half_pos hr)⟩
  exact hBall.trans_le (measure_mono (harnack_cube_contains_ball c))

theorem harnack_cube_affine_preimage {n : ℕ} (c : Space n) {r : ℝ} (hr : 0 < r) :
    (fun x : Space n => c+r • x) ⁻¹' harnackCube c r=harnackCube (0 : Space n) 1 := by
  ext x
  simp only [mem_preimage,harnackCube,mem_ofPred_eq,add_sub_cancel_left,sub_zero,
    real_inner_smul_left]
  constructor
  · intro hx i
    have hi := hx i
    constructor
    · apply (mul_le_mul_iff_of_pos_left hr).mp
      convert hi.1 using 1; ring
    · apply (mul_lt_mul_iff_of_pos_left hr).mp
      convert hi.2 using 1; ring
  · intro hx i
    have hi := hx i
    constructor
    · convert mul_le_mul_of_nonneg_left hi.1 hr.le using 1; ring
    · convert mul_lt_mul_of_pos_left hi.2 hr using 1; ring

theorem harnack_cube_volume {n : ℕ} (c : Space n) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Space n)) (harnackCube c r)=
      ENNReal.ofReal (r^(2*n))*(volume : Measure (Space n)) (harnackCube (0 : Space n) 1) := by
  have hScale := Measure.map_addHaar_smul (volume : Measure (Space n)) hr.ne'
  rw [complexVector_finrank_real,abs_of_pos (inv_pos.mpr (pow_pos hr _))] at hScale
  have hMap : Measure.map (fun x : Space n => c+r • x) volume=
      ENNReal.ofReal ((r^(2*n))⁻¹) • (volume : Measure (Space n)) := by
    have hFun : (fun x : Space n => c+r • x)=(fun x : Space n => x+c) ∘ (fun x : Space n => r • x) := by
      funext x
      simp only [Function.comp_apply,add_comm]
    rw [hFun,← Measure.map_map (by fun_prop) (by fun_prop),hScale,
      Measure.map_smul _ (by fun_prop),Measure.IsAddRightInvariant.map_add_right_eq_self]
  have hVol := congrArg (fun μ : Measure (Space n) => μ (harnackCube c r)) hMap
  rw [Measure.map_apply (by fun_prop) (harnack_cube_measurable c r),
    harnack_cube_affine_preimage c hr,Measure.smul_apply,smul_eq_mul] at hVol
  have hMul := congrArg (fun v : ENNReal => ENNReal.ofReal (r^(2*n))*v) hVol
  rw [← mul_assoc,← ENNReal.ofReal_mul (pow_nonneg hr.le _),
    mul_inv_cancel₀ (pow_ne_zero _ hr.ne'),ENNReal.ofReal_one,one_mul] at hMul
  exact hMul.symm

def harnackCubeVolume (n : ℕ) : ℝ :=
  ((volume : Measure (Space n)) (harnackCube (0 : Space n) 1)).toReal

theorem harnack_cubeVolume_pos (n : ℕ) : 0 < harnackCubeVolume n :=
  ENNReal.toReal_pos (harnack_cube_measure_pos 0 (by norm_num : (0 : ℝ) < 1)).ne'
    (harnack_cube_measure_ne_top 0 (by norm_num : (0 : ℝ) ≤ 1))

theorem harnack_box_volume {n : ℕ} (c : Space n) {r : ℝ} (hr : 0 < r) (a : ℝ) :
    (volume : Measure (Point n)) (harnackBox c r a)=
      ENNReal.ofReal (r^(2*n+2))*(volume : Measure (Space n)) (harnackCube (0 : Space n) 1) := by
  rw [harnackBox,Measure.volume_eq_prod,Measure.prod_prod,harnack_cube_volume c hr,Real.volume_Ioc]
  have hSub : a+r^2-a=r^2 := by ring
  rw [hSub,mul_right_comm,← ENNReal.ofReal_mul (pow_nonneg hr.le _),← pow_add]

theorem harnack_box_mu {n : ℕ} (c : Space n) {r : ℝ} (hr : 0 < r) (a : ℝ) :
    harnackMu (harnackBox c r a)=harnackCubeVolume n*r^(2*n+2) := by
  rw [harnackMu,harnack_box_volume c hr,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  exact mul_comm _ _

theorem harnack_box_measure_ne_top {n : ℕ} (c : Space n) {r : ℝ} (hr : 0 < r) (a : ℝ) :
    (volume : Measure (Point n)) (harnackBox c r a) ≠ ⊤ := by
  rw [harnack_box_volume c hr]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (harnack_cube_measure_ne_top 0 (by norm_num))

theorem harnack_box_mu_pos {n : ℕ} (c : Space n) {r : ℝ} (hr : 0 < r) (a : ℝ) :
    0 < harnackMu (harnackBox c r a) := by
  rw [harnack_box_mu c hr]
  exact mul_pos (harnack_cubeVolume_pos n) (pow_pos hr _)

theorem harnack_box_affine_preimage {n : ℕ} (c : Space n) {r a : ℝ} (hr : 0 < r) :
    (harnackAffine c r (a-r^2) (r^2)) ⁻¹' harnackBox c r a=
      harnackBox (0 : Space n) 1 0 := by
  ext z
  have hx : c+r • z.1∈harnackCube c r ↔ z.1∈harnackCube (0 : Space n) 1 :=
    Set.ext_iff.mp (harnack_cube_affine_preimage c hr) z.1
  change harnackAffine c r (a-r^2) (r^2) z∈harnackBox c r a ↔ z∈harnackBox (0 : Space n) 1 0
  rw [harnack_affine_apply]
  change (c+r • z.1∈harnackCube c r ∧ a < a-r^2+r^2*(z.2+1) ∧
    a-r^2+r^2*(z.2+1) ≤ a+r^2) ↔
      (z.1∈harnackCube (0 : Space n) 1 ∧ (0 : ℝ) < z.2 ∧ z.2 ≤ 0+1^2)
  rw [hx]
  have hr2 := sq_pos_of_ne_zero hr.ne'
  constructor
  · rintro ⟨hx,hl,hu⟩
    have hl' : r^2*0 < r^2*z.2 := by nlinarith
    have hu' : r^2*z.2 ≤ r^2*1 := by nlinarith
    exact ⟨hx,(mul_lt_mul_iff_of_pos_left hr2).mp hl',
      by simpa using (mul_le_mul_iff_of_pos_left hr2).mp hu'⟩
  · rintro ⟨hx,hl,hu⟩
    have hl' := mul_lt_mul_of_pos_left hl hr2
    have hu' := mul_le_mul_of_nonneg_left hu hr2.le
    exact ⟨hx,by nlinarith,by nlinarith⟩

theorem harnack_mu_affine_preimage {n : ℕ} (c : Space n) {R a T : ℝ}
    (hR : 0 < R) (hT : 0 < T) {E : Set (Point n)} (hE : MeasurableSet E) :
    harnackMu E=harnackAffineJacobian n R T*
      harnackMu (harnackAffine c R a T ⁻¹' E) := by
  have hMap := harnack_map_affine_volume (a := a) c hR hT
  have hVol := congrArg (fun μ : Measure (Point n) => μ E) hMap
  rw [Measure.map_apply (harnack_affine_contDiff c R a T).continuous.measurable hE,
    Measure.smul_apply,smul_eq_mul] at hVol
  have hJ := harnack_affineJacobian_pos (n := n) hR hT
  have hEq := congrArg ENNReal.toReal hVol
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr hJ.le)] at hEq
  change harnackMu (harnackAffine c R a T ⁻¹' E)=(harnackAffineJacobian n R T)⁻¹*harnackMu E at hEq
  rw [hEq]
  field_simp [hJ.ne']

end Yau.LeafProofs.L05Aux






