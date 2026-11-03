import Yau.LeafProofs.L16DeGiorgiSobolev
import Yau.LeafProofs.L16DeGiorgiIteration

/-! The normalized small-upper-set De Giorgi lemma uses actual finite cylinder
measures and the proved signed-level Caccioppoli and parabolic inequalities. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators NNReal ENNReal
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Open-time backward cylinder, for actual product Lebesgue integration. -/
def dgSmCylinderOpen {n : ℕ} (R : ℝ) : Set (Point n) :=
  Metric.ball 0 R ×ˢ Ioo (-(R^2)) 0

/-- Backward cylinder with its terminal time face. -/
def dgSmCylinder {n : ℕ} (R : ℝ) : Set (Point n) :=
  Metric.ball 0 R ×ˢ Ioc (-(R^2)) 0

/-- Every superlevel measure below is the real value of a genuinely finite measure. -/
def dgSmSuperlevelMeasure {n : ℕ} (R k : ℝ) (u : Point n → ℝ) : ℝ :=
  (productVolume (Metric.ball 0 R) (Ioo (-(R^2)) 0) {z | k < u z}).toReal

def dgSmRadius (j : ℕ) : ℝ := 1/2+(1/2 : ℝ)^(j+2)
def dgSmLevel (j : ℕ) : ℝ := (1-(1/2 : ℝ)^j)/2
def dgSmSupportRadius (j : ℕ) : ℝ := (dgSmRadius j+dgSmRadius (j+1))/2

@[simp] theorem dgSmRadius_zero : dgSmRadius 0 = 3/4 := by norm_num [dgSmRadius]
@[simp] theorem dgSmLevel_zero : dgSmLevel 0 = 0 := by norm_num [dgSmLevel]

theorem dgSmRadius_bounds (j : ℕ) : 1/2 < dgSmRadius j ∧ dgSmRadius j ≤ 3/4 := by
  have hp := pow_pos (by norm_num : (0 : ℝ) < 1/2) (j+2)
  have hpow : (1/2 : ℝ)^(j+2) ≤ 1/4 := by
    rw [pow_add]
    have hle := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) (n := j)
    norm_num at *
    nlinarith
  dsimp only [dgSmRadius]
  constructor <;> linarith

theorem dgSmRadius_decreasing (j : ℕ) : dgSmRadius (j+1) < dgSmRadius j := by
  have hp := pow_pos (by norm_num : (0 : ℝ) < 1/2) (j+2)
  dsimp only [dgSmRadius]
  rw [show j+1+2 = (j+2)+1 by omega,pow_succ]
  nlinarith

theorem dgSmLevel_bounds (j : ℕ) : 0 ≤ dgSmLevel j ∧ dgSmLevel j < 1/2 := by
  have hp := pow_pos (by norm_num : (0 : ℝ) < 1/2) j
  have hle := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) (n := j)
  dsimp only [dgSmLevel]
  constructor <;> linarith

theorem dgSmLevel_gap (j : ℕ) : dgSmLevel (j+1)-dgSmLevel j = (1/2 : ℝ)^(j+2) := by
  simp only [dgSmLevel,pow_add,pow_succ]
  ring

theorem dgSmSupportRadius_bounds (j : ℕ) :
    0 < dgSmRadius (j+1) ∧ dgSmRadius (j+1) < dgSmSupportRadius j ∧
      dgSmSupportRadius j < dgSmRadius j := by
  have hpos := (dgSmRadius_bounds (j+1)).1
  have hd := dgSmRadius_decreasing j
  dsimp only [dgSmSupportRadius]
  constructor
  · linarith
  constructor <;> linarith

/-- A fixed smooth step has a universal derivative bound; it precedes all fields. -/
theorem dgSmStep_derivative_bound : ∃ M : ℝ, 0 < M ∧ ∀ q, |deriv Real.smoothTransition q| ≤ M := by
  have hθ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hc : Continuous (deriv Real.smoothTransition) := (contDiff_infty_iff_deriv.mp hθ).2.continuous
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hc.continuousOn
  refine ⟨|C|+1,by positivity,?_⟩
  intro q
  by_cases hq : q ∈ Icc (0 : ℝ) 1
  · have hh := hC q hq
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (by linarith [le_abs_self C])
  · have hz : deriv Real.smoothTransition q = 0 := by
      change ¬(0 ≤ q ∧ q ≤ 1) at hq
      rcases not_and_or.mp hq with hq | hq
      · have hq : q < 0 := lt_of_not_ge hq
        have he : Real.smoothTransition =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
          filter_upwards [gt_mem_nhds hq] with y hy
          exact Real.smoothTransition.zero_of_nonpos hy.le
        exact he.deriv_eq.trans (deriv_const q 0)
      · have hq : 1 < q := lt_of_not_ge hq
        have he : Real.smoothTransition =ᶠ[𝓝 q] fun _ => (1 : ℝ) := by
          filter_upwards [lt_mem_nhds hq] with y hy
          exact Real.smoothTransition.one_of_one_le hy.le
        exact he.deriv_eq.trans (deriv_const q 1)
    rw [hz,abs_zero]
    positivity

/-- A concrete smooth cutoff; the support radius lies strictly inside the
Caccioppoli ball, and its inner time threshold may be larger than the bottom. -/
def dgSmCutoff {n : ℕ} (ρ α a b : ℝ) (z : Point n) : ℝ :=
  Real.smoothTransition ((ρ^2-‖z.1‖^2)/(ρ^2-α^2))*
    Real.smoothTransition ((z.2-a)/(b-a))

theorem dgSmCutoff_contDiff {n : ℕ} (ρ α a b : ℝ) :
    ContDiff ℝ ∞ (dgSmCutoff (n := n) ρ α a b) := by
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub ((contDiff_norm_sq ℝ).comp contDiff_fst)).div_const _)
  · exact Real.smoothTransition.contDiff.comp ((contDiff_snd.sub contDiff_const).div_const _)

theorem dgSmCutoff_range {n : ℕ} (ρ α a b : ℝ) (z : Point n) :
    0 ≤ dgSmCutoff ρ α a b z ∧ dgSmCutoff ρ α a b z ≤ 1 := by
  exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)⟩

theorem dgSmCutoff_zero_spatial {n : ℕ} {ρ α a b : ℝ} (hα : 0 ≤ α) (hαρ : α < ρ)
    {z : Point n} (hz : ρ ≤ ‖z.1‖) : dgSmCutoff ρ α a b z = 0 := by
  have hd : 0 < ρ^2-α^2 := by nlinarith
  have hn : ρ^2-‖z.1‖^2 ≤ 0 := by nlinarith [norm_nonneg z.1]
  rw [dgSmCutoff,Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hn hd.le),zero_mul]

theorem dgSmCutoff_one {n : ℕ} {ρ α a b : ℝ} (hα : 0 ≤ α) (hαρ : α < ρ) (hab : a < b)
    {z : Point n} (hx : ‖z.1‖ ≤ α) (ht : b ≤ z.2) : dgSmCutoff ρ α a b z = 1 := by
  have hd : 0 < ρ^2-α^2 := by nlinarith
  have hx' : 1 ≤ (ρ^2-‖z.1‖^2)/(ρ^2-α^2) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [norm_nonneg z.1]
  have ht' : 1 ≤ (z.2-a)/(b-a) := (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  rw [dgSmCutoff,Real.smoothTransition.one_of_one_le hx',Real.smoothTransition.one_of_one_le ht',one_mul]

theorem dgSmCutoff_bottom {n : ℕ} (ρ α a b : ℝ) (x : Space n) :
    dgSmCutoff ρ α a b (x,a) = 0 := by
  simp only [dgSmCutoff,sub_self,zero_div,Real.smoothTransition.zero,mul_zero]

theorem dgSmCutoff_admissible {n : ℕ} {r ρ α a b T : ℝ}
    (hα : 0 ≤ α) (hαρ : α < ρ) (hρr : ρ < r) :
    DGSpatialCutoff (Metric.ball (0 : Space n) r) a T (dgSmCutoff ρ α a b) := by
  refine ⟨dgSmCutoff_contDiff _ _ _ _,fun z _ => dgSmCutoff_range _ _ _ _ z,
    Metric.closedBall 0 ρ,isCompact_closedBall _ _,?_,?_⟩
  · exact Metric.closedBall_subset_ball hρr
  · intro z _ hz
    have hnorm : ρ < ‖z.1‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
    exact dgSmCutoff_zero_spatial hα hαρ hnorm.le

/-- The concrete cutoff has the expected actual time-derivative bound. -/
theorem dgSmCutoff_time_bound {n : ℕ} {M ρ α a b : ℝ} (hM : 0 ≤ M)
    (hθ : ∀ q, |deriv Real.smoothTransition q| ≤ M) (hab : a < b) (z : Point n) :
    |deriv (fun t => dgSmCutoff ρ α a b (z.1,t)) z.2| ≤ M/(b-a) := by
  have hθs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hd := (hθs.differentiable (by simp) ((z.2-a)/(b-a))).hasDerivAt.comp z.2
    (((hasDerivAt_id z.2).sub_const a).div_const (b-a))
  have hd' := hd.const_mul (Real.smoothTransition ((ρ^2-‖z.1‖^2)/(ρ^2-α^2)))
  have hdval : deriv (fun t => dgSmCutoff ρ α a b (z.1,t)) z.2 =
      Real.smoothTransition ((ρ^2-‖z.1‖^2)/(ρ^2-α^2))*
        (deriv Real.smoothTransition ((z.2-a)/(b-a))*(1/(b-a))) := by
    simpa only [dgSmCutoff,Function.comp_def,id_eq] using hd'.deriv
  rw [hdval,abs_mul,abs_mul,abs_div,abs_one,abs_of_pos (sub_pos.mpr hab),
    abs_of_nonneg (Real.smoothTransition.nonneg _)]
  calc
    _ ≤ 1*(M*(1/(b-a))) := by
      apply mul_le_mul (Real.smoothTransition.le_one _)
      · exact mul_le_mul_of_nonneg_right (hθ _) (by positivity)
      · positivity
      · norm_num
    _ = _ := by ring

/-- The actual spatial gradient norm is controlled by the radial gap. -/
theorem dgSmCutoff_gradient_bound {n : ℕ} {M ρ α a b : ℝ} (hM : 0 ≤ M)
    (hθ : ∀ q, |deriv Real.smoothTransition q| ≤ M) (hα : 0 ≤ α) (hαρ : α < ρ)
    (z : Point n) (hx : ‖z.1‖ ≤ 1) :
    dgGradientSq (dgGradient (dgSmCutoff ρ α a b) z) ≤ (2*M/(ρ^2-α^2))^2 := by
  let δ := ρ^2-α^2
  have hδ : 0 < δ := by dsimp only [δ]; nlinarith
  let x := z.1
  let η := Real.smoothTransition ((z.2-a)/(b-a))
  let q : Space n → ℝ := fun y => (ρ^2-‖y‖^2)/δ
  have ha : HasFDerivAt q ((-2/δ) • innerSL ℝ x) x := by
    convert (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub (ρ^2)).mul_const δ⁻¹) using 1
    · funext y
      dsimp only [q]
      rw [div_eq_mul_inv]
    · ext y
      simp only [smul_apply,smul_eq_mul,neg_apply]
      ring
  have hθs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hd := (hθs.differentiable (by simp) (q x)).hasDerivAt.comp_hasFDerivAt x ha
  have hd' := hd.mul_const η
  have hnorm : ‖fderiv ℝ (fun y => dgSmCutoff ρ α a b (y,z.2)) x‖ ≤ 2*M/δ := by
    change ‖fderiv ℝ (fun y => (Real.smoothTransition ∘ q) y*η) x‖ ≤ _
    rw [hd'.fderiv]
    simp only [norm_smul,Real.norm_eq_abs,innerSL_apply_norm,abs_div,abs_neg,
      abs_of_pos hδ,abs_of_pos (by norm_num : (0:ℝ) < 2),abs_of_nonneg (Real.smoothTransition.nonneg _)]
    have hη0 : 0 ≤ η := Real.smoothTransition.nonneg _
    have hη1 : η ≤ 1 := Real.smoothTransition.le_one _
    have hηabs : |η| ≤ 1 := by rwa [abs_of_nonneg hη0]
    calc
      _ ≤ 1*(M*(2/δ*1)) := by gcongr; exact hθ _
      _ = _ := by ring
  change dgGradientSq (fun i => d (fun y => dgSmCutoff ρ α a b (y,z.2)) z.1 i) ≤ _
  rw [← dg_fderiv_norm_sq]
  change ‖fderiv ℝ (fun y => dgSmCutoff ρ α a b (y,z.2)) x‖^2 ≤ _
  exact sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hnorm

/-- Radius gaps have genuine geometric lower bounds. -/
theorem dgSmRadius_gap_bounds (j : ℕ) :
    (1/2 : ℝ)^j/16 ≤ (dgSmSupportRadius j)^2-(dgSmRadius (j+1))^2 ∧
    (1/2 : ℝ)^j/8 ≤ (dgSmRadius j)^2-(dgSmRadius (j+1))^2 := by
  let q : ℝ := (1/2)^j
  have hq : 0 < q := pow_pos (by norm_num) _
  have hr : dgSmRadius j = 1/2+q/4 := by
    simp only [dgSmRadius,pow_add,q]; norm_num; ring
  have hr' : dgSmRadius (j+1) = 1/2+q/8 := by
    simp only [dgSmRadius,pow_add,pow_succ,q]; norm_num; ring
  have hρ : dgSmSupportRadius j = 1/2+3*q/16 := by
    rw [dgSmSupportRadius,hr,hr']; ring
  rw [hr,hr',hρ]
  constructor <;> nlinarith [sq_nonneg q]

/-- The concrete nested cutoff used by the iteration. -/
def dgSmIterationCutoff {n : ℕ} (j : ℕ) : Point n → ℝ :=
  dgSmCutoff (dgSmSupportRadius j) (dgSmRadius (j+1))
    (-((dgSmRadius j)^2)) (-((dgSmRadius (j+1))^2))

theorem dgSmIterationCutoff_admissible {n : ℕ} (j : ℕ) :
    DGSpatialCutoff (Metric.ball (0 : Space n) (dgSmRadius j))
      (-((dgSmRadius j)^2)) 0 (dgSmIterationCutoff j) := by
  obtain ⟨hα,hαρ,hρr⟩ := dgSmSupportRadius_bounds j
  exact dgSmCutoff_admissible hα.le hαρ hρr

theorem dgSmIterationCutoff_one {n : ℕ} (j : ℕ) {z : Point n}
    (hz : z ∈ dgSmCylinder (dgSmRadius (j+1))) : dgSmIterationCutoff j z = 1 := by
  obtain ⟨hα,hαρ,_hρr⟩ := dgSmSupportRadius_bounds j
  have hd := dgSmRadius_decreasing j
  have hab : -((dgSmRadius j)^2) < -((dgSmRadius (j+1))^2) := by nlinarith
  exact dgSmCutoff_one hα.le hαρ hab (by have hh : ‖z.1‖ < dgSmRadius (j+1) := by simpa only [Metric.mem_ball,dist_zero_right] using hz.1
                                         exact hh.le) hz.2.1.le

theorem dgSmIterationCutoff_derivative_bound {n : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hθ : ∀ q, |deriv Real.smoothTransition q| ≤ M) (j : ℕ) {z : Point n}
    (hz : z ∈ dgSmCylinderOpen (dgSmRadius j)) :
    |deriv (fun t => dgSmIterationCutoff j (z.1,t)) z.2|+
      dgGradientSq (dgGradient (dgSmIterationCutoff j) z)+(dgSmIterationCutoff j z)^2 ≤
      (8*M+1024*M^2+1)*(4:ℝ)^j := by
  obtain ⟨hα,hαρ,hρr⟩ := dgSmSupportRadius_bounds j
  have hdr := dgSmRadius_decreasing j
  have hr := dgSmRadius_bounds j
  have hx : ‖z.1‖ ≤ 1 := by
    have hh : ‖z.1‖ < dgSmRadius j := by simpa only [Metric.mem_ball,dist_zero_right] using hz.1
    linarith
  have hab : -((dgSmRadius j)^2) < -((dgSmRadius (j+1))^2) := by nlinarith
  have hδ : 0 < (dgSmSupportRadius j)^2-(dgSmRadius (j+1))^2 := by nlinarith
  have hΔ : 0 < (dgSmRadius j)^2-(dgSmRadius (j+1))^2 := by nlinarith
  have hcancel : (1/2 : ℝ)^j*(2:ℝ)^j = 1 := by rw [← mul_pow]; norm_num
  have hgaps := dgSmRadius_gap_bounds j
  have hinv1 : 1/((dgSmSupportRadius j)^2-(dgSmRadius (j+1))^2) ≤ 16*(2:ℝ)^j := by
    apply (div_le_iff₀ hδ).mpr
    have hh := mul_le_mul_of_nonneg_right hgaps.1 (show 0 ≤ 16*(2:ℝ)^j by positivity)
    nlinarith
  have hinv2 : 1/((dgSmRadius j)^2-(dgSmRadius (j+1))^2) ≤ 8*(2:ℝ)^j := by
    apply (div_le_iff₀ hΔ).mpr
    have hh := mul_le_mul_of_nonneg_right hgaps.2 (show 0 ≤ 8*(2:ℝ)^j by positivity)
    nlinarith
  have htime := dgSmCutoff_time_bound (n := n) (ρ := dgSmSupportRadius j) (α := dgSmRadius (j+1)) hM hθ hab z
  have hgrad := dgSmCutoff_gradient_bound (a := -((dgSmRadius j)^2)) (b := -((dgSmRadius (j+1))^2)) hM hθ hα.le hαρ z hx
  have htime' : |deriv (fun t => dgSmIterationCutoff j (z.1,t)) z.2| ≤ 8*M*(2:ℝ)^j := by
    apply htime.trans
    have hh := mul_le_mul_of_nonneg_left hinv2 hM
    convert hh using 1 <;> ring
  have hgrad' : dgGradientSq (dgGradient (dgSmIterationCutoff j) z) ≤ (32*M*(2:ℝ)^j)^2 := by
    apply hgrad.trans
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hinv1 (show 0 ≤ 2*M by positivity)
    convert hh using 1 <;> ring
  have hsquare : ((2:ℝ)^j)^2 = (4:ℝ)^j := by
    rw [← pow_mul,Nat.mul_comm j 2,pow_mul]
    norm_num
  have hp24 : (2:ℝ)^j ≤ (4:ℝ)^j := by gcongr <;> norm_num
  have hp4 : (1:ℝ) ≤ (4:ℝ)^j := one_le_pow₀ (by norm_num)
  have hζ := dgSmCutoff_range (n := n) (dgSmSupportRadius j) (dgSmRadius (j+1))
    (-((dgSmRadius j)^2)) (-((dgSmRadius (j+1))^2)) z
  have hζ2 : (dgSmIterationCutoff j z)^2 ≤ 1 := by
    dsimp only [dgSmIterationCutoff]
    nlinarith
  have htfinal := htime'.trans (mul_le_mul_of_nonneg_left hp24 (show 0 ≤ 8*M by positivity))
  rw [mul_pow,mul_pow,hsquare] at hgrad'
  nlinarith

theorem dgSmClassicalFields_mono {n : ℕ} {U V : Set (Point n)}
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hf : DGClassicalFields U A c f u) (hVU : V ⊆ U) : DGClassicalFields V A c f u :=
  ⟨fun i j => (hf.1 i j).mono hVU,fun i => (hf.2.1 i).mono hVU,
    hf.2.2.1.mono hVU,hf.2.2.2.mono hVU⟩

theorem dgSmUniformBounds_mono {n : ℕ} {U V : Set (Point n)}
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f : Point n → ℝ}
    {ν L D F : ℝ} (hb : DGUniformBounds U A c f ν L D F) (hVU : V ⊆ U) :
    DGUniformBounds V A c f ν L D F :=
  ⟨⟨hb.1.1,hb.1.2.1,fun z hz => hb.1.2.2 z (hVU hz)⟩,
    fun z hz => hb.2.1 z (hVU hz),fun z hz => hb.2.2 z (hVU hz)⟩

theorem dgSmCylinderOpen_isOpen {n : ℕ} (R : ℝ) : IsOpen (dgSmCylinderOpen (n := n) R) :=
  Metric.isOpen_ball.prod isOpen_Ioo

theorem dgSmCylinderOpen_subset {n : ℕ} {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) :
    dgSmCylinderOpen (n := n) R ⊆ dgSmCylinderOpen S := by
  intro z hz
  refine ⟨Metric.ball_subset_ball hRS hz.1,?_,hz.2.2⟩
  nlinarith [hz.2.1]

theorem dgSmCylinder_subset {n : ℕ} {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) :
    dgSmCylinder (n := n) R ⊆ dgSmCylinder S := by
  intro z hz
  refine ⟨Metric.ball_subset_ball hRS hz.1,?_,hz.2.2⟩
  nlinarith [hz.2.1]

theorem dgSmCylinder_measure_finite {n : ℕ} (R : ℝ) :
    productVolume (Metric.ball (0 : Space n) R) (Ioo (-(R^2)) 0) univ < ⊤ :=
  dg_cylinder_measure_lt_top 0 R (-(R^2)) 0

/-- Exact card-5 target, with the smallness constant before every field and u.
No lower bound for u is assumed; the terminal face is included. -/
def DGSmallMeasureGap : Prop :=
  ∀ n : ℕ, 0 < n → ∀ ν L : ℝ, 0 < ν → ν ≤ L →
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
  ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ),
    DGClassicalFields (dgSmCylinderOpen 1) A c f u →
    ClassicalDivEq (dgSmCylinderOpen 1) A c f u →
    DGUniformBounds (dgSmCylinderOpen 1) A c f ν L 1 1 →
    ContinuousOn u (dgSmCylinder 1) →
    (∀ z ∈ dgSmCylinder 1, u z ≤ 1) →
    dgSmSuperlevelMeasure 1 0 u ≤ δ*
      (productVolume (Metric.ball (0 : Space n) 1) (Ioo (-1) 0) univ).toReal →
    ∀ z ∈ dgSmCylinder (1/2), u z ≤ 1/2

/-- Finite-measure indicator normalization uses the actual superlevel measure. -/
theorem dgSm_superlevel_indicator {n : ℕ} {R k : ℝ} {u : Point n → ℝ}
    (hu : ContinuousOn u (dgSmCylinderOpen R)) :
    let μ := productVolume (Metric.ball (0 : Space n) R) (Ioo (-(R^2)) 0)
    let S := dgSmCylinderOpen R ∩ {z | k < u z}
    MeasurableSet S ∧ Integrable (S.indicator (fun _ => (1:ℝ))) μ ∧
      (∫ z, S.indicator (fun _ => (1:ℝ)) z ∂μ) = dgSmSuperlevelMeasure R k u := by
  let μ := productVolume (Metric.ball (0 : Space n) R) (Ioo (-(R^2)) 0)
  let S := dgSmCylinderOpen R ∩ {z | k < u z}
  have hS : MeasurableSet S := (hu.isOpen_inter_preimage (dgSmCylinderOpen_isOpen R) isOpen_Ioi).measurableSet
  haveI dgSmIndicatorFinite : IsFiniteMeasure μ := ⟨dgSmCylinder_measure_finite R⟩
  have hmem : ∀ᵐ z ∂μ, z ∈ dgSmCylinderOpen R := by
    rw [show μ = volume.restrict (dgSmCylinderOpen R) from dg_productVolume_eq_restrict _ _]
    exact ae_restrict_mem (dgSmCylinderOpen_isOpen R).measurableSet
  have hμS : μ S = μ {z | k < u z} := by
    apply measure_congr
    filter_upwards [hmem] with z hz
    simp only [S,mem_inter_iff,mem_setOf_eq,hz,true_and]
  refine ⟨hS,(integrable_const (1:ℝ)).indicator hS,?_⟩
  rw [integral_indicator_const (1:ℝ) hS]
  simp only [measureReal_def,hμS,smul_eq_mul,mul_one,dgSmSuperlevelMeasure,μ]

/-- The forcing term is controlled by the same active-set measure as the
cutoff error. This produces no additive cylinder-volume error. -/
theorem dgSm_iteration_energy {n : ℕ} (hn : 0 < n) {ν L : ℝ} (hν : 0 < ν) (hνL : ν ≤ L) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ),
      DGClassicalFields (dgSmCylinderOpen 1) A c f u →
      ClassicalDivEq (dgSmCylinderOpen 1) A c f u →
      DGUniformBounds (dgSmCylinderOpen 1) A c f ν L 1 1 →
      ContinuousOn u (dgSmCylinder 1) → (∀ z ∈ dgSmCylinder 1, u z ≤ 1) → ∀ j : ℕ,
      let R := dgSmRadius j
      let k := dgSmLevel j
      let ζ := dgSmIterationCutoff (n := n) j
      let μ := productVolume (Metric.ball (0 : Space n) R) (Ioo (-(R^2)) 0)
      let B := K*(4:ℝ)^j*dgSmSuperlevelMeasure R k u
      Integrable (fun z => dgGradientSq (dgTruncationCutoffGradient 1 k u ζ z)) μ ∧
      (∀ t ∈ Ioo (-(R^2)) 0, dgSliceEnergy (Metric.ball 0 R) (dgTruncation 1 k u) ζ t ≤ B) ∧
      ν*dgCylinderIntegral (Metric.ball 0 R) (-(R^2)) 0
        (fun z => dgGradientSq (dgTruncationCutoffGradient 1 k u ζ z)) ≤ B := by
  obtain ⟨C,hC,hCacc⟩ := dgTruncation_caccioppoli n hn ν L 1 hν hνL (by norm_num)
  obtain ⟨M,hM,hθ⟩ := dgSmStep_derivative_bound
  let T := 8*M+1024*M^2+1
  refine ⟨C*(T+1),mul_pos hC (by dsimp only [T]; positivity),?_⟩
  intro A c f u hf hpde hb hu hupper j
  let R := dgSmRadius j
  let k := dgSmLevel j
  let ζ := dgSmIterationCutoff (n := n) j
  let O : Set (Space n) := Metric.ball 0 R
  let U : Set (Point n) := O ×ˢ Ioo (-1:ℝ) 0
  let μ := productVolume O (Ioo (-(R^2)) 0)
  let S := dgSmCylinderOpen R ∩ {z | k < u z}
  let Y := dgSmSuperlevelMeasure R k u
  have hR : 0 < R := by have hh := (dgSmRadius_bounds j).1; dsimp only [R]; linarith
  have hR1 : R < 1 := by have hh := (dgSmRadius_bounds j).2; dsimp only [R]; linarith
  have ha : -1 < -(R^2) := by have hh := (dgSmRadius_bounds j).2; dsimp only [R]; nlinarith
  have hab : -(R^2) < 0 := by nlinarith
  have hU : U ⊆ dgSmCylinderOpen 1 := by
    intro z hz
    exact ⟨Metric.ball_subset_ball hR1.le hz.1,by simpa using hz.2⟩
  have hclosed : O ×ˢ Icc (-(R^2)) 0 ⊆ dgSmCylinder 1 := by
    intro z hz
    exact ⟨Metric.ball_subset_ball hR1.le hz.1,by norm_num; linarith [hz.2.1],hz.2.2⟩
  have hCyl : dgSmCylinderOpen (n := n) R ⊆ dgSmCylinderOpen 1 := dgSmCylinderOpen_subset hR.le hR1.le
  obtain ⟨hS,hSI,hSInt⟩ := dgSm_superlevel_indicator ((hf.2.2.2.continuousOn).mono hCyl) (k := k)
  obtain ⟨hH,hErr,hFor,hSlice,hComp,hCompB⟩ := hCacc 1 (by norm_num) 0 R (-1) 0 (-(R^2)) 0
    hR ha hab le_rfl A c f u ζ (dgSmClassicalFields_mono hf hU)
    (fun z hz => hpde z (hU hz)) (dgSmUniformBounds_mono hb hU) (hu.mono hclosed)
    (dgSmIterationCutoff_admissible j) 1 k (Or.inl rfl)
  have hv0 (z : Point n) : 0 ≤ dgTruncation 1 k u z := le_max_left _ _
  have hv1 (z : Point n) (hz : z ∈ dgSmCylinderOpen R) : dgTruncation 1 k u z ≤ 1 := by
    have hh := hupper z ⟨(hCyl hz).1,(hCyl hz).2.1,(hCyl hz).2.2.le⟩
    have hk := (dgSmLevel_bounds j).1
    change max 0 (1*u z-k) ≤ 1
    apply max_le (by norm_num)
    dsimp only [k]
    linarith
  have hvzero (z : Point n) (hz : ¬k < u z) : dgTruncation 1 k u z = 0 := by
    change max 0 (1*u z-k) = 0
    rw [max_eq_left (by linarith)]
  have hmem : ∀ᵐ z ∂μ, z ∈ dgSmCylinderOpen R := by
    rw [show μ = volume.restrict (dgSmCylinderOpen R) from dg_productVolume_eq_restrict O _]
    exact ae_restrict_mem (dgSmCylinderOpen_isOpen R).measurableSet
  have hErrBound : ∀ᵐ z ∂μ, dgTruncationCutoffError 1 k u ζ z ≤
      T*(4:ℝ)^j*S.indicator (fun _ => (1:ℝ)) z := by
    filter_upwards [hmem] with z hz
    have hd := dgSmIterationCutoff_derivative_bound hM.le hθ j hz
    by_cases ha : k < u z
    · rw [indicator_of_mem (show z ∈ S from ⟨hz,ha⟩)]
      have hv := hv1 z hz
      have hv' := hv0 z
      have hv2 : (dgTruncation 1 k u z)^2 ≤ 1 := by nlinarith
      have hb0 : 0 ≤ |deriv (fun t => ζ (z.1,t)) z.2|+dgGradientSq (dgGradient ζ z)+(ζ z)^2 :=
        add_nonneg (add_nonneg (abs_nonneg _) (dgGradientSq_nonneg _)) (sq_nonneg _)
      exact (mul_le_mul_of_nonneg_right hv2 hb0).trans (by simpa only [one_mul,mul_one,T,ζ] using hd)
    · rw [indicator_of_notMem (show z ∉ S from fun hh => ha hh.2)]
      simp only [dgTruncationCutoffError,hvzero z ha,zero_pow (by decide : 2 ≠ 0),zero_mul,mul_zero,le_refl]
  have hForBound : ∀ᵐ z ∂μ, dgTruncationForcingDensity 1 k u ζ z ≤ S.indicator (fun _ => (1:ℝ)) z := by
    filter_upwards [hmem] with z hz
    by_cases ha : k < u z
    · rw [indicator_of_mem (show z ∈ S from ⟨hz,ha⟩)]
      have hv := hv1 z hz
      have hζ := dgSmCutoff_range (n := n) (dgSmSupportRadius j) (dgSmRadius (j+1))
        (-((dgSmRadius j)^2)) (-((dgSmRadius (j+1))^2)) z
      have hζ2 : (ζ z)^2 ≤ 1 := by dsimp only [ζ,dgSmIterationCutoff]; nlinarith
      exact (mul_le_mul hv hζ2 (sq_nonneg _) zero_le_one).trans_eq (one_mul 1)
    · rw [indicator_of_notMem (show z ∉ S from fun hh => ha hh.2)]
      simp only [dgTruncationForcingDensity,hvzero z ha,zero_mul,le_refl]
  have hE : dgCylinderIntegral O (-(R^2)) 0 (dgTruncationCutoffError 1 k u ζ) ≤ T*(4:ℝ)^j*Y := by
    have hh := integral_mono_ae hErr (hSI.const_mul (T*(4:ℝ)^j)) hErrBound
    rw [integral_const_mul,hSInt] at hh
    exact hh
  have hF : dgCylinderIntegral O (-(R^2)) 0 (dgTruncationForcingDensity 1 k u ζ) ≤ Y := by
    have hh := integral_mono_ae hFor hSI hForBound
    rwa [hSInt] at hh
  have hInitial : dgSliceEnergy O (dgTruncation 1 k u) ζ (-(R^2)) = 0 := by
    apply dgSliceEnergy_eq_zero_of_cutoff_zero
    intro x _
    exact dgSmCutoff_bottom _ _ _ _ x
  have hY : 0 ≤ Y := ENNReal.toReal_nonneg
  have hpower : 1 ≤ (4:ℝ)^j := one_le_pow₀ (by norm_num)
  have hB : C*dgCylinderIntegral O (-(R^2)) 0 (dgTruncationCutoffError 1 k u ζ)+
      C*1*dgCylinderIntegral O (-(R^2)) 0 (dgTruncationForcingDensity 1 k u ζ)+
      C*dgSliceEnergy O (dgTruncation 1 k u) ζ (-(R^2)) ≤ C*(T+1)*(4:ℝ)^j*Y := by
    rw [hInitial,mul_zero,add_zero,mul_one]
    have hCE := mul_le_mul_of_nonneg_left hE hC.le
    have hCF := mul_le_mul_of_nonneg_left hF hC.le
    have hp := mul_le_mul_of_nonneg_right hpower hY
    nlinarith
  refine ⟨hComp,?_,hCompB.trans hB⟩
  intro τ hτ
  have hh := (hSlice τ (Ioo_subset_Icc_self hτ)).2
  have hH0 : 0 ≤ ν*dgCylinderIntegral O (-(R^2)) 0 (dgTruncationEnergyDensity 1 k u ζ) :=
    mul_nonneg hν.le (integral_nonneg fun z => mul_nonneg (dgGradientSq_nonneg _) (sq_nonneg _))
  exact (le_add_of_nonneg_right hH0).trans (hh.trans hB)

/-- Product-cylinder superlevel measures equal the corresponding ambient
Lebesgue measures, with finite measures justified separately. -/
theorem dgSmSuperlevelMeasure_eq_volume {n : ℕ} (R k : ℝ) (u : Point n → ℝ) :
    dgSmSuperlevelMeasure R k u = (volume (dgSmCylinderOpen R ∩ {z | k < u z})).toReal := by
  unfold dgSmSuperlevelMeasure
  rw [dg_productVolume_eq_restrict]
  change ((volume.restrict (dgSmCylinderOpen R)) {z | k < u z}).toReal = _
  rw [Measure.restrict_apply' (dgSmCylinderOpen_isOpen R).measurableSet]
  rw [inter_comm]

theorem dgSmSuperlevel_volume_finite {n : ℕ} (R k : ℝ) (u : Point n → ℝ) :
    volume (dgSmCylinderOpen R ∩ {z | k < u z}) < ⊤ := by
  have hh := dgSmCylinder_measure_finite (n := n) R
  rw [dg_productVolume_eq_restrict,Measure.restrict_apply_univ] at hh
  exact (measure_mono inter_subset_left).trans_lt hh

theorem dgSmSuperlevelMeasure_mono {n : ℕ} {R S a b : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S)
    (hab : a ≤ b) (u : Point n → ℝ) : dgSmSuperlevelMeasure R b u ≤ dgSmSuperlevelMeasure S a u := by
  rw [dgSmSuperlevelMeasure_eq_volume,dgSmSuperlevelMeasure_eq_volume]
  apply ENNReal.toReal_mono (dgSmSuperlevel_volume_finite S a u).ne
  apply measure_mono
  intro z hz
  exact ⟨dgSmCylinderOpen_subset hR hRS hz.1,hab.trans_lt hz.2⟩

/-- Chebyshev on the next genuine superlevel set, using the actual cutoff
which equals one there. Both integrals are integrable before comparison. -/
theorem dgSm_next_measure_bound {n : ℕ} {u : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (dgSmCylinderOpen 1)) (j : ℕ) {p : ℝ} (hp : 0 < p)
    (hI : Integrable (fun z => |dgTruncation 1 (dgSmLevel j) u z*dgSmIterationCutoff j z|^p)
      (productVolume (Metric.ball 0 (dgSmRadius j)) (Ioo (-((dgSmRadius j)^2)) 0))) :
    ((1/2:ℝ)^(j+2))^p*dgSmSuperlevelMeasure (dgSmRadius (j+1)) (dgSmLevel (j+1)) u ≤
      dgCylinderIntegral (Metric.ball 0 (dgSmRadius j)) (-((dgSmRadius j)^2)) 0
        (fun z => |dgTruncation 1 (dgSmLevel j) u z*dgSmIterationCutoff j z|^p) := by
  let R := dgSmRadius j
  let R' := dgSmRadius (j+1)
  let k := dgSmLevel j
  let k' := dgSmLevel (j+1)
  let g : ℝ := (1/2)^(j+2)
  let μ := productVolume (Metric.ball (0 : Space n) R) (Ioo (-(R^2)) 0)
  let μ' := productVolume (Metric.ball (0 : Space n) R') (Ioo (-(R'^2)) 0)
  let S' := dgSmCylinderOpen R' ∩ {z | k' < u z}
  have hR' : 0 < R' := by have hh := (dgSmRadius_bounds (j+1)).1; dsimp only [R']; linarith
  have hR1 : R' ≤ 1 := by have hh := (dgSmRadius_bounds (j+1)).2; dsimp only [R']; linarith
  have hsub : dgSmCylinderOpen (n := n) R' ⊆ dgSmCylinderOpen R :=
    dgSmCylinderOpen_subset hR'.le (dgSmRadius_decreasing j).le
  have hS' : MeasurableSet S' :=
    ((hu.continuousOn.mono (dgSmCylinderOpen_subset hR'.le hR1)).isOpen_inter_preimage
      (dgSmCylinderOpen_isOpen R') isOpen_Ioi).measurableSet
  haveI dgSmNextCylinderFinite : IsFiniteMeasure μ := ⟨dgSmCylinder_measure_finite R⟩
  have hSI : Integrable (S'.indicator (fun _ => (1:ℝ))) μ := (integrable_const (1:ℝ)).indicator hS'
  have hμeq : μ S' = μ' {z | k' < u z} := by
    rw [show μ = volume.restrict (dgSmCylinderOpen R) from dg_productVolume_eq_restrict _ _,
      show μ' = volume.restrict (dgSmCylinderOpen R') from dg_productVolume_eq_restrict _ _,
      Measure.restrict_apply' (dgSmCylinderOpen_isOpen R).measurableSet,
      Measure.restrict_apply' (dgSmCylinderOpen_isOpen R').measurableSet]
    rw [inter_eq_self_of_subset_left (show S' ⊆ dgSmCylinderOpen R from fun z hz => hsub hz.1)]
    congr 1
    exact inter_comm _ _
  have hInd : (∫ z, S'.indicator (fun _ => (1:ℝ)) z ∂μ) = dgSmSuperlevelMeasure R' k' u := by
    rw [integral_indicator_const (1:ℝ) hS']
    simp only [measureReal_def,hμeq,smul_eq_mul,mul_one,dgSmSuperlevelMeasure,μ']
  have hg : 0 < g := pow_pos (by norm_num) _
  have hpoint (z : Point n) : g^p*S'.indicator (fun _ => (1:ℝ)) z ≤
      |dgTruncation 1 k u z*dgSmIterationCutoff j z|^p := by
    by_cases hz : z ∈ S'
    · rw [indicator_of_mem hz,mul_one,dgSmIterationCutoff_one j
        (show z ∈ dgSmCylinder R' from ⟨hz.1.1,hz.1.2.1,hz.1.2.2.le⟩),mul_one]
      have hv0 : 0 ≤ dgTruncation 1 k u z := le_max_left _ _
      rw [abs_of_nonneg hv0]
      have hgap := dgSmLevel_gap j
      have hv : g ≤ dgTruncation 1 k u z := by
        have hh : u z-k ≤ dgTruncation 1 k u z := by
          simpa only [dgTruncation,one_mul,dgPositivePart] using (le_max_right (0:ℝ) (u z-k))
        have hk : k' < u z := hz.2
        dsimp only [k,k',g] at *
        linarith
      exact Real.rpow_le_rpow hg.le hv hp.le
    · rw [indicator_of_notMem hz,mul_zero]
      exact Real.rpow_nonneg (abs_nonneg _) _
  have hh := integral_mono (hSI.const_mul (g^p)) hI hpoint
  rw [integral_const_mul,hInd] at hh
  exact hh

/-- Caccioppoli and first-gradient parabolic Sobolev give the actual measure
recurrence before its purely scalar power normalization. -/
theorem dgSm_raw_measure_recurrence {n : ℕ} (hn : 0 < n) {ν L : ℝ} (hν : 0 < ν) (hνL : ν ≤ L) :
    ∃ K S : ℝ, 0 < K ∧ 0 < S ∧
    ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ),
      DGClassicalFields (dgSmCylinderOpen 1) A c f u →
      ClassicalDivEq (dgSmCylinderOpen 1) A c f u →
      DGUniformBounds (dgSmCylinderOpen 1) A c f ν L 1 1 →
      ContinuousOn u (dgSmCylinder 1) → (∀ z ∈ dgSmCylinder 1, u z ≤ 1) → ∀ j : ℕ,
      let Y := dgSmSuperlevelMeasure (dgSmRadius j) (dgSmLevel j) u
      let Y' := dgSmSuperlevelMeasure (dgSmRadius (j+1)) (dgSmLevel (j+1)) u
      let B := K*(4:ℝ)^j*Y
      ((1/2:ℝ)^(j+2))^((2:ℝ)+2/n)*Y' ≤ S*B^((n:ℝ)⁻¹)*(B/ν) := by
  obtain ⟨K,hK,hEnergy⟩ := dgSm_iteration_energy hn hν hνL
  obtain ⟨S,hS,hPS⟩ := dg_parabolic_sobolev hn
  refine ⟨K,S,hK,hS,?_⟩
  intro A c f u hf hpde hb hu hupper j
  let R := dgSmRadius j
  let k := dgSmLevel j
  let ζ := dgSmIterationCutoff (n := n) j
  let B := K*(4:ℝ)^j*dgSmSuperlevelMeasure R k u
  have hR : 0 < R := by have hh := (dgSmRadius_bounds j).1; dsimp only [R]; linarith
  have hR1 : R ≤ 1 := by have hh := (dgSmRadius_bounds j).2; dsimp only [R]; linarith
  have hB : 0 ≤ B := by dsimp only [B,dgSmSuperlevelMeasure]; positivity
  obtain ⟨hEI,hSlice,hEB⟩ := hEnergy A c f u hf hpde hb hu hupper j
  obtain ⟨hZI,hZB⟩ := hPS (Metric.ball 0 R) Metric.isOpen_ball (-(R^2)) 0 (by nlinarith)
    u ζ (hf.2.2.2.mono (dgSmCylinderOpen_subset hR.le hR1))
    (dgSmIterationCutoff_admissible j) 1 k B hB hEI hSlice
  have hCheb := dgSm_next_measure_bound hf.2.2.2 j (by positivity : 0 < (2:ℝ)+2/n) hZI
  have hEB' : dgCylinderIntegral (Metric.ball 0 R) (-(R^2)) 0
      (fun z => dgGradientSq (dgTruncationCutoffGradient 1 k u ζ z)) ≤ B/ν := by
    apply (le_div_iff₀ hν).mpr
    nlinarith [hEB]
  exact hCheb.trans (hZB.trans (mul_le_mul_of_nonneg_left hEB'
    (mul_nonneg hS.le (Real.rpow_nonneg hB _))))

/-- Only scalar power algebra is used to normalize the PDE-derived recurrence.
The nonlinear sequence induction itself is imported from the fixed iteration card. -/
theorem dgSm_normalize_recurrence {K S ν ε p Y Y' : ℝ}
    (hK : 0 < K) (hS : 0 < S) (hν : 0 < ν) (hε : 0 ≤ ε) (hY : 0 ≤ Y) (j : ℕ)
    (hraw : ((1/2:ℝ)^(j+2))^p*Y' ≤ S*(K*(4:ℝ)^j*Y)^ε*((K*(4:ℝ)^j*Y)/ν)) :
    Y' ≤ ((4:ℝ)^p*S*K^ε*K/ν)*((4:ℝ)^ε*4*(2:ℝ)^p)^j*Y^(1+ε) := by
  let g : ℝ := (1/2)^(j+2)
  let H : ℝ := 4*(2:ℝ)^j
  have hg : 0 < g := pow_pos (by norm_num) _
  have hH : 0 < H := by dsimp only [H]; positivity
  have hcancel : H*g = 1 := by
    dsimp only [H,g]
    rw [pow_add]
    have hh : (2:ℝ)^j*(1/2:ℝ)^j = 1 := by rw [← mul_pow]; norm_num
    nlinarith
  have hpowcancel : H^p*g^p = 1 := by
    rw [← Real.mul_rpow hH.le hg.le,hcancel,Real.one_rpow]
  have h4 : ((4:ℝ)^j)^ε = ((4:ℝ)^ε)^j := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm (j:ℝ) ε,Real.rpow_mul_natCast (by norm_num)]
  have h2 : ((2:ℝ)^j)^p = ((2:ℝ)^p)^j := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm (j:ℝ) p,Real.rpow_mul_natCast (by norm_num)]
  have hBpow : (K*(4:ℝ)^j*Y)^ε = K^ε*((4:ℝ)^ε)^j*Y^ε := by
    rw [Real.mul_rpow (mul_nonneg hK.le (by positivity)) hY,Real.mul_rpow hK.le (by positivity),h4]
  have hHpow : H^p = (4:ℝ)^p*((2:ℝ)^p)^j := by
    dsimp only [H]
    rw [Real.mul_rpow (by norm_num) (by positivity),h2]
  have hYpow : Y^(1+ε) = Y*Y^ε := by
    rw [Real.rpow_add_of_nonneg hY zero_le_one hε,Real.rpow_one]
  have hh := mul_le_mul_of_nonneg_left hraw (Real.rpow_nonneg hH.le p)
  have hl : H^p*(g^p*Y') = Y' := by rw [← mul_assoc,hpowcancel,one_mul]
  change H^p*(g^p*Y') ≤ _ at hh
  rw [hl] at hh
  apply hh.trans_eq
  rw [hBpow,hHpow,hYpow]
  simp only [mul_pow]
  ring

/-- The genuine superlevel measures satisfy a universal nonlinear recurrence. -/
theorem dgSm_measure_recurrence {n : ℕ} (hn : 0 < n) {ν L : ℝ} (hν : 0 < ν) (hνL : ν ≤ L) :
    ∃ C b : ℝ, 0 < C ∧ 1 < b ∧
    ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ),
      DGClassicalFields (dgSmCylinderOpen 1) A c f u →
      ClassicalDivEq (dgSmCylinderOpen 1) A c f u →
      DGUniformBounds (dgSmCylinderOpen 1) A c f ν L 1 1 →
      ContinuousOn u (dgSmCylinder 1) → (∀ z ∈ dgSmCylinder 1, u z ≤ 1) → ∀ j : ℕ,
      dgSmSuperlevelMeasure (dgSmRadius (j+1)) (dgSmLevel (j+1)) u ≤
        C*b^j*(dgSmSuperlevelMeasure (dgSmRadius j) (dgSmLevel j) u)^(1+(n:ℝ)⁻¹) := by
  obtain ⟨K,S,hK,hS,hRaw⟩ := dgSm_raw_measure_recurrence hn hν hνL
  let ε : ℝ := (n:ℝ)⁻¹
  let p : ℝ := 2+2/(n:ℝ)
  let C : ℝ := (4:ℝ)^p*S*K^ε*K/ν
  let b₀ : ℝ := (4:ℝ)^ε*4*(2:ℝ)^p
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hb₀ : 0 < b₀ := by dsimp only [b₀]; positivity
  refine ⟨C,b₀+1,hC,by linarith,?_⟩
  intro A c f u hf hpde hb hu hupper j
  have hh := dgSm_normalize_recurrence hK hS hν hε.le
    (show 0 ≤ dgSmSuperlevelMeasure (dgSmRadius j) (dgSmLevel j) u from ENNReal.toReal_nonneg) j
    (hRaw A c f u hf hpde hb hu hupper j)
  exact hh.trans (by
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left (by gcongr; linarith : b₀^j ≤ (b₀+1)^j) hC.le
    · exact Real.rpow_nonneg ENNReal.toReal_nonneg _)

/-- Vanishing true superlevel measures imply the pointwise drop, including
the terminal face by continuity from strictly earlier times. -/
theorem dgSm_pointwise_of_measure_tendsto {n : ℕ} {u : Point n → ℝ}
    (hu : ContinuousOn u (dgSmCylinder 1))
    (hlim : Tendsto (fun j => dgSmSuperlevelMeasure (dgSmRadius j) (dgSmLevel j) u)
      atTop (𝓝 0)) : ∀ z ∈ dgSmCylinder (1/2), u z ≤ 1/2 := by
  have hmono (j : ℕ) : dgSmSuperlevelMeasure (1/2) (1/2) u ≤
      dgSmSuperlevelMeasure (dgSmRadius j) (dgSmLevel j) u :=
    dgSmSuperlevelMeasure_mono (by norm_num) (dgSmRadius_bounds j).1.le (dgSmLevel_bounds j).2.le u
  have hle0 : dgSmSuperlevelMeasure (1/2) (1/2) u ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (.of_forall hmono)
  have hreal0 : dgSmSuperlevelMeasure (1/2) (1/2) u = 0 := le_antisymm hle0 ENNReal.toReal_nonneg
  rw [dgSmSuperlevelMeasure_eq_volume] at hreal0
  have hzero : volume (dgSmCylinderOpen (1/2) ∩ {z | (1/2:ℝ) < u z}) = 0 :=
    (measureReal_eq_zero_iff (dgSmSuperlevel_volume_finite (1/2) (1/2) u).ne).mp hreal0
  have hsub : dgSmCylinderOpen (n := n) (1/2) ⊆ dgSmCylinder 1 := by
    intro z hz
    refine ⟨Metric.ball_subset_ball (by norm_num : (1/2:ℝ) ≤ 1) hz.1,?_,hz.2.2.le⟩
    norm_num at *
    linarith [hz.2.1]
  have hSopen : IsOpen (dgSmCylinderOpen (1/2) ∩ {z | (1/2:ℝ) < u z}) :=
    (hu.mono hsub).isOpen_inter_preimage (dgSmCylinderOpen_isOpen _) isOpen_Ioi
  have hinterior : ∀ z ∈ dgSmCylinderOpen (1/2), u z ≤ 1/2 := by
    intro z hz
    by_contra hh
    have hpos := hSopen.measure_pos volume (show (dgSmCylinderOpen (1/2) ∩ {z | (1/2:ℝ) < u z}).Nonempty from
      ⟨z,hz,lt_of_not_ge hh⟩)
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos
  intro z hz
  by_cases ht : z.2 < 0
  · exact hinterior z ⟨hz.1,hz.2.1,ht⟩
  · have hz0 : z.2 = 0 := le_antisymm hz.2.2 (le_of_not_gt ht)
    let τ : ℕ → ℝ := fun j => -(1/8:ℝ)*(1/2:ℝ)^j
    have hτ (j : ℕ) : (z.1,τ j) ∈ dgSmCylinderOpen (1/2) := by
      have hp := pow_pos (by norm_num : (0:ℝ) < 1/2) j
      have hple := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) (n := j)
      refine ⟨hz.1,?_,?_⟩ <;> dsimp only [τ] <;> norm_num <;> nlinarith
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)
    have hτlim : Tendsto τ atTop (𝓝 0) := by
      simpa only [τ,mul_zero] using hpow.const_mul (-(1/8:ℝ))
    have hpoint : Tendsto (fun j => (z.1,τ j)) atTop (𝓝 z) := by
      have hh : Tendsto (fun j => (z.1,τ j)) atTop (𝓝 (z.1,0)) := tendsto_const_nhds.prodMk_nhds hτlim
      have he : (z.1,0) = z := Prod.ext rfl hz0.symm
      rwa [he] at hh
    have hwithin : Tendsto (fun j => (z.1,τ j)) atTop (𝓝[dgSmCylinder 1] z) :=
      tendsto_nhdsWithin_iff.mpr ⟨hpoint,.of_forall fun j => hsub (hτ j)⟩
    have hz1 : z ∈ dgSmCylinder 1 := dgSmCylinder_subset (by norm_num) (by norm_num) hz
    have hvalue := (hu z hz1).tendsto.comp hwithin
    exact le_of_tendsto_of_tendsto hvalue tendsto_const_nhds (.of_forall fun j => hinterior _ (hτ j))

/-- Small upper-set measure forces a pointwise drop on the full terminal
half-cylinder. The positive threshold is fixed before all coefficient fields
and the solution; no lower bound for the solution is used. -/
theorem dg_small_measure : DGSmallMeasureGap := by
  intro n hn ν L hν hνL
  obtain ⟨C,b,hC,hb,hRec⟩ := dgSm_measure_recurrence hn hν hνL
  have hε : 0 < (n:ℝ)⁻¹ := by positivity
  obtain ⟨δ₀,hδ₀,hIter⟩ := Yau.LeafProofs.L16DG.exists_nonlinear_iteration_threshold C b (n:ℝ)⁻¹ hC hb hε
  let V : ℝ := (productVolume (Metric.ball (0 : Space n) 1) (Ioo (-1) 0) univ).toReal
  let δ : ℝ := min (1/2) (δ₀/(2*(V+1)))
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  refine ⟨δ,hδ,(min_le_left _ _).trans_lt (by norm_num),?_⟩
  intro A c f u hf hpde hbnd hu hupper hsmall
  let Y : ℕ → ℝ := fun j => dgSmSuperlevelMeasure (dgSmRadius j) (dgSmLevel j) u
  have hδbound : δ*V ≤ δ₀ := by
    have hh : δ*(2*(V+1)) ≤ δ₀ := (le_div_iff₀ (by positivity : 0 < 2*(V+1))).mp (min_le_right _ _)
    exact (mul_le_mul_of_nonneg_left (by linarith : V ≤ 2*(V+1)) hδ.le).trans hh
  have hY0 : Y 0 ≤ δ₀ := by
    have hh : Y 0 ≤ dgSmSuperlevelMeasure 1 0 u := by
      simpa only [Y,dgSmRadius_zero,dgSmLevel_zero] using
        dgSmSuperlevelMeasure_mono (by norm_num : (0:ℝ) ≤ 3/4) (by norm_num : (3/4:ℝ) ≤ 1) le_rfl u
    exact hh.trans (hsmall.trans hδbound)
  have hlim : Tendsto Y atTop (𝓝 0) := hIter Y (fun _ => ENNReal.toReal_nonneg) hY0
    (fun j => hRec A c f u hf hpde hbnd hu hupper j)
  exact dgSm_pointwise_of_measure_tendsto hu hlim

end Yau.LeafProofs.L16Aux
