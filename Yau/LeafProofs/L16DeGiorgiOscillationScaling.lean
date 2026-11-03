import Yau.LeafProofs.L16DeGiorgiIntermediateValue
import Yau.LeafProofs.L16DeGiorgiSmallMeasure

open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

local instance dgOscScaling_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance dgOscScaling_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- Affine value normalization preserves the actual smooth field assumptions. -/
theorem dgOsc_affine_fields {n : ℕ} {U : Set (Point n)}
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hf : DGClassicalFields U A c f u) (σ k : ℝ) :
    DGClassicalFields U A c (fun z => σ*f z) (fun z => σ*u z-k) :=
  ⟨hf.1,hf.2.1,contDiffOn_const.mul hf.2.2.1,(contDiffOn_const.mul hf.2.2.2).sub contDiffOn_const⟩

/-- The forcing budget transforms by its actual absolute scalar factor. -/
theorem dgOsc_affine_uniform {n : ℕ} {U : Set (Point n)} {ν L D F σ : ℝ}
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f : Point n → ℝ}
    (hb : DGUniformBounds U A c f ν L D F) :
    DGUniformBounds U A c (fun z => σ*f z) ν L D (|σ| *F) := by
  refine ⟨hb.1,hb.2.1,?_⟩
  intro z hz
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hb.2.2 z hz) (abs_nonneg _)

theorem dgOsc_uniform_mono {n : ℕ} {U : Set (Point n)} {ν L D D' F F' : ℝ}
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f : Point n → ℝ}
    (hb : DGUniformBounds U A c f ν L D F) (hD : 0 ≤ D) (hDD' : D ≤ D') (hFF' : F ≤ F') :
    DGUniformBounds U A c f ν L D' F' :=
  ⟨hb.1,fun z hz => (hb.2.1 z hz).trans (pow_le_pow_left₀ hD hDD' 2),
    fun z hz => (hb.2.2 z hz).trans hFF'⟩

/-- Open-time and terminal-face backward cylinders at an arbitrary actual point. -/
def dgOscCylinderOpen {n : ℕ} (p : Point n) (R : ℝ) : Set (Point n) :=
  Metric.ball p.1 R ×ˢ Ioo (p.2-R^2) p.2

def dgOscCylinder {n : ℕ} (p : Point n) (R : ℝ) : Set (Point n) :=
  Metric.ball p.1 R ×ˢ Ioc (p.2-R^2) p.2

@[simp] theorem dgOscCylinderOpen_zero {n : ℕ} (R : ℝ) :
    dgOscCylinderOpen (0 : Point n) R = dgSmCylinderOpen R := by
  simp only [dgOscCylinderOpen,dgSmCylinderOpen,Prod.fst_zero,Prod.snd_zero,zero_sub]

@[simp] theorem dgOscCylinder_zero {n : ℕ} (R : ℝ) :
    dgOscCylinder (0 : Point n) R = dgSmCylinder R := by
  simp only [dgOscCylinder,dgSmCylinder,Prod.fst_zero,Prod.snd_zero,zero_sub]

/-- Genuine parabolic translation and scaling, before any value normalization. -/
def dgOscMap {n : ℕ} (p₀ : Point n) (ρ : ℝ) (p : Point n) : Point n :=
  (p₀.1+ρ • p.1,p₀.2+ρ^2*p.2)

def dgOscUnmap {n : ℕ} (p₀ : Point n) (ρ : ℝ) (p : Point n) : Point n :=
  (ρ⁻¹ • (p.1-p₀.1),(p.2-p₀.2)/(ρ^2))

theorem dgOscMap_contDiff {n : ℕ} (p₀ : Point n) (ρ : ℝ) : ContDiff ℝ ∞ (dgOscMap p₀ ρ) := by
  unfold dgOscMap
  fun_prop

theorem dgOscMap_unmap {n : ℕ} (p₀ : Point n) {ρ : ℝ} (hρ : ρ ≠ 0) (p : Point n) :
    dgOscMap p₀ ρ (dgOscUnmap p₀ ρ p) = p := by
  apply Prod.ext
  · change p₀.1+ρ • (ρ⁻¹ • (p.1-p₀.1)) = p.1
    rw [smul_smul,mul_inv_cancel₀ hρ,one_smul]
    abel
  · change p₀.2+ρ^2*((p.2-p₀.2)/(ρ^2)) = p.2
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 hρ)]
    ring

theorem dgOscUnmap_map {n : ℕ} (p₀ : Point n) {ρ : ℝ} (hρ : ρ ≠ 0) (p : Point n) :
    dgOscUnmap p₀ ρ (dgOscMap p₀ ρ p) = p := by
  apply Prod.ext
  · change ρ⁻¹ • (p₀.1+ρ • p.1-p₀.1) = p.1
    rw [show p₀.1+ρ • p.1-p₀.1 = ρ • p.1 by abel,smul_smul,inv_mul_cancel₀ hρ,one_smul]
  · change (p₀.2+ρ^2*p.2-p₀.2)/(ρ^2) = p.2
    rw [show p₀.2+ρ^2*p.2-p₀.2 = p.2*ρ^2 by ring,mul_div_cancel_right₀ _ (pow_ne_zero 2 hρ)]

theorem dgOscMap_spatial_mem_iff {n : ℕ} (p₀ : Point n) {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (p : Point n) :
    (dgOscMap p₀ ρ p).1 ∈ Metric.ball p₀.1 (ρ*r) ↔ p.1 ∈ Metric.ball 0 r := by
  simp only [dgOscMap,Metric.mem_ball,dist_eq_norm,sub_zero]
  rw [show p₀.1+ρ • p.1-p₀.1 = ρ • p.1 by abel,norm_smul,Real.norm_of_nonneg hρ.le]
  exact mul_lt_mul_iff_right₀ hρ

theorem dgOscMap_time_lower_iff {n : ℕ} (p₀ : Point n) {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (t : ℝ) :
    p₀.2-(ρ*r)^2 < p₀.2+ρ^2*t ↔ -(r^2) < t := by
  rw [mul_pow]
  constructor
  · intro ht
    apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos hρ)).mp
    nlinarith only [ht]
  · intro ht
    have hh := mul_lt_mul_of_pos_left ht (sq_pos_of_pos hρ)
    nlinarith only [hh]

theorem dgOscMap_time_upper_iff {n : ℕ} (p₀ : Point n) {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    p₀.2+ρ^2*t ≤ p₀.2 ↔ t ≤ 0 := by
  constructor
  · intro ht
    by_contra hn
    have hh := mul_pos (sq_pos_of_pos hρ) (lt_of_not_ge hn)
    linarith only [ht,hh]
  · intro ht
    have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ρ) ht
    linarith only [hh]

theorem dgOscMap_time_upper_strict_iff {n : ℕ} (p₀ : Point n) {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    p₀.2+ρ^2*t < p₀.2 ↔ t < 0 := by
  constructor
  · intro ht
    by_contra hn
    have hh := mul_nonneg (sq_nonneg ρ) (le_of_not_gt hn)
    linarith only [ht,hh]
  · intro ht
    have hh := mul_neg_of_pos_of_neg (sq_pos_of_pos hρ) ht
    linarith only [hh]

theorem dgOscMap_mem_cylinder_iff {n : ℕ} (p₀ : Point n) {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (p : Point n) :
    dgOscMap p₀ ρ p ∈ dgOscCylinder p₀ (ρ*r) ↔ p ∈ dgSmCylinder r := by
  change ((dgOscMap p₀ ρ p).1 ∈ Metric.ball p₀.1 (ρ*r) ∧
    p₀.2-(ρ*r)^2 < p₀.2+ρ^2*p.2 ∧ p₀.2+ρ^2*p.2 ≤ p₀.2) ↔ _
  rw [dgOscMap_spatial_mem_iff p₀ hρ,dgOscMap_time_lower_iff p₀ hρ,dgOscMap_time_upper_iff p₀ hρ]
  rfl

theorem dgOscMap_mem_open_cylinder_iff {n : ℕ} (p₀ : Point n) {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) (p : Point n) :
    dgOscMap p₀ ρ p ∈ dgOscCylinderOpen p₀ (ρ*r) ↔ p ∈ dgSmCylinderOpen r := by
  change ((dgOscMap p₀ ρ p).1 ∈ Metric.ball p₀.1 (ρ*r) ∧
    p₀.2-(ρ*r)^2 < p₀.2+ρ^2*p.2 ∧ p₀.2+ρ^2*p.2 < p₀.2) ↔ _
  rw [dgOscMap_spatial_mem_iff p₀ hρ,dgOscMap_time_lower_iff p₀ hρ,dgOscMap_time_upper_strict_iff p₀ hρ]
  rfl


/-- The actual differential of the parabolic affine map. -/
def dgOscMapLinear {n : ℕ} (ρ : ℝ) : Point n →L[ℝ] Point n :=
  (ρ • ContinuousLinearMap.fst ℝ (Space n) ℝ).prod
    ((ρ^2) • ContinuousLinearMap.snd ℝ (Space n) ℝ)

theorem dgOscMap_hasFDerivAt {n : ℕ} (p₀ : Point n) (ρ : ℝ) (p : Point n) :
    HasFDerivAt (dgOscMap p₀ ρ) (dgOscMapLinear ρ) p := by
  change HasFDerivAt (fun q : Point n => p₀+dgOscMapLinear ρ q) (dgOscMapLinear ρ) p
  exact (dgOscMapLinear ρ).hasFDerivAt.const_add p₀

theorem dgOsc_gradient_comp {n : ℕ} (p₀ : Point n) (ρ : ℝ) {g : Point n → ℝ}
    {p : Point n} (hg : DifferentiableAt ℝ g (dgOscMap p₀ ρ p)) (i : Yau.RIdx n) :
    dgGradient (fun q => g (dgOscMap p₀ ρ q)) p i = ρ*dgGradient g (dgOscMap p₀ ρ p) i := by
  have hc := hg.hasFDerivAt.comp p (dgOscMap_hasFDerivAt p₀ ρ p)
  change dgGradient (g ∘ dgOscMap p₀ ρ) p i = _
  rw [dgGradient_eq_joint_fderiv hc.differentiableAt i,hc.fderiv,dgGradient_eq_joint_fderiv hg i]
  change fderiv ℝ g (dgOscMap p₀ ρ p) (dgOscMapLinear ρ (Yau.realVec i,0)) = _
  have he : dgOscMapLinear ρ (Yau.realVec i,0) = ρ • (Yau.realVec i,0) := by
    ext <;> simp [dgOscMapLinear]
  rw [he,map_smul]
  rfl

theorem dgOsc_time_comp {n : ℕ} (p₀ : Point n) (ρ : ℝ) {g : Point n → ℝ}
    {p : Point n} (hg : DifferentiableAt ℝ g (dgOscMap p₀ ρ p)) :
    deriv (fun t => g (dgOscMap p₀ ρ (p.1,t))) p.2 =
      ρ^2*deriv (fun t => g ((dgOscMap p₀ ρ p).1,t)) (dgOscMap p₀ ρ p).2 := by
  have hc := hg.hasFDerivAt.comp p (dgOscMap_hasFDerivAt p₀ ρ p)
  change deriv (fun t => (g ∘ dgOscMap p₀ ρ) (p.1,t)) p.2 = _
  rw [dgTimeDeriv_eq_joint_fderiv hc.differentiableAt,hc.fderiv,dgTimeDeriv_eq_joint_fderiv hg]
  change fderiv ℝ g (dgOscMap p₀ ρ p) (dgOscMapLinear ρ (0,1)) = _
  have he : dgOscMapLinear ρ ((0,1) : Point n) = (ρ^2) • ((0,1) : Point n) := by
    ext <;> simp [dgOscMapLinear]
  rw [he,map_smul]
  rfl

/-- Smoothness transports through the genuine parabolic affine map. -/
theorem dgOsc_scaled_fields {n : ℕ} {U V : Set (Point n)}
    (p₀ : Point n) (ρ : ℝ) (hMap : MapsTo (dgOscMap p₀ ρ) V U)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hf : DGClassicalFields U A c f u) :
    DGClassicalFields V (fun p => A (dgOscMap p₀ ρ p))
      (fun p i => ρ*c (dgOscMap p₀ ρ p) i) (fun p => ρ^2*f (dgOscMap p₀ ρ p))
      (fun p => u (dgOscMap p₀ ρ p)) :=
  ⟨fun i j => (hf.1 i j).comp (dgOscMap_contDiff p₀ ρ).contDiffOn hMap,
    fun i => contDiffOn_const.mul ((hf.2.1 i).comp (dgOscMap_contDiff p₀ ρ).contDiffOn hMap),
    contDiffOn_const.mul (hf.2.2.1.comp (dgOscMap_contDiff p₀ ρ).contDiffOn hMap),
    hf.2.2.2.comp (dgOscMap_contDiff p₀ ρ).contDiffOn hMap⟩

/-- Ellipticity is unchanged; drift and forcing have their exact parabolic
scaling factors. Coefficient derivative norms never enter these budgets. -/
theorem dgOsc_scaled_uniform {n : ℕ} {U V : Set (Point n)} {ν L D F : ℝ}
    (p₀ : Point n) (ρ : ℝ) (hMap : MapsTo (dgOscMap p₀ ρ) V U)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f : Point n → ℝ}
    (hb : DGUniformBounds U A c f ν L D F) :
    DGUniformBounds V (fun p => A (dgOscMap p₀ ρ p))
      (fun p i => ρ*c (dgOscMap p₀ ρ p) i) (fun p => ρ^2*f (dgOscMap p₀ ρ p))
      ν L (|ρ| *D) (ρ^2*F) := by
  refine ⟨⟨hb.1.1,hb.1.2.1,fun p hp => hb.1.2.2 _ (hMap hp)⟩,?_,?_⟩
  · intro p hp
    have he : dgGradientSq (fun i => ρ*c (dgOscMap p₀ ρ p) i) = ρ^2*dgGradientSq (c (dgOscMap p₀ ρ p)) := by
      simp only [dgGradientSq,mul_pow,Finset.mul_sum]
    rw [he]
    exact (mul_le_mul_of_nonneg_left (hb.2.1 _ (hMap hp)) (sq_nonneg _)).trans_eq (by rw [mul_pow,sq_abs])
  · intro p hp
    rw [abs_mul,abs_sq]
    exact mul_le_mul_of_nonneg_left (hb.2.2 _ (hMap hp)) (sq_nonneg _)

/-- The literal divergence equation transports by actual first and second
coordinate differentiation, with c'=ρc and f'=ρ²f. -/
theorem dgOsc_scaled_equation {n : ℕ} {U V : Set (Point n)} (hU : IsOpen U) (hV : IsOpen V)
    (p₀ : Point n) (ρ : ℝ) (hMap : MapsTo (dgOscMap p₀ ρ) V U)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hf : DGClassicalFields U A c f u) (hpde : ClassicalDivEq U A c f u) :
    ClassicalDivEq V (fun p => A (dgOscMap p₀ ρ p))
      (fun p i => ρ*c (dgOscMap p₀ ρ p) i) (fun p => ρ^2*f (dgOscMap p₀ ρ p))
      (fun p => u (dgOscMap p₀ ρ p)) := by
  let Φ := dgOscMap p₀ ρ
  let A' := fun p => A (Φ p)
  let v := fun p => u (Φ p)
  have hfV := dgOsc_scaled_fields p₀ ρ hMap hf
  have hFu (i : Yau.RIdx n) := dgFlux_contDiffOn hU hf.1 hf.2.2.2 i
  have hFv (i : Yau.RIdx n) := dgFlux_contDiffOn hV hfV.1 hfV.2.2.2 i
  have huDiff (p : Point n) (hp : p ∈ V) : DifferentiableAt ℝ u (Φ p) :=
    (hf.2.2.2.contDiffAt (hU.mem_nhds (hMap hp))).differentiableAt (by simp)
  have hGrad (p : Point n) (hp : p ∈ V) (i : Yau.RIdx n) : dgGradient v p i = ρ*dgGradient u (Φ p) i :=
    dgOsc_gradient_comp p₀ ρ (huDiff p hp) i
  have hFlux (p : Point n) (hp : p ∈ V) (i : Yau.RIdx n) :
      dgFlux A' v p i = ρ*dgFlux A u (Φ p) i := by
    change (∑ j, A (Φ p) i j*dgGradient v p j) = ρ*(∑ j, A (Φ p) i j*dgGradient u (Φ p) j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hGrad p hp j]
    ring
  intro p hp
  have hDiv (i : Yau.RIdx n) : dgGradient (fun q => dgFlux A' v q i) p i =
      ρ^2*dgGradient (fun q => dgFlux A u q i) (Φ p) i := by
    have hgd : DifferentiableAt ℝ (fun q => dgFlux A u q i) (Φ p) :=
      ((hFu i).contDiffAt (hU.mem_nhds (hMap hp))).differentiableAt (by simp)
    have hcomp : DifferentiableAt ℝ (fun q => dgFlux A u (Φ q) i) p :=
      hgd.comp p (dgOscMap_hasFDerivAt p₀ ρ p).differentiableAt
    have he : (fun q => dgFlux A' v q i) =ᶠ[𝓝 p] fun q => ρ*dgFlux A u (Φ q) i := by
      filter_upwards [hV.mem_nhds hp] with q hq
      exact hFlux q hq i
    rw [dgGradient_eq_joint_fderiv ((hFv i).contDiffAt (hV.mem_nhds hp)|>.differentiableAt (by simp)) i,
      he.fderiv_eq,fderiv_const_mul hcomp]
    change ρ*(fderiv ℝ (fun q => dgFlux A u (Φ q) i) p (Yau.realVec i,0)) = _
    rw [←dgGradient_eq_joint_fderiv hcomp i,dgOsc_gradient_comp p₀ ρ hgd i]
    ring
  have hTime := dgOsc_time_comp p₀ ρ (huDiff p hp)
  have hEq := congrArg (fun r : ℝ => ρ^2*r) (hpde (Φ p) (hMap hp))
  change deriv (fun t => u (Φ (p.1,t))) p.2-
      (∑ i, dgGradient (fun q => dgFlux A' v q i) p i) =
      (∑ i, (ρ*c (Φ p) i)*dgGradient v p i)+ρ^2*f (Φ p)
  rw [hTime]
  simp_rw [hDiv,hGrad p hp]
  simp only [mul_sub,mul_add,Finset.mul_sum] at hEq
  have hSum : (∑ i : Yau.RIdx n, (ρ*c (Φ p) i)*(ρ*dgGradient u (Φ p) i)) =
      ∑ i : Yau.RIdx n, ρ^2*(c (Φ p) i*dgGradient u (Φ p) i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hSum]
  exact hEq


theorem dgOsc_fields_mono {n : ℕ} {U V : Set (Point n)} (hVU : V ⊆ U)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hf : DGClassicalFields U A c f u) : DGClassicalFields V A c f u :=
  ⟨fun i j => (hf.1 i j).mono hVU,fun i => (hf.2.1 i).mono hVU,
    hf.2.2.1.mono hVU,hf.2.2.2.mono hVU⟩

theorem dgOsc_uniform_restrict {n : ℕ} {U V : Set (Point n)} {ν L D F : ℝ} (hVU : V ⊆ U)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f : Point n → ℝ}
    (hb : DGUniformBounds U A c f ν L D F) : DGUniformBounds V A c f ν L D F :=
  ⟨⟨hb.1.1,hb.1.2.1,fun p hp => hb.1.2.2 p (hVU hp)⟩,
    fun p hp => hb.2.1 p (hVU hp),fun p hp => hb.2.2 p (hVU hp)⟩


theorem dgOscCylinder_subset {n : ℕ} {p₀ : Point n} {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    dgOscCylinder p₀ r ⊆ dgOscCylinder p₀ R := by
  intro p hp
  refine ⟨Metric.ball_subset_ball hrR hp.1,?_,hp.2.2⟩
  have hh := pow_le_pow_left₀ hr hrR 2
  linarith only [hp.2.1,hh]

theorem dgOscCylinderOpen_subset {n : ℕ} {p₀ : Point n} {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    dgOscCylinderOpen p₀ r ⊆ dgOscCylinderOpen p₀ R := by
  intro p hp
  refine ⟨Metric.ball_subset_ball hrR hp.1,?_,hp.2.2⟩
  have hh := pow_le_pow_left₀ hr hrR 2
  linarith only [hp.2.1,hh]

def dgOscDriftRadius (D : ℝ) : ℝ := min 1 ((1+D)⁻¹)

theorem dgOscDriftRadius_pos {D : ℝ} (hD : 0 ≤ D) : 0 < dgOscDriftRadius D := by
  dsimp only [dgOscDriftRadius]
  positivity

theorem dgOsc_scaled_drift_le_one {D R : ℝ} (hD : 0 ≤ D) (hR : 0 < R)
    (hRs : R ≤ dgOscDriftRadius D) : |R/2| *D ≤ 1 := by
  have hh : R ≤ 1/(1+D) := by simpa only [one_div] using hRs.trans (min_le_right _ _)
  have hp : R*(1+D) ≤ 1 := (le_div_iff₀ (by positivity : (0:ℝ) < 1+D)).mp hh
  rw [abs_of_pos (by positivity : (0:ℝ) < R/2)]
  nlinarith only [hp,hR]

end Yau.LeafProofs.L16Aux
