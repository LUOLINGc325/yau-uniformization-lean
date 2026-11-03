import Yau.LeafProofs.L16
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- The actual orthogonal reflection in the hyperplane normal to `e`. -/
def halfSpaceReflection {n : ℕ} (e : Space n) : Space n ≃ₗᵢ[ℝ] Space n :=
  (ℝ ∙ e)ᗮ.reflection

theorem halfSpaceReflection_apply {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (x : Space n) : halfSpaceReflection e x = x - (2*inner ℝ e x) • e := by
  rw [halfSpaceReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, he]
  simp only [RCLike.ofReal_real_eq_id, id_eq, one_pow, div_one]
  module

theorem halfSpaceReflection_normal {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (x : Space n) : inner ℝ e (halfSpaceReflection e x) = -inner ℝ e x := by
  rw [halfSpaceReflection_apply he]
  simp only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow]
  ring

theorem halfSpaceReflection_boundary {n : ℕ} {e x : Space n}
    (he : ‖e‖ = 1) (hx : inner ℝ e x = 0) : halfSpaceReflection e x = x := by
  rw [halfSpaceReflection_apply he, hx]
  simp

theorem halfSpaceReflection_twice {n : ℕ} (e x : Space n) :
    halfSpaceReflection e (halfSpaceReflection e x) = x :=
  Submodule.reflection_reflection _ x

/-- The genuine Dirichlet heat kernel obtained by reflection. -/
def dirichletGaussianKernel {n : ℕ} (e : Space n) (t : ℝ)
    (x y : Space n) : ℝ :=
  gaussianKernel t (x-y) - gaussianKernel t (x-halfSpaceReflection e y)

theorem dirichletGaussianKernel_boundary {n : ℕ} {e x : Space n}
    (he : ‖e‖ = 1) (hx : inner ℝ e x = 0) (t : ℝ) (y : Space n) :
    dirichletGaussianKernel e t x y = 0 := by
  have hnorm : ‖x-halfSpaceReflection e y‖ = ‖x-y‖ := by
    have h := (halfSpaceReflection e).norm_map (x-y)
    rw [map_sub, halfSpaceReflection_boundary he hx] at h
    exact h
  simp only [dirichletGaussianKernel, gaussianKernel, hnorm, sub_self]

theorem halfSpaceReflection_distance_sq {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (x y : Space n) :
    ‖x-halfSpaceReflection e y‖^2 = ‖x-y‖^2+4*inner ℝ e x*inner ℝ e y := by
  rw [norm_sub_sq_real, norm_sub_sq_real, (halfSpaceReflection e).norm_map,
    halfSpaceReflection_apply he]
  simp only [inner_sub_right, inner_smul_right]
  rw [real_inner_comm x e]
  ring

theorem dirichletGaussianKernel_nonneg {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {t : ℝ} (ht : 0 < t) {x y : Space n}
    (hx : 0 ≤ inner ℝ e x) (hy : 0 ≤ inner ℝ e y) :
    0 ≤ dirichletGaussianKernel e t x y := by
  have hsq : ‖x-y‖^2 ≤ ‖x-halfSpaceReflection e y‖^2 := by
    rw [halfSpaceReflection_distance_sq he]
    nlinarith [mul_nonneg hx hy]
  have hExp : -‖x-halfSpaceReflection e y‖^2/(4*t) ≤ -‖x-y‖^2/(4*t) :=
    div_le_div_of_nonneg_right (neg_le_neg hsq) (by positivity)
  apply sub_nonneg.mpr
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) (by positivity)

theorem dirichletGaussianKernel_le {n : ℕ} (e : Space n) {t : ℝ} (ht : 0 < t)
    (x y : Space n) : dirichletGaussianKernel e t x y ≤ gaussianKernel t (x-y) := by
  exact sub_le_self _ (gaussianKernel_pos ht _).le


theorem dirichletGaussianKernel_integrable {n : ℕ} (e : Space n) {t : ℝ}
    (ht : 0 < t) (x : Space n) : Integrable (dirichletGaussianKernel e t x) := by
  have hFirst := (gaussianKernel_integrable (n := n) ht).comp_sub_left x
  have hSecond := (halfSpaceReflection e).measurePreserving.integrable_comp_of_integrable hFirst
  exact hFirst.sub hSecond

theorem dirichletGaussianKernel_mass_bound {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {t : ℝ} (ht : 0 < t) {x : Space n} (hx : 0 ≤ inner ℝ e x) :
    let H := {y : Space n | 0 ≤ inner ℝ e y}
    0 ≤ (∫ y in H, dirichletGaussianKernel e t x y) ∧
      (∫ y in H, dirichletGaussianKernel e t x y) ≤ 1 := by
  dsimp only
  let H := {y : Space n | 0 ≤ inner ℝ e y}
  have hH : MeasurableSet H := isClosed_le continuous_const (continuous_const.inner continuous_id) |>.measurableSet
  have hFirst := (gaussianKernel_integrable (n := n) ht).comp_sub_left x
  have hKernel := dirichletGaussianKernel_integrable e ht x
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem hH] with y hy
    exact dirichletGaussianKernel_nonneg he ht hx hy
  · calc
      (∫ y in H, dirichletGaussianKernel e t x y) ≤ ∫ y in H, gaussianKernel t (x-y) := by
        apply integral_mono_ae hKernel.integrableOn hFirst.integrableOn
        exact Filter.Eventually.of_forall (dirichletGaussianKernel_le e ht x)
      _ ≤ ∫ y : Space n, gaussianKernel t (x-y) := by
        exact integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun y => (gaussianKernel_pos ht (x-y)).le) hFirst
      _ = 1 := by
        rw [integral_sub_left_eq_self (gaussianKernel t) volume x, gaussianKernel_integral ht]


/-- The actual reflected heat average integrates only over the half-space. -/
def dirichletHeatAverage {n : ℕ} (e : Space n) (t : ℝ)
    (g : Space n → ℝ) (x : Space n) : ℝ :=
  ∫ y in {y : Space n | 0 ≤ inner ℝ e y}, dirichletGaussianKernel e t x y*g y

theorem dirichletHeatAverage_boundary {n : ℕ} {e x : Space n}
    (he : ‖e‖ = 1) (hx : inner ℝ e x = 0) (t : ℝ) (g : Space n → ℝ) :
    dirichletHeatAverage e t g x = 0 := by
  simp only [dirichletHeatAverage, dirichletGaussianKernel_boundary he hx,
    zero_mul, integral_zero]

theorem dirichletHeatAverage_integrable {n : ℕ} (e : Space n) {t B : ℝ}
    (ht : 0 < t) {g : Space n → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict {y | 0 ≤ inner ℝ e y}))
    (hB : ∀ y, 0 ≤ inner ℝ e y → |g y| ≤ B) (x : Space n) :
    Integrable (fun y => dirichletGaussianKernel e t x y*g y)
      (volume.restrict {y : Space n | 0 ≤ inner ℝ e y}) := by
  apply (dirichletGaussianKernel_integrable e ht x).integrableOn.mul_bdd hg
  have hH : MeasurableSet {y : Space n | 0 ≤ inner ℝ e y} :=
    isClosed_le continuous_const (continuous_const.inner continuous_id) |>.measurableSet
  filter_upwards [ae_restrict_mem hH] with y hy
  exact hB y hy

theorem dirichletHeatAverage_bound {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {t B : ℝ} (ht : 0 < t) (hB0 : 0 ≤ B) {g : Space n → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict {y | 0 ≤ inner ℝ e y}))
    (hB : ∀ y, 0 ≤ inner ℝ e y → |g y| ≤ B)
    {x : Space n} (hx : 0 ≤ inner ℝ e x) : |dirichletHeatAverage e t g x| ≤ B := by
  let H := {y : Space n | 0 ≤ inner ℝ e y}
  have hH : MeasurableSet H :=
    isClosed_le continuous_const (continuous_const.inner continuous_id) |>.measurableSet
  have hInt := dirichletHeatAverage_integrable e ht hg hB x
  have hKernel := (dirichletGaussianKernel_integrable e ht x).integrableOn (s := H)
  have hDom : ∀ᵐ y ∂volume.restrict H,
      ‖dirichletGaussianKernel e t x y*g y‖ ≤ B*dirichletGaussianKernel e t x y := by
    filter_upwards [ae_restrict_mem hH] with y hy
    have hPos := dirichletGaussianKernel_nonneg he ht hx hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hPos]
    nlinarith [hB y hy]
  calc
    |dirichletHeatAverage e t g x| ≤ ∫ y in H, ‖dirichletGaussianKernel e t x y*g y‖ :=
      by simpa only [Real.norm_eq_abs, dirichletHeatAverage] using
        (norm_integral_le_integral_norm (μ := volume.restrict H)
          (fun y => dirichletGaussianKernel e t x y*g y))
    _ ≤ ∫ y in H, B*dirichletGaussianKernel e t x y :=
      integral_mono_ae hInt.norm (hKernel.const_mul B) hDom
    _ = B*(∫ y in H, dirichletGaussianKernel e t x y) := integral_const_mul _ _
    _ ≤ B := by
      have hMass := (dirichletGaussianKernel_mass_bound he ht hx).2
      nlinarith


theorem dirichletGaussianKernel_spatial_smooth {n : ℕ} (e : Space n)
    (t : ℝ) (y : Space n) : ContDiff ℝ ∞ (fun x => dirichletGaussianKernel e t x y) := by
  exact ((gaussianKernel_spatial_smooth t).comp (contDiff_id.sub contDiff_const)).sub
    ((gaussianKernel_spatial_smooth t).comp (contDiff_id.sub contDiff_const))

theorem dirichletGaussianKernel_joint_smooth {n : ℕ} (e : Space n)
    {t : ℝ} (ht : 0 < t) (x y : Space n) :
    ContDiffAt ℝ ∞ (fun p : Point n => dirichletGaussianKernel e p.2 p.1 y) (x,t) := by
  exact ((gaussianKernel_joint_smooth ht (x-y)).comp (x,t)
    (contDiffAt_snd.prodMk (contDiffAt_fst.sub contDiffAt_const))).sub
    ((gaussianKernel_joint_smooth ht (x-halfSpaceReflection e y)).comp (x,t)
      (contDiffAt_snd.prodMk (contDiffAt_fst.sub contDiffAt_const)))


theorem dirichletGaussianKernel_joint_measurable {n : ℕ} (e x : Space n)
    (t : ℝ) : Measurable (fun p : ℝ × Space n =>
      dirichletGaussianKernel e (t-p.1) x p.2) := by
  have hFirst := (gaussianKernel_joint_measurable (n := n)).comp
    (show Measurable (fun p : ℝ × Space n => (t-p.1,x-p.2)) from by fun_prop)
  have hSecond := (gaussianKernel_joint_measurable (n := n)).comp
    (show Measurable (fun p : ℝ × Space n =>
      (t-p.1,x-halfSpaceReflection e p.2)) from by
        exact (measurable_const.sub measurable_fst).prodMk
          (measurable_const.sub ((halfSpaceReflection e).continuous.measurable.comp measurable_snd)))
  exact hFirst.sub hSecond

/-- The genuine reflected Duhamel potential, with both zero-data faces. -/
def dirichletHeatDuhamel {n : ℕ} (e : Space n) (f : Point n → ℝ)
    (t : ℝ) (x : Space n) : ℝ :=
  ∫ s in (0 : ℝ)..t, dirichletHeatAverage e (t-s) (fun y => f (y,s)) x

theorem dirichletHeatDuhamel_initial {n : ℕ} (e : Space n)
    (f : Point n → ℝ) (x : Space n) : dirichletHeatDuhamel e f 0 x = 0 := by
  simp only [dirichletHeatDuhamel, intervalIntegral.integral_same]

theorem dirichletHeatDuhamel_boundary {n : ℕ} {e x : Space n}
    (he : ‖e‖ = 1) (hx : inner ℝ e x = 0) (f : Point n → ℝ) (t : ℝ) :
    dirichletHeatDuhamel e f t x = 0 := by
  simp only [dirichletHeatDuhamel, dirichletHeatAverage_boundary he hx,
    intervalIntegral.integral_zero]

theorem dirichletHeatDuhamel_integrable_and_bound {n : ℕ} {e : Space n}
    (he : ‖e‖ = 1) {f : Point n → ℝ} {B t : ℝ} (hf : Measurable f)
    (hB0 : 0 ≤ B) (hB : ∀ p, 0 ≤ inner ℝ e p.1 → p.2 ∈ Set.Icc 0 t → |f p| ≤ B)
    (ht : 0 ≤ t) {x : Space n} (hx : 0 ≤ inner ℝ e x) :
    IntervalIntegrable (fun s : ℝ => dirichletHeatAverage e (t-s)
      (fun y => f (y,s)) x) volume 0 t ∧ |dirichletHeatDuhamel e f t x| ≤ t*B := by
  let H := {y : Space n | 0 ≤ inner ℝ e y}
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 t)
  let ν : Measure (Space n) := volume.restrict H
  letI : IsFiniteMeasure μ := ⟨by simp [μ,Real.volume_Ioc]⟩
  have hF : Measurable (fun p : ℝ × Space n =>
      dirichletGaussianKernel e (t-p.1) x p.2*f (p.2,p.1)) := by
    exact (dirichletGaussianKernel_joint_measurable e x t).mul
      (hf.comp measurable_swap)
  have hm : AEStronglyMeasurable (fun s : ℝ =>
      dirichletHeatAverage e (t-s) (fun y => f (y,s)) x) μ := by
    simpa only [dirichletHeatAverage, Function.uncurry_apply_pair] using
      (hF.aestronglyMeasurable (μ := μ.prod ν)).integral_prod_right'
  have hb : ∀ᵐ s ∂μ,
      |dirichletHeatAverage e (t-s) (fun y => f (y,s)) x| ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, μ.ae_ne t] with s hs hst
    have hst' : s < t := lt_of_le_of_ne hs.2 hst
    apply dirichletHeatAverage_bound he (sub_pos.mpr hst') hB0 _ _ hx
    · exact (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · intro y hy
      exact hB (y,s) hy ⟨hs.1.le,hs.2⟩
  have hi : Integrable (fun s : ℝ =>
      dirichletHeatAverage e (t-s) (fun y => f (y,s)) x) μ := by
    apply (integrable_const B).mono' hm
    filter_upwards [hb] with s hs
    simpa only [Real.norm_eq_abs] using hs
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hi,?_⟩
  have hvol : μ.real Set.univ = t := by
    simp [μ,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal ht]
  have hn := norm_integral_le_of_norm_le_const
    (μ := μ) (f := fun s : ℝ => dirichletHeatAverage e (t-s) (fun y => f (y,s)) x)
    (by filter_upwards [hb] with s hs; simpa only [Real.norm_eq_abs] using hs)
  rw [dirichletHeatDuhamel,intervalIntegral.integral_of_le ht]
  change |∫ s, dirichletHeatAverage e (t-s) (fun y => f (y,s)) x ∂μ| ≤ t*B
  simpa only [Real.norm_eq_abs,hvol,mul_comm] using hn

end Yau.LeafProofs.L16Aux
