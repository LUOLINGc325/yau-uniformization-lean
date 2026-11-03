import Yau.LeafProofs.L05ABPMollifier
import Yau.LeafProofs.L05ABPLasryConvexity

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance L05ABPMollifierConvexity_pointVolumeHaar (n : ℕ) :
    (volume : Measure (Point n)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _

theorem affine_sub_mix {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z y q : E) {a b : ℝ} (hab : a+b=1) :
    a • (z-q)+b • (y-q)=(a • z+b • y)-q := by
  calc
    _ = (a • z+b • y)-(a+b) • q := by module
    _ = _ := by rw [hab,one_smul]

theorem jointSemiconvex_shifted {n : ℕ} {K : ℝ} {w : Point n → ℝ}
    (hw : jointSemiconvex K w) (q : Point n) :
    ConvexOn ℝ Set.univ (fun z => w (z-q)+(K/2)*qnorm2 z) := by
  refine ⟨convex_univ,?_⟩
  intro z hz y hy a b ha hb hab
  have hm := hw.2 (Set.mem_univ (z-q)) (Set.mem_univ (y-q)) ha hb hab
  rw [affine_sub_mix z y q hab] at hm
  have hq := congrArg (fun r : ℝ => (K/2)*r) (qnorm2_difference_affine z y q hab)
  simp only [smul_eq_mul] at hm ⊢
  nlinarith

theorem abpMollify_jointSemiconvex {n : ℕ} {w : Point n → ℝ} {K r : ℝ}
    (hr : 0<r) (hu : Continuous w) (hw : jointSemiconvex K w) :
    jointSemiconvex K (abpMollify r w) := by
  have hconv : ∀ᵐ q ∂(volume : Measure (Point n)),
      ConvexOn ℝ Set.univ (fun z => scaledKernel n r q*(w (z-q)+(K/2)*qnorm2 z)) := by
    apply Filter.Eventually.of_forall
    intro q
    convert! (jointSemiconvex_shifted hw q).smul (scaledKernel_nonneg hr q) using 1
  have hint (z : Point n) (_hz : z ∈ Set.univ) :
      Integrable (fun q => scaledKernel n r q*(w (z-q)+(K/2)*qnorm2 z)) := by
    have hc : Continuous (fun q => scaledKernel n r q*(w (z-q)+(K/2)*qnorm2 z)) :=
      (scaledKernel_smooth n r).continuous.mul ((hu.comp (continuous_const.sub continuous_id)).add continuous_const)
    exact hc.integrable_of_hasCompactSupport (scaledKernel_compactSupport hr).mul_right
  have hi := integral_convexOn_of_integrand_ae convex_univ hconv hint
  have he : (fun z : Point n => ∫ q, scaledKernel n r q*(w (z-q)+(K/2)*qnorm2 z))=
      (fun z => abpMollify r w z+(K/2)*qnorm2 z) := by
    funext z
    change (∫ q, scaledKernel n r q*(w (z-q)+(K/2)*qnorm2 z))=
      (∫ q, scaledKernel n r q*w (z-q))+(K/2)*qnorm2 z
    simp_rw [mul_add]
    rw [integral_add (abpMollify_integrand_integrable hr hu z)
      (abpMollify_integrand_integrable hr continuous_const z),integral_mul_const,
      scaledKernel_integral hr,one_mul]
  rwa [he] at hi

theorem norm_sq_difference_affine {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z y q : E) {a b : ℝ} (hab : a+b=1) :
    ‖a • z+b • y‖^2-‖a • z+b • y-q‖^2=
      a*(‖z‖^2-‖z-q‖^2)+b*(‖y‖^2-‖y-q‖^2) := by
  rw [norm_sub_sq_real,norm_sub_sq_real,norm_sub_sq_real]
  simp only [inner_add_left,real_inner_smul_left]
  have hb : b=1-a := by linarith
  rw [hb]
  ring

theorem spatialSemiconcave_shifted {n : ℕ} {K : ℝ} {w : Point n → ℝ}
    (hw : spatialSemiconcave K w) (q : Point n) (t : ℝ) :
    ConcaveOn ℝ Set.univ (fun x : Space n => w ((x,t)-q)-(K/2)*‖x‖^2) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  have hm := (hw (t-q.2)).2 (Set.mem_univ (x-q.1)) (Set.mem_univ (y-q.1)) ha hb hab
  rw [affine_sub_mix x y q.1 hab] at hm
  have hq := congrArg (fun r : ℝ => (K/2)*r) (norm_sq_difference_affine x y q.1 hab)
  simp only [smul_eq_mul] at hm ⊢
  change a*(w (x-q.1,t-q.2)-(K/2)*‖x‖^2)+b*(w (y-q.1,t-q.2)-(K/2)*‖y‖^2)≤
    w ((a • x+b • y)-q.1,t-q.2)-(K/2)*‖a • x+b • y‖^2
  nlinarith

theorem abpMollify_spatialSemiconcave {n : ℕ} {w : Point n → ℝ} {K r : ℝ}
    (hr : 0<r) (hu : Continuous w) (hw : spatialSemiconcave K w) :
    spatialSemiconcave K (abpMollify r w) := by
  intro t
  have hconc : ∀ᵐ q ∂(volume : Measure (Point n)),
      ConcaveOn ℝ Set.univ (fun x : Space n => scaledKernel n r q*(w ((x,t)-q)-(K/2)*‖x‖^2)) := by
    apply Filter.Eventually.of_forall
    intro q
    convert! (spatialSemiconcave_shifted hw q t).smul (scaledKernel_nonneg hr q) using 1
  have hint (x : Space n) (_hx : x ∈ Set.univ) :
      Integrable (fun q => scaledKernel n r q*(w ((x,t)-q)-(K/2)*‖x‖^2)) := by
    have hc : Continuous (fun q => scaledKernel n r q*(w ((x,t)-q)-(K/2)*‖x‖^2)) :=
      (scaledKernel_smooth n r).continuous.mul ((hu.comp (continuous_const.sub continuous_id)).sub continuous_const)
    exact hc.integrable_of_hasCompactSupport (scaledKernel_compactSupport hr).mul_right
  have hi := integral_concaveOn_of_integrand_ae convex_univ hconc hint
  have he : (fun x : Space n => ∫ q, scaledKernel n r q*(w ((x,t)-q)-(K/2)*‖x‖^2))=
      (fun x => abpMollify r w (x,t)-(K/2)*‖x‖^2) := by
    funext x
    change (∫ q, scaledKernel n r q*(w ((x,t)-q)-(K/2)*‖x‖^2))=
      (∫ q, scaledKernel n r q*w ((x,t)-q))-(K/2)*‖x‖^2
    simp_rw [mul_sub]
    rw [integral_sub (abpMollify_integrand_integrable hr hu (x,t))
      (abpMollify_integrand_integrable hr continuous_const (x,t)),integral_mul_const,
      scaledKernel_integral hr,one_mul]
  rwa [he] at hi

end Yau.LeafProofs.L05Aux
