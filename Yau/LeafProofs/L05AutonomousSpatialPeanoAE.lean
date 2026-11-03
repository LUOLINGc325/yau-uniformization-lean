import Yau.LeafProofs.L05AutonomousSpatialSemiconvex
import Yau.LeafProofs.L05AutonomousPeanoFirst
import Mathlib.Analysis.Calculus.FDeriv.Measurable

noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

theorem auto_spatial_peano_congr {n : ℕ} {f g : Space n → ℝ} {x : Space n}
    {l : Space n →L[ℝ] ℝ} {B : Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (heq : f=ᶠ[𝓝 x] g) (h : autoSpatialPeanoJet f x l B) : autoSpatialPeanoJet g x l B := by
  refine ⟨h.1,?_⟩
  refine h.2.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [heq] with y hy
  rw [hy,heq.eq_of_nhds]


/-- The actual first derivative fixes the linear coefficient of each genuine spatial Peano expansion. -/
theorem auto_ae_spatial_peano_with_gradient {n : ℕ} {O : Set (Space n)} (hO : MeasurableSet O)
    {f : Space n → ℝ} {G : Space n → (Space n →L[ℝ] ℝ)}
    (hFirst : ∀ x∈O, HasFDerivAt f (G x) x)
    (hPeano : ∀ᵐ x ∂((volume : Measure (Space n)).restrict O), ∃ l B, autoSpatialPeanoJet f x l B) :
    ∀ᵐ x ∂((volume : Measure (Space n)).restrict O), ∃ B : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∀ v w, B v w=B w v) ∧
      (fun y => f y-f x-G x (y-x)-(1/2 : ℝ)*B (y-x) (y-x)) =o[𝓝 x] (fun y => ‖y-x‖^2) := by
  filter_upwards [hPeano,ae_restrict_mem hO] with x hx hxO
  obtain ⟨l,B,hJet⟩ := hx
  have hEq : l=G x := (auto_spatial_peano_hasFDerivAt hJet).unique (hFirst x hxO)
  exact ⟨B,by simpa only [autoSpatialPeanoJet,hEq] using hJet⟩

/-- The actual derivative of a globally continuous source is a measurable field,
with no global differentiability assumption. -/
theorem auto_spatialD_measurable {n : ℕ} {u : Point n → ℝ} (hu : Continuous u) :
    Measurable (spatialD u) := by
  let f : ℝ → Space n → ℝ := fun t x => u (x,t)
  have hf : Continuous f.uncurry := hu.comp continuous_swap
  have hm := (measurable_fderiv_with_param ℝ hf).comp measurable_swap
  exact hm

/-- At every actual Peano point its linear part equals the actual total fderiv.
This makes the measurable Peano provider independent of the gradient limit. -/
theorem auto_ae_spatial_peano_with_actual_fderiv {n : ℕ} {O : Set (Space n)}
    {f : Space n → ℝ}
    (hPeano : ∀ᵐ x ∂((volume : Measure (Space n)).restrict O), ∃ l B, autoSpatialPeanoJet f x l B) :
    ∀ᵐ x ∂((volume : Measure (Space n)).restrict O), ∃ B : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∀ v w, B v w=B w v) ∧
      (fun y => f y-f x-fderiv ℝ f x (y-x)-(1/2 : ℝ)*B (y-x) (y-x))
        =o[𝓝 x] (fun y => ‖y-x‖^2) := by
  filter_upwards [hPeano] with x hx
  obtain ⟨l,B,hJet⟩ := hx
  have hEq : fderiv ℝ f x=l := (auto_spatial_peano_hasFDerivAt hJet).fderiv
  refine ⟨B,hJet.1,?_⟩
  rw [hEq]
  exact hJet.2

/-- Every original normalized solution has genuine spatial Peano jets almost everywhere on every slice. -/
theorem auto_original_ae_spatial_peano {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {F : Sym n → ℝ}
    (hF : Continuous F) (hE : globalElliptic F ell L) (hConc : ConcaveOn ℝ univ F) (h0 : F 0=0)
    {u : Point n → ℝ} (hu : ContinuousOn u (unitClosed n)) (hb : ∀ p∈unitClosed n, |u p| ≤ 1)
    (hsol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    {t : ℝ} (ht : t∈Icc (-(5/8 : ℝ)^2) 0) :
    ∀ᵐ x ∂((volume : Measure (Space n)).restrict (Metric.ball 0 (5/8))),
      ∃ l B, autoSpatialPeanoJet (fun y => u (y,t)) x l B := by
  obtain ⟨C,hC,hSemiconvex⟩ := auto_uniform_spatial_semiconvex n hn ell L hell hL
  have hConvex := hSemiconvex F hF hE hConc h0 u hu hb hsol t ht
  have hae := auto_convex_ae_spatial_peano Metric.isOpen_ball hConvex
  filter_upwards [hae] with x hx
  obtain ⟨l,B,hJet⟩ := hx
  exact ⟨l-C • spaceInnerBilin n x,B-C • spaceInnerBilin n,auto_spatial_semiconvex_peano hJet⟩

/-- Equality on the original closed cylinder gives genuine spatial neighborhood
equality at every buffered point, including its terminal time. -/
theorem auto_unit_spatial_eventuallyEq {n : ℕ} {u w : Point n → ℝ}
    (hwu : EqOn w u (unitClosed n)) {x : Space n} {t : ℝ}
    (hx : ‖x‖ < 1) (ht : t∈Icc (-1 : ℝ) 0) :
    (fun y => w (y,t))=ᶠ[𝓝 x](fun y => u (y,t)) := by
  have hxBall : x∈Metric.ball (0 : Space n) 1 := by
    simpa only [Metric.mem_ball,dist_zero_right] using hx
  filter_upwards [Metric.isOpen_ball.mem_nhds hxBall] with y hy
  exact hwu ⟨Metric.ball_subset_closedBall hy,ht⟩

/-- The actual compact extension has per-time Peano jets with its OWN actual
fderiv as linear part. No prior gradient limit or caller differentiability is used. -/
theorem auto_original_extension_ae_spatial_peano {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {F : Sym n → ℝ}
    (hF : Continuous F) (hE : globalElliptic F ell L) (hConc : ConcaveOn ℝ univ F) (h0 : F 0=0)
    {u w : Point n → ℝ} (hu : ContinuousOn u (unitClosed n))
    (hb : ∀ p∈unitClosed n, |u p| ≤ 1)
    (hsol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    (hwu : EqOn w u (unitClosed n)) {t : ℝ} (ht : t∈Icc (-(5/8 : ℝ)^2) 0) :
    ∀ᵐ x ∂((volume : Measure (Space n)).restrict (Metric.ball 0 (5/8))),
      ∃ B : Space n →L[ℝ] Space n →L[ℝ] ℝ, (∀ v z, B v z=B z v) ∧
      (fun y => w (y,t)-w (x,t)-spatialD w (x,t) (y-x)-
        (1/2 : ℝ)*B (y-x) (y-x)) =o[𝓝 x] (fun y => ‖y-x‖^2) := by
  have hOriginal := auto_original_ae_spatial_peano hn hell hL hF hE hConc h0 hu hb hsol ht
  have hPeano : ∀ᵐ x ∂((volume : Measure (Space n)).restrict (Metric.ball 0 (5/8))),
      ∃ l B, autoSpatialPeanoJet (fun y => w (y,t)) x l B := by
    filter_upwards [hOriginal,ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxBall
    obtain ⟨l,B,hJet⟩ := hx
    have hxNorm : ‖x‖ < 1 :=
      (show ‖x‖ < 5/8 by simpa only [Metric.mem_ball,dist_zero_right] using hxBall).trans (by norm_num)
    have htUnit : t∈Icc (-1 : ℝ) 0 := ⟨by linarith only [ht.1],ht.2⟩
    exact ⟨l,B,auto_spatial_peano_congr (auto_unit_spatial_eventuallyEq hwu hxNorm htUnit).symm hJet⟩
  exact auto_ae_spatial_peano_with_actual_fderiv hPeano

end Yau.LeafProofs.L05AutonomousAux
