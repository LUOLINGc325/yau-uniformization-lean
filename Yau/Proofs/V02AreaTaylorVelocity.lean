import Yau.Proofs.V02AreaTaylorFamily
import Yau.Proofs.V02AreaTaylorSprayModel
import Yau.Proofs.V02AreaTaylorChartBound
import Yau.Proofs.V02AreaTaylorEnergy

/-! The original closed-disc spray differential is the actual differential
of its finite-dimensional input map. Its squared input velocity has the
original uniform area/Fourier integrable majorant. -/

open scoped Topology ContDiff Matrix Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof
open Yau Yau.Blueprint V03Proof

set_option synthInstance.maxHeartbeats 100000

variable {n q b : ℕ} {X : KahlerManifold n}

def inputData (x : Pt X) (f : ℂ → CotangentPoint X.manifold) (h : ℂ → ℂ)
    (c : ℂ → ComplexVector b) (ζ : ℂ) : SprayData n b :=
  (cotangentChart x (f ζ), (h ζ, c ζ))

theorem inputData_contDiffWithinAt {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f)
    {h : ℂ → ℂ} (hh : ContDiffOn ℂ ∞ h (Metric.closedBall 0 1))
    {c : ℂ → ComplexVector b} (hc : ContDiffOn ℂ ∞ c (Metric.closedBall 0 1))
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1) (x : Pt X) (hx : f ζ ∈ cotangentSource x) :
    ContDiffWithinAt ℂ ∞ (inputData x f h c) (Metric.closedBall 0 1) ζ :=
  (cotangentDisc_coords_contDiffWithinAt hf hζ x hx).prodMk ((hh ζ hζ).prodMk (hc ζ hζ))

theorem inputData_derivative {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f)
    {h : ℂ → ℂ} (hh : ContDiffOn ℂ ∞ h (Metric.closedBall 0 1))
    {c : ℂ → ComplexVector b} (hc : ContDiffOn ℂ ∞ c (Metric.closedBall 0 1))
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1) (x : Pt X) (hx : f ζ ∈ cotangentSource x) :
    closedDiscDerivative (inputData x f h c) ζ =
      (closedDiscDerivative (fun η => cotangentChart x (f η)) ζ,
        (closedDiscDerivative h ζ, closedDiscDerivative c ζ)) := by
  have hfD := (cotangentDisc_coords_contDiffWithinAt hf hζ x hx).differentiableWithinAt (by simp)
  have hhD := (hh ζ hζ).differentiableWithinAt (by simp)
  have hcD := (hc ζ hζ).differentiableWithinAt (by simp)
  exact congrArg (fun A : ℂ →L[ℂ] SprayData n b => A 1)
    ((hfD.hasFDerivWithinAt.prodMk (hhD.hasFDerivWithinAt.prodMk hcD.hasFDerivWithinAt)).fderivWithin
      (uniqueDiffOn_complex_closedDisc ζ hζ))

theorem spray_coordinate_eventuallyEq
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f)
    (h : ℂ → ℂ) (c : ℂ → ComplexVector b) (z : ℂ)
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1) (x : Pt X) (hx : f ζ ∈ cotangentSource x) :
    (fun η => cotangentChart x (sprayFamily Ψ f h c z η)) =ᶠ[𝓝[Metric.closedBall 0 1] ζ]
      (fun η => localSprayMap Ψ x (z, inputData x f h c η)) := by
  have hs : ∀ᶠ η in 𝓝[Metric.closedBall 0 1] ζ, f η ∈ cotangentSource x :=
    (hf.1 ζ hζ).continuousWithinAt.preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hx)
  filter_upwards [hs] with η hη
  simp only [localSprayMap, sprayCoordinate, sprayInput, inputData, sprayFamily,
    cotangentChart_left_inv x hη]

theorem spray_coordinate_derivative
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f)
    {h : ℂ → ℂ} (hh : ContDiffOn ℂ ∞ h (Metric.closedBall 0 1))
    {c : ℂ → ComplexVector b} (hc : ContDiffOn ℂ ∞ c (Metric.closedBall 0 1))
    (x : Pt X) {a : CotangentCoord n} {δ R : ℝ}
    (hψ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R))
    {z ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1) (hx : f ζ ∈ cotangentSource x)
    (hp : (z, inputData x f h c ζ) ∈ localSprayDomain a δ R) :
    closedDiscDerivative (fun η => cotangentChart x (sprayFamily Ψ f h c z η)) ζ =
      localSprayDifferential Ψ x (z, inputData x f h c ζ)
        (closedDiscDerivative (inputData x f h c) ζ) := by
  have hT := (localSprayMap_contDiffOn x hψ).contDiffAt ((localSprayDomain_isOpen a δ R).mem_nhds hp)
  have hs : DifferentiableAt ℂ (fun u => localSprayMap Ψ x (z, u)) (inputData x f h c ζ) :=
    (hT.comp _ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hinput := (inputData_contDiffWithinAt hf hh hc hζ x hx).differentiableWithinAt (by simp)
  unfold closedDiscDerivative
  rw [(spray_coordinate_eventuallyEq Ψ hf h c z hζ x hx).fderivWithin_eq_of_mem hζ]
  change (fderivWithin ℂ ((fun u => localSprayMap Ψ x (z, u)) ∘ inputData x f h c)
    (Metric.closedBall 0 1) ζ) 1 = _
  rw [fderiv_comp_fderivWithin ζ hs hinput (uniqueDiffOn_complex_closedDisc ζ hζ),
    ContinuousLinearMap.comp_apply, ← localSprayDifferential_eq_slice x hψ hp]

theorem spatialDensity_eq_localKernel {d : VariationData X q} (hG : CotangentImmersion d.G)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f)
    {h : ℂ → ℂ} (hh : ContDiffOn ℂ ∞ h (Metric.closedBall 0 1))
    {c : ℂ → ComplexVector b} (hc : ContDiffOn ℂ ∞ c (Metric.closedBall 0 1))
    (x : Pt X) {a : CotangentCoord n} {δ R : ℝ}
    (hψ : ContDiffOn ℂ ∞ (sprayCoordinate Ψ x) (Metric.ball a (2 * δ) ×ˢ Metric.ball 0 R))
    {z ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1) (hx : f ζ ∈ cotangentSource x)
    (hp : (z, inputData x f h c ζ) ∈ localSprayDomain a δ R)
    (hs : CotangentDisc (sprayFamily Ψ f h c z))
    (hy : sprayFamily Ψ f h c z ζ ∈ cotangentSource x) :
    spatialDensity d (sprayFamily Ψ f h c z) ζ =
      complexDiagonal (localSpatialKernel d Ψ x (z, inputData x f h c ζ))
        (closedDiscDerivative (inputData x f h c) ζ) := by
  rw [spatialDensity_eq_coordinate hG hs hζ x hy]
  change complexDiagonal (spatialChartBilinear d.G X.metric.form x _)
    (closedDiscDerivative (fun η => cotangentChart x (sprayFamily Ψ f h c z η)) ζ) = _
  rw [spray_coordinate_derivative hf hh hc x hψ hζ hx hp,
    (spray_coordinate_eventuallyEq Ψ hf h c z hζ x hx).eq_of_nhdsWithin hζ]
  exact (complexDiagonal_pullback _ _ _).symm

theorem norm_triple_sq_le {E F H : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup H] (u : E) (v : F) (w : H) :
    ‖(u, (v, w))‖ ^ 2 ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  simp only [Prod.norm_mk]
  rcases le_total ‖v‖ ‖w‖ with h | h
  · rw [max_eq_right h]
    rcases le_total ‖u‖ ‖w‖ with g | g
    · rw [max_eq_right g]; nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖v‖]
    · rw [max_eq_left g]; nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖w‖]
  · rw [max_eq_left h]
    rcases le_total ‖u‖ ‖v‖ with g | g
    · rw [max_eq_right g]; nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖w‖]
    · rw [max_eq_left g]; nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖w‖]

theorem norm_inputData_derivative_sq_le {d : VariationData X q} (hG : CotangentImmersion d.G)
    {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f)
    {h : ℂ → ℂ} (hh : ContDiffOn ℂ ∞ h (Metric.closedBall 0 1))
    {c : ℂ → ComplexVector b} (hc : ContDiffOn ℂ ∞ c (Metric.closedBall 0 1))
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall 0 1) (x : Pt X) (hx : f ζ ∈ cotangentSource x)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ v : CotangentCoord n, ‖v‖ ≤ L *
      ‖fderiv ℂ (fun w => d.G (cotangentChartInv x w)) (cotangentChart x (f ζ)) v‖) :
    ‖closedDiscDerivative (inputData x f h c) ζ‖ ^ 2 ≤
      (L + 1) ^ 2 * inputDerivativeWeight (fun η => d.G (f η)) h c ζ := by
  have hambient := congrArg (fun A : ℂ →L[ℂ] ComplexVector q => A 1)
    (cotangentHolomorphicOn_ambient_fderivWithin hG.1 (cotangentDisc_holomorphicOn hf)
      hζ (uniqueDiffOn_complex_closedDisc ζ hζ) x hx)
  simp only [ContinuousLinearMap.comp_apply] at hambient
  have hcoord := hbound (closedDiscDerivative (fun η => cotangentChart x (f η)) ζ)
  change ‖closedDiscDerivative (fun η => cotangentChart x (f η)) ζ‖ ≤
    L * ‖fderiv ℂ (fun w => d.G (cotangentChartInv x w)) (cotangentChart x (f ζ))
      (fderivWithin ℂ (fun η => cotangentChart x (f η)) (Metric.closedBall 0 1) ζ 1)‖ at hcoord
  rw [← hambient] at hcoord
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mpr hcoord
  rw [mul_pow] at hsquare
  have hL2 : L ^ 2 ≤ (L + 1) ^ 2 := by nlinarith
  have hL1 : 1 ≤ (L + 1) ^ 2 := by nlinarith
  rw [inputData_derivative hf hh hc hζ x hx]
  refine (norm_triple_sq_le _ _ _).trans ?_
  unfold inputDerivativeWeight
  calc
    _ ≤ L ^ 2 * ‖closedDiscDerivative (fun η => d.G (f η)) ζ‖ ^ 2 +
        ‖closedDiscDerivative h ζ‖ ^ 2 + ‖closedDiscDerivative c ζ‖ ^ 2 := by
      exact add_le_add (add_le_add hsquare le_rfl) le_rfl
    _ ≤ (L + 1) ^ 2 * ‖closedDiscDerivative (fun η => d.G (f η)) ζ‖ ^ 2 +
        (L + 1) ^ 2 * ‖closedDiscDerivative h ζ‖ ^ 2 +
        (L + 1) ^ 2 * ‖closedDiscDerivative c ζ‖ ^ 2 := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hL2 (sq_nonneg _))
        (le_mul_of_one_le_left (sq_nonneg _) hL1))
        (le_mul_of_one_le_left (sq_nonneg _) hL1)
    _ = _ := by ring

end Yau.Blueprint.V02AreaTaylorProof
