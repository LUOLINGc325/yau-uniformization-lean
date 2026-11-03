import Yau.Proofs.C03ShortLiftBounds
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! A continuous actual local section of the original map is complex smooth. -/
noncomputable section
open scoped Topology ContDiff Manifold
open Filter Set
namespace Yau.Proofs.C03Aux.ShortLift
open Yau Yau.Blueprint

set_option backward.isDefEq.respectTransparency false

theorem contDiffAt_of_invertible_comp
    {𝕜 E F A : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    {m : ℕ∞ω} {G : E → F} {sigma : A → E} {H : A → F} {x : A}
    (hcont : ContinuousAt sigma x) (hG : ContDiffAt 𝕜 m G (sigma x))
    (D : E ≃L[𝕜] F) (hD : HasFDerivAt G (D : E →L[𝕜] F) (sigma x))
    (hm : m ≠ 0) (hH : ContDiffAt 𝕜 m H x)
    (heq : G ∘ sigma =ᶠ[𝓝 x] H) : ContDiffAt 𝕜 m sigma x := by
  let e := hG.toOpenPartialHomeomorph G hD hm
  have hx : sigma x ∈ e.source := hG.mem_toOpenPartialHomeomorph_source hD hm
  have hval : G (sigma x) = H x := heq.eq_of_nhds
  have hinv : ContDiffAt 𝕜 m e.symm (H x) := by
    rw [← hval]
    exact hG.to_localInverse hD hm
  have hcomp := hinv.comp x hH
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hcont.preimage_mem_nhds (e.open_source.mem_nhds hx), heq] with y hy heqy
  change sigma y = e.symm (H y)
  rw [← heqy]
  exact (e.left_inv hy).symm

variable {n : ℕ} {M : ComplexManifold n}
local instance : ContinuousSMul ℂ (ComplexVector n) where
  continuous_smul := by
    change Continuous (fun p : ℂ × ComplexVector n =>
      WithLp.toLp 2 (fun i => p.1 * p.2 i))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
      (continuous_pi fun i => continuous_fst.mul
        ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).continuous.comp continuous_snd))

theorem section_contDiffOn {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hPhi : IsLocalBiholomorphism Phi r) (ctarget : M.Carrier)
    {S : Set (ComplexVector n)} (hS : IsOpen S)
    (sigma : ComplexVector n → ComplexVector n) (hcont : ContinuousOn sigma S)
    (hmem : MapsTo sigma S (Metric.ball 0 r))
    (hTarget : S ⊆ chartTarget ctarget)
    (hright : ∀ w ∈ S, Phi (sigma w) = chartInv ctarget w) :
    ContDiffOn ℂ ∞ sigma S := by
  intro w hw
  let z := sigma w
  let G : ComplexVector n → ComplexVector n := fun u => chartPt (Phi z) (Phi u)
  let H : ComplexVector n → ComplexVector n := fun u => chartPt (Phi z) (chartInv ctarget u)
  obtain ⟨hG, hGb⟩ := C07Aux.coordinate_chart_invertible hPhi (hmem hw)
  change ContDiffAt ℂ ∞ G z at hG
  change Function.Bijective (fderiv ℂ G z) at hGb
  let D : ComplexVector n ≃L[ℂ] ComplexVector n :=
    ContinuousLinearEquiv.ofBijective (fderiv ℂ G z)
      (LinearMap.ker_eq_bot.mpr hGb.1) (LinearMap.range_eq_top.mpr hGb.2)
  have hD : HasFDerivAt G (D : ComplexVector n →L[ℂ] ComplexVector n) z := by
    simpa only [D, ContinuousLinearEquiv.coe_ofBijective] using
      (hG.differentiableAt (by simp)).hasFDerivAt
  have hi : ContMDiffAt (ComplexModel n) (ComplexModel n) ∞ (chartInv ctarget) w :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) ctarget).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) ctarget).mem_nhds (hTarget hw))
  have hc : ContMDiffAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞
      (chartPt (Phi z)) (chartInv ctarget w) := by
    rw [← hright w hw]
    exact contMDiffAt_extChartAt
  have hH : ContDiffAt ℂ ∞ H w := (hc.comp w hi).contDiffAt
  have heq : G ∘ sigma =ᶠ[𝓝 w] H := by
    filter_upwards [hS.mem_nhds hw] with u hu
    change chartPt (Phi z) (Phi (sigma u)) = chartPt (Phi z) (chartInv ctarget u)
    rw [hright u hu]
  exact (contDiffAt_of_invertible_comp (hcont.continuousAt (hS.mem_nhds hw))
    hG D hD (by simp) hH heq).contDiffWithinAt

end Yau.Proofs.C03Aux.ShortLift

