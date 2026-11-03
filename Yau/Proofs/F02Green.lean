import Yau.Proofs.F02Cutoff
import Yau.LeafProofs.L22Locality
import Yau.LeafProofs.L19

/-! Moving the actual initial Kähler Laplacian onto a compact cutoff. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.F02Aux
open Yau Blueprint
open LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem laplacian_congr_local (g : HermitianField M) {f k : M.Carrier → ℝ}
    {x : M.Carrier} (hfk : f =ᶠ[𝓝 x] k) : laplacian g f x = laplacian g k x := by
  unfold laplacian
  rw [LeafProofs.L22Aux.levi_congr_of_eventuallyEq hfk]

theorem laplacian_zero_off_tsupport (g : HermitianField M) (f : M.Carrier → ℝ)
    {x : M.Carrier} (hx : x ∉ tsupport f) : laplacian g f x = 0 := by
  rw [laplacian_congr_local g (notMem_tsupport_iff_eventuallyEq.mp hx)]
  exact laplacian_const g 0 x

theorem scalarGradientPair_congr_local_left (g : HermitianField M)
    {f k : M.Carrier → ℝ} (v : M.Carrier → ℝ) {x : M.Carrier}
    (hfk : f =ᶠ[𝓝 x] k) : scalarGradientPair g f v x = scalarGradientPair g k v x := by
  have hD := (inChart_eventuallyEq hfk).fderiv_eq (𝕜 := ℝ)
  unfold scalarGradientPair chartGradientPair rDeriv
  rw [hD]

/-- Double Green for an arbitrary smooth scalar and a compact cutoff.
The extra compact scalar is constructed internally and removed by locality. -/
theorem integral_laplacian_swap_compact (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {u χ : M.Carrier → ℝ} (hu : SmoothFn u) (hχ : SmoothFn χ)
    (hcχ : HasCompactSupport χ) (o : M.Carrier) {R : ℝ} (hR : 0 < R)
    (hsχ : tsupport χ ⊆ distBall g.form o R) :
    Integrable (fun x => χ x * laplacian g.form u x) μ ∧
      Integrable (fun x => u x * laplacian g.form χ x) μ ∧
      (∫ x, χ x * laplacian g.form u x ∂μ) =
        ∫ x, u x * laplacian g.form χ x ∂μ := by
  obtain ⟨η, hη, hcη, _, hηone, _⟩ := exists_smooth_compact_cutoff g o
    (r := R + 1) (R := R + 2) (by linarith) (by linarith)
  have hnear (x : M.Carrier) (hx : x ∈ tsupport χ) :
      (fun y => η y * u y) =ᶠ[𝓝 x] u := by
    have hr : inducedDistance g.form o x < R + 1 :=
      ((LeafProofs.L12Aux.mem_distBall_iff g o x hR).mp (hsχ hx)).trans (by linarith)
    filter_upwards [(LeafProofs.L12Aux.continuous_distFrom g o).continuousAt.eventually
      (gt_mem_nhds hr)] with y hy
    rw [hηone y hy.le, one_mul]
  have hG₁ := integral_scalar_green g hK μ hμ hu hχ hcχ
  have hG₂ := integral_scalar_green g hK μ hμ hχ (smoothFn_mul hη hu) hcη.mul_right
  have hL : (fun x => (η x * u x) * laplacian g.form χ x) =
      fun x => u x * laplacian g.form χ x := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [(hnear x hx).eq_of_nhds]
    · rw [laplacian_zero_off_tsupport g.form χ hx]
      simp
  have hE : scalarGradientPair g.form (fun x => η x * u x) χ =
      scalarGradientPair g.form χ u := by
    funext x
    rw [scalarGradientPair_symm]
    by_cases hx : x ∈ tsupport χ
    · rw [scalarGradientPair_symm,
        scalarGradientPair_congr_local_left g.form χ (hnear x hx), scalarGradientPair_symm]
    · rw [scalarGradientPair_zero_of_notMem_tsupport g.form χ _ hx,
        scalarGradientPair_zero_of_notMem_tsupport g.form χ _ hx]
  rw [hL, hE] at hG₂
  exact ⟨hG₁.1, hG₂.1, hG₁.2.2.trans hG₂.2.2.symm⟩

end Yau.Proofs.F02Aux
