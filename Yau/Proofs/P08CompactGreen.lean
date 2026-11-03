import Yau.Proofs.P06WeakDDbarCurrentGreen
import Yau.LeafProofs.L19ScalarEnergy

/-! Moving the scalar Laplacian onto a compact test without any global
integrability hypothesis on the other smooth scalar. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Matrix
namespace Yau.NodeProofs.P08Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- Locality in the second scalar of the actual metric gradient pairing. -/
theorem scalarGradientPair_congr_near_right (g : HermitianField M)
    (f u v : M.Carrier → ℝ) (x : M.Carrier) (heq : u =ᶠ[𝓝 x] v) :
    L18Aux.scalarGradientPair g f u x = L18Aux.scalarGradientPair g f v x := by
  unfold L18Aux.scalarGradientPair L18Aux.chartGradientPair rDeriv
  rw [(L18Aux.inChart_eventuallyEq heq).fderiv_eq (𝕜 := ℝ)]

/-- The compact Green swap retains both integrability claims. -/
theorem integral_laplacian_compact_swap (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {w χ : M.Carrier → ℝ} (hw : SmoothFn w) (hχ : SmoothFn χ)
    (hcχ : HasCompactSupport χ) :
    Integrable (fun x => χ x * laplacian g.form w x) μ ∧
      Integrable (fun x => w x * laplacian g.form χ x) μ ∧
      (∫ x, χ x * laplacian g.form w x ∂μ) =
        ∫ x, w x * laplacian g.form χ x ∂μ := by
  obtain ⟨η, hη, hcη, hηone⟩ :=
    P06Aux.WeakCurrent.exists_compact_smooth_one_near g hcχ
  let v : M.Carrier → ℝ := fun x => η x * w x
  have hv : SmoothFn v := L18Aux.smoothFn_mul hη hw
  have hcv : HasCompactSupport v := hcη.mul_right
  have hvnear (x : M.Carrier) (hx : x ∈ tsupport χ) : v =ᶠ[𝓝 x] w := by
    filter_upwards [hηone x hx] with y hy
    simp only [v, hy, one_mul]
  have hprod : (fun x => v x * laplacian g.form χ x) =
      (fun x => w x * laplacian g.form χ x) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [(hvnear x hx).self_of_nhds]
    · rw [L19Aux.laplacian_zero_of_notMem_tsupport g.form hχ hx, mul_zero, mul_zero]
  have hpair : L18Aux.scalarGradientPair g.form v χ =
      L18Aux.scalarGradientPair g.form χ w := by
    funext x
    rw [L18Aux.scalarGradientPair_symm g.form v χ x]
    by_cases hx : x ∈ tsupport χ
    · exact scalarGradientPair_congr_near_right g.form χ v w x (hvnear x hx)
    · rw [L18Aux.scalarGradientPair_zero_of_notMem_tsupport g.form χ v hx,
        L18Aux.scalarGradientPair_zero_of_notMem_tsupport g.form χ w hx]
  have h₁ := L18Aux.integral_scalar_green g hK μ hμ hw hχ hcχ
  have h₂ := L18Aux.integral_scalar_green g hK μ hμ hχ hv hcv
  rw [hprod, hpair] at h₂
  exact ⟨h₁.1, h₂.1, h₁.2.2.trans h₂.2.2.symm⟩

end Yau.NodeProofs.P08Aux
