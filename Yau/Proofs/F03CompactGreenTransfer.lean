import Yau.Proofs.F02Green
import Yau.LeafProofs.L19ScalarEnergy

/-! Moving both derivatives of a truncated potential onto the heat kernel uses only its first gradient. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L18Aux LeafProofs.L19Aux F02Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem integral_laplacian_compact_product_transfer
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v k χ : M.Carrier → ℝ} (hv : SmoothFn v) (hk : SmoothFn k)
    (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ) (o : M.Carrier)
    {R : ℝ} (hR : 0 < R) (hsχ : tsupport χ ⊆ distBall g.form o R) :
    Integrable (fun y => k y*laplacian g.form (fun z => χ z*v z) y) μ ∧
    Integrable (fun y => k y*χ y*laplacian g.form v y) μ ∧
    Integrable (fun y => v y*k y*laplacian g.form χ y) μ ∧
    Integrable (fun y => v y*scalarGradientPair g.form k χ y) μ ∧
    (∫ y,k y*laplacian g.form (fun z => χ z*v z) y ∂μ) =
      (∫ y,k y*χ y*laplacian g.form v y ∂μ)-
      (∫ y,v y*k y*laplacian g.form χ y ∂μ)-
      (∫ y,v y*scalarGradientPair g.form k χ y ∂μ) := by
  have hG₁ := integral_laplacian_swap_compact g hK μ hμ hk
    (smoothFn_mul hχ hv) hcχ.mul_right o hR (tsupport_mul_subset_left.trans hsχ)
  have hG₂ := integral_laplacian_swap_compact g hK μ hμ hv
    (smoothFn_mul hχ hk) hcχ.mul_right o hR (tsupport_mul_subset_left.trans hsχ)
  have hI₁ : Integrable (fun y => v y*χ y*laplacian g.form k y) μ := by
    convert hG₁.1 using 1
    funext y
    ring
  have hI₂ : Integrable (fun y => v y*k y*laplacian g.form χ y) μ :=
    smoothFn_integrable_compact g μ hμ
      (smoothFn_mul (smoothFn_mul hv hk) (smoothFn_laplacian g hχ))
      (laplacian_hasCompactSupport g.form hχ hcχ).mul_left
  have hI₃ : Integrable (fun y => v y*scalarGradientPair g.form k χ y) μ := by
    apply ((hG₂.2.1.sub hI₁).sub hI₂).congr
    apply ae_of_all μ
    intro y
    change v y*laplacian g.form (fun z => χ z*k z) y-
      v y*χ y*laplacian g.form k y-v y*k y*laplacian g.form χ y = _
    rw [laplacian_mul g.form hχ hk]
    change v y*(χ y*laplacian g.form k y+k y*laplacian g.form χ y+
      scalarGradientPair g.form χ k y)-v y*χ y*laplacian g.form k y-
        v y*k y*laplacian g.form χ y = _
    rw [scalarGradientPair_symm g.form χ k y]
    ring
  have hI₀ : Integrable (fun y => k y*χ y*laplacian g.form v y) μ := by
    convert hG₂.1 using 1
    funext y
    ring
  refine ⟨hG₁.2.1,hI₀,hI₂,hI₃,?_⟩
  have hEq₁ : (∫ y,v y*χ y*laplacian g.form k y ∂μ)=
      (∫ y,k y*laplacian g.form (fun z => χ z*v z) y ∂μ) := by
    rw [← hG₁.2.2]
    apply integral_congr_ae
    exact ae_of_all μ (fun y => by ring)
  have hEq₂ : (∫ y,k y*χ y*laplacian g.form v y ∂μ)=
      (∫ y,v y*χ y*laplacian g.form k y ∂μ)+
      (∫ y,v y*k y*laplacian g.form χ y ∂μ)+
      (∫ y,v y*scalarGradientPair g.form k χ y ∂μ) := by
    calc
      _ = ∫ y,(χ y*k y)*laplacian g.form v y ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ (fun y => by ring)
      _ = ∫ y,v y*laplacian g.form (fun z => χ z*k z) y ∂μ := hG₂.2.2
      _ = ∫ y,(v y*χ y*laplacian g.form k y+v y*k y*laplacian g.form χ y)+
          v y*scalarGradientPair g.form k χ y ∂μ := by
        apply integral_congr_ae
        apply ae_of_all μ
        intro y
        change v y*laplacian g.form (fun z => χ z*k z) y = _
        rw [laplacian_mul g.form hχ hk]
        change v y*(χ y*laplacian g.form k y+k y*laplacian g.form χ y+
          scalarGradientPair g.form χ k y) = _
        rw [scalarGradientPair_symm g.form χ k y]
        ring
      _ = _ := by
        have hAdd := integral_add (hI₁.add hI₂) hI₃
        simp only [Pi.add_apply] at hAdd
        rw [hAdd,integral_add hI₁ hI₂]
  linarith

end Yau.Proofs.F03Aux
