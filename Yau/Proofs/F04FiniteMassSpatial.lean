import Yau.Proofs.F04MassTimeSlices
import Yau.Proofs.F04MassScalarError

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

theorem finite_mass_spatial_bound {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (μg μt : Measure (Pt X)) (hμg : IsRiemannianVolume X.metric.form μg) {t : ℝ}
    (hμt : IsRiemannianVolume (h t) μt) (ht : 0 ≤ t)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {R : ℝ} (hR : 0 < R) {χ z : Pt X → ℝ} (hχ : SmoothFn χ) (hz : SmoothFn z)
    (hz0 : ∀ x, 0 ≤ z x) (C : ℝ)
    (hLevi : ∀ x, HermLE (levi χ x) (((C * χ x : ℝ) : ℂ) • gMat (h t) x))
    (hErr : Integrable (fun x => |z x * massScalarError (h t) u χ R x * density ρ x t|) μg) :
    (∫ x, (χ x * massCutoff u R x * laplacian (h t) z x) * density ρ x t ∂μg) ≤
      ((n : ℝ) * C) * (∫ x, massCutoff u R x * (z x * χ x * density ρ x t) ∂μg) +
        ∫ x, |z x * massScalarError (h t) u χ R x * density ρ x t| ∂μg := by
  have hp := massCutoff_smooth hu.1 R
  have hc := massCutoff_compact X o u hu hR
  have hd : SmoothFn (fun x => density ρ x t) := by
    intro c
    exact ((hloc.2.2.2.1 c).neg.exp).comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ hz => ⟨hz, ht⟩)
  have hmetric := metricFamilySmooth_slice h (Ici 0) hloc.1.2.1 t ht
  let ψ : Pt X → ℝ := fun x => χ x * massCutoff u R x
  have hψ : SmoothFn ψ := smoothFn_mul hχ hp
  have hcψ : HasCompactSupport ψ := hc.mul_left
  have hlap : SmoothFn (laplacian (h t) ψ) := Adjoint.smoothFn_laplacian (h t) hmetric hψ
  have hI : Integrable (fun x => massCutoff u R x * (z x * χ x * density ρ x t)) μg :=
    initial_volume_integrable_of_continuous_compact X.metric μg hμg
      ((continuous_of_smoothFn hp).mul
        (((continuous_of_smoothFn hz).mul (continuous_of_smoothFn hχ)).mul (continuous_of_smoothFn hd)))
      hc.mul_right
  have hJ : Integrable (fun x => (z x * laplacian (h t) ψ x) * density ρ x t) μg :=
    initial_volume_integrable_of_continuous_compact X.metric μg hμg
      (((continuous_of_smoothFn hz).mul (continuous_of_smoothFn hlap)).mul (continuous_of_smoothFn hd))
      (laplacian_compact_support (h t) hcψ).mul_left.mul_right
  have hpoint (x : Pt X) : (z x * laplacian (h t) ψ x) * density ρ x t ≤
      ((n : ℝ) * C) * (massCutoff u R x * (z x * χ x * density ρ x t)) +
        |z x * massScalarError (h t) u χ R x * density ρ x t| := by
    have hH := LeafProofs.gMat_posDef (h t) x
    have hχlap := Proofs.F02Aux.traceWith_mono (gMat (h t) x) _ _ hH.posSemidef (hLevi x)
    rw [Proofs.F02Aux.traceWith_real_smul, Proofs.F02Aux.traceWith_self _ hH] at hχlap
    change laplacian (h t) χ x ≤ (C * χ x) * (n : ℝ) at hχlap
    have hm := mul_le_mul_of_nonneg_left hχlap
      (mul_nonneg (mul_nonneg (hz0 x) (massCutoff_range u R x).1) (density_pos ρ x t).le)
    calc
      _ = (z x * massCutoff u R x * density ρ x t) * laplacian (h t) χ x +
          z x * massScalarError (h t) u χ R x * density ρ x t := by
        dsimp only [massScalarError, ψ]
        ring
      _ ≤ (z x * massCutoff u R x * density ρ x t) * ((C * χ x) * (n : ℝ)) +
          |z x * massScalarError (h t) u χ R x * density ρ x t| :=
        add_le_add hm (le_abs_self _)
      _ = _ := by ring
  have hbound := integral_mono hJ ((hI.const_mul ((n : ℝ) * C)).add hErr) hpoint
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hI.const_mul ((n : ℝ) * C)) hErr, integral_const_mul] at hbound
  have hgreen := flow_density_compact_adjoint X o h U P ρ hloc ht μg μt hμg hμt z ψ hz hψ hcψ
  change (∫ x, (ψ x * laplacian (h t) z x) * density ρ x t ∂μg) ≤ _
  rw [hgreen]
  exact hbound

end Yau.F04Proof
