import Yau.Proofs.F04ScalarGradientProducts
import Yau.Proofs.F04FlowVolumeProducer
import Yau.Proofs.F04DensityAdjoint

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

variable {n : ℕ}

/-- The genuine fixed initial-volume Green form contains exactly the density
 drift. The evolving Hermitian metric is not assumed complete. -/
theorem flow_fixed_volume_green
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {t : ℝ} (ht : 0 ≤ t) {u v : Pt X → ℝ}
    (hu : SmoothFn u) (hv : SmoothFn v) (hcv : HasCompactSupport v) :
    Integrable (fun x => v x * laplacian (h t) u x) μ ∧
      Integrable (scalarGradientPair (h t) v u) μ ∧
      Integrable (fun x => v x * scalarGradientPair (h t) (fun y => ρ y t) u x) μ ∧
      -(∫ x, v x * laplacian (h t) u x ∂μ) =
        (1 / 2 : ℝ) * ((∫ x, scalarGradientPair (h t) v u x ∂μ) +
          ∫ x, v x * scalarGradientPair (h t) (fun y => ρ y t) u x ∂μ) := by
  let := riemannianVolume_locallyFinite X.metric μ hμ
  have hh := metricFamilySmooth_slice h (Ici 0) hloc.1.2.1 t ht
  have hρ : SmoothFn (fun x => ρ x t) := fun c =>
    (hloc.2.2.2.1 c).comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ hz => ⟨hz, ht⟩)
  have hleft : Integrable (fun x => v x * laplacian (h t) u x) μ :=
    (continuous_of_smoothFn (smoothFn_mul hv (Adjoint.smoothFn_laplacian (h t) hh hu))).integrable_of_hasCompactSupport hcv.mul_right
  have hprincipal : Integrable (scalarGradientPair (h t) v u) μ :=
    (continuous_of_smoothFn (Adjoint.smoothFn_scalarGradientPair (h t) hh hv hu)).integrable_of_hasCompactSupport
      (scalarGradientPair_hasCompactSupport (h t) v u hcv)
  have hdrift : Integrable (fun x => v x * scalarGradientPair (h t) (fun y => ρ y t) u x) μ :=
    (continuous_of_smoothFn (smoothFn_mul hv
      (Adjoint.smoothFn_scalarGradientPair (h t) hh hρ hu))).integrable_of_hasCompactSupport hcv.mul_right
  let μt := μ.withDensity (fun x => ENNReal.ofReal (density ρ x t))
  have hμt : IsRiemannianVolume (h t) μt := flow_reference_volume X o h U P ρ hloc μ hμ t ht
  let ψ := fun x => Real.exp (ρ x t) * v x
  have hψ : SmoothFn ψ := smoothFn_mul (fun c => (hρ c).exp) hv
  have hcψ : HasCompactSupport ψ := hcv.mul_left
  have hg := (Adjoint.integral_scalar_green (h t) hh (hloc.1.2.2.1 t ht) μt hμt hu hψ hcψ).2.2
  have hc (x : Pt X) : density ρ x t * Real.exp (ρ x t) = 1 := by
    change Real.exp (-ρ x t) * Real.exp (ρ x t) = 1
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hli : (∫ x, ψ x * laplacian (h t) u x ∂μt) =
      ∫ x, v x * laplacian (h t) u x ∂μ := by
    rw [flow_density_integral X o h U P ρ hloc ht μ μt hμ hμt]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only [ψ]
    rw [← mul_assoc, ← mul_assoc, hc, one_mul]
  have hri : (∫ x, scalarGradientPair (h t) ψ u x ∂μt) =
      (∫ x, scalarGradientPair (h t) v u x ∂μ) +
        ∫ x, v x * scalarGradientPair (h t) (fun y => ρ y t) u x ∂μ := by
    rw [flow_density_integral X o h U P ρ hloc ht μ μt hμ hμt,
      ← integral_add hprincipal hdrift]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => scalarGradientPair_exponential_density (h t) hρ hv u x)
  rw [hli, hri] at hg
  exact ⟨hleft, hprincipal, hdrift, by linarith only [hg]⟩

end Yau.F04Proof
