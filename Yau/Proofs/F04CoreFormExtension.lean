import Yau.Proofs.F04CoreBilinearProfile
import Yau.Proofs.F04CoreFormBounds
import Yau.Proofs.F04BilinearQuadraticBound
import Yau.Proofs.F04BilinearExtensionBound

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000

namespace Yau.F04Proof

open Yau.Blueprint Yau.Proofs.F03Aux

variable {n : ℕ}

/-- Extend the actual fixed-volume form in both arguments into continuous
 physical time profiles on the same completed supported energy space. -/
theorem flow_core_form_extension
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O K : Set (Pt X)) (hK : IsCompact K) (hOK : O ⊆ K) {S : ℝ} (hS : 0 < S) :
    ∃ C : ℝ, ∃ B : DirichletEnergy X.metric μ hμ O →L[ℝ]
        DirichletEnergy X.metric μ hμ O →L[ℝ] C(Icc (0 : ℝ) S, ℝ),
      0 < C ∧ (∀ u v, ‖B u v‖ ≤ C * ‖u‖ * ‖v‖) ∧ ∀ f v : dirichletCore X.metric μ hμ O, ∀ t : Icc (0 : ℝ) S,
        B (dirichletCoreEmbedding X.metric μ hμ O f) (dirichletCoreEmbedding X.metric μ hμ O v) t =
          -(∫ x, v.val x * laplacian (h t) f.val x ∂μ) := by
  have hh : MetricFamilySmooth h (Icc 0 S) := fun c i j =>
    (hloc.1.2.1 c i j).mono (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  let b := intrinsicCoreBilinearProfile X.metric μ hμ h hh O
  let e := dirichletCoreEmbedding X.metric μ hμ O
  obtain ⟨A, hA, hAb⟩ := flow_core_quadratic_bound X o h U P ρ hloc μ hμ O K hK hOK hS
  have hqb (f v : dirichletCore X.metric μ hμ O) : ‖b f v‖ ≤ A * (‖f‖ ^ 2 + ‖v‖ ^ 2) := by
    apply (ContinuousMap.norm_le _ (mul_nonneg hA.le (add_nonneg (sq_nonneg _) (sq_nonneg _)))).mpr
    intro t
    change |-(∫ x, v.val x * laplacian (h t) f.val x ∂μ)| ≤ A * (‖f‖ ^ 2 + ‖v‖ ^ 2)
    simpa only [dirichletCoreEmbedding_norm, Submodule.norm_coe] using hAb t t.property f v
  have hpb (f v : dirichletCore X.metric μ hμ O) : ‖b f v‖ ≤ (2 * A) * ‖e f‖ * ‖e v‖ := by
    dsimp only [e]
    rw [dirichletCoreEmbedding_norm, dirichletCoreEmbedding_norm]
    simpa only [← Submodule.norm_coe] using bilinear_product_bound_of_quadratic_bound b A hqb f v
  obtain ⟨B, hbound, hBe⟩ := bounded_bilinear_extension_pointwise e
    (dirichletCoreEmbedding_denseRange X.metric μ hμ O) b (by positivity : 0 ≤ 2 * A) hpb
  refine ⟨2 * A, B, by positivity, hbound, ?_⟩
  intro f v t
  exact congrArg (fun φ : C(Icc (0 : ℝ) S, ℝ) => φ t) (hBe f v)

end Yau.F04Proof
