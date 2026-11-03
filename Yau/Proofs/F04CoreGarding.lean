import Yau.Proofs.F04FixedVolumeGreen
import Yau.Proofs.F04FlowGradientContinuity
import Yau.Proofs.F04GradientCauchy
import Yau.Proofs.F04CoreEnergyIntegrals

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.Proofs.F03Aux Yau.LeafProofs.L18Aux

variable {n : ℕ}

theorem flow_core_garding_with_gradient_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O K : Set (Pt X)) (hOK : O ⊆ K) {t : ℝ} (ht : 0 ≤ t) (D : ℝ)
    (hD : ∀ x ∈ K, scalarGradientPair (h t) (fun y => ρ y t) (fun y => ρ y t) x ≤ D)
    (f : dirichletCore X.metric μ hμ O) :
    (1 / 2 : ℝ) * ‖dirichletCoreEmbedding X.metric μ hμ O f‖ ^ 2 ≤
      -(∫ x, f.val x * laplacian (h t) f.val x ∂μ) +
        (D / 4 + 1 / 2) * ‖dirichletL2 X.metric μ hμ O
          (dirichletCoreEmbedding X.metric μ hμ O f)‖ ^ 2 := by
  have hg := flow_fixed_volume_green X o h U P ρ hloc μ hμ ht
    f.val.2.1 f.val.2.1 f.val.2.2
  have hg0 := scalarGradientPair_integrable X.metric μ hμ f.val.2.1 f.val.2.1 f.val.2.2
  have hf0 : Integrable (fun x => f.val x * f.val x) μ :=
    smoothFn_integrable_compact X.metric μ hμ (smoothFn_mul f.val.2.1 f.val.2.1) f.val.2.2.mul_right
  have hp (x : Pt X) : scalarGradientPair X.metric.form f.val f.val x ≤
      2 * scalarGradientPair (h t) f.val f.val x +
        2 * (f.val x * scalarGradientPair (h t) (fun y => ρ y t) f.val x) +
        D * (f.val x * f.val x) := by
    by_cases hx : x ∈ K
    · have ha := scalarGradientPair_drift_absorption (h t) (fun y => ρ y t) f.val x (f.val x) D (hD x hx)
      have hlo := flow_scalarGradientPair_lower_bound X o h U P ρ hloc ht f.val x
      nlinarith [neg_abs_le (f.val x * scalarGradientPair (h t) (fun y => ρ y t) f.val x)]
    · have hxf : x ∉ tsupport (f.val : Pt X → ℝ) := fun hs => hx (hOK (f.property hs))
      rw [scalarGradientPair_zero_of_notMem_tsupport X.metric.form f.val f.val hxf,
        scalarGradientPair_zero_of_notMem_tsupport (h t) f.val f.val hxf,
        image_eq_zero_of_notMem_tsupport hxf]
      ring_nf
      exact le_rfl
  have hi := integral_mono hg0 (((hg.2.1.const_mul 2).add (hg.2.2.1.const_mul 2)).add (hf0.const_mul D)) hp
  have ho := integral_add ((hg.2.1.const_mul 2).add (hg.2.2.1.const_mul 2)) (hf0.const_mul D)
  have hin := integral_add (hg.2.1.const_mul 2) (hg.2.2.1.const_mul 2)
  dsimp only [Pi.add_apply] at hi ho hin
  rw [ho, hin] at hi
  simp only [integral_const_mul] at hi
  rw [dirichletCoreEmbedding_norm_integral, dirichletCoreEmbedding_pivot_norm_integral]
  nlinarith [hg.2.2.2]

/-- A single actual coefficient bound yields the same positive coercivity
 constant and one pivot shift for every original smooth core element. -/
theorem flow_core_garding
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O K : Set (Pt X)) (hK : IsCompact K) (hOK : O ⊆ K) {S : ℝ} (hS : 0 < S) :
    ∃ shift : ℝ, 0 ≤ shift ∧ ∀ t ∈ Icc 0 S,
      ∀ f : dirichletCore X.metric μ hμ O,
      (1 / 2 : ℝ) * ‖dirichletCoreEmbedding X.metric μ hμ O f‖ ^ 2 ≤
        -(∫ x, f.val x * laplacian (h t) f.val x ∂μ) +
          shift * ‖dirichletL2 X.metric μ hμ O
            (dirichletCoreEmbedding X.metric μ hμ O f)‖ ^ 2 := by
  obtain ⟨D, hD, hDb⟩ := flow_rho_gradient_bound X o h U P ρ hloc hS K hK
  refine ⟨D / 4 + 1 / 2, by positivity, ?_⟩
  intro t ht f
  exact flow_core_garding_with_gradient_bound X o h U P ρ hloc μ hμ O K hOK ht.1 D
    (fun x hx => hDb x hx t ht) f

end Yau.F04Proof
