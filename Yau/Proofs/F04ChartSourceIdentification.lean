import Yau.Proofs.F04SupportedChartSource
import Yau.Proofs.F04ProductSliceEquality
import Yau.Blueprint.ParabolicSpaces

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux Yau.HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}

/-- The genuinely constructed joint source is the original physical
 forcing on a chart inside the actual supported domain. Actual source
 classes are identified first in space and then in product measure. -/
theorem chart_joint_source_eq_physical
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (c : M.Carrier)
    {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω) {S : ℝ}
    (v : M.Carrier → ℝ → ℝ) (hv : ∀ t, ScalarL2 (μ.restrict Ω) (fun x => v x t))
    (f : ℝ → Lp ℝ 2 (μ.restrict Ω))
    (hf : ∀ᵐ t ∂volume.restrict (Ioo 0 S), f t = scalarToLp (hv t))
    {F : Point n → ℝ} (hF : MemLp F 2 (productVolume O (Ioo 0 S)))
    (hV : MemLp (fun p : Point n => v (chartInv c p.1) p.2) 2 (productVolume O (Ioo 0 S)))
    (hSlices : ∀ᵐ t ∂volume.restrict (Ioo 0 S),
      (fun z => F (z, t)) =ᵐ[volume.restrict O]
        scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ (f t))) :
    F =ᵐ[productVolume O (Ioo 0 S)] (fun p => v (chartInv c p.1) p.2) := by
  apply product_memLp_ae_eq_of_ae_time_slices hF hV
  filter_upwards [hSlices, hf] with t ht hft
  rw [hft] at ht
  exact ht.trans (supportedL2_physical_chart_source g μ hμ Ω hΩ c hO hOC hOt hMap (hv t))

theorem weakEquation_source_congr_ae
    {n : ℕ} {O : Set (Space n)} {I : Set ℝ}
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {f g u : Point n → ℝ}
    {G : Point n → RIdx n → ℝ} (hEq : WeakEquation O I a b f u G)
    (hfg : f =ᵐ[productVolume O I] g) : WeakEquation O I a b g u G := by
  intro φ hφ
  apply (hEq φ hφ).trans
  apply integral_congr_ae
  filter_upwards [hfg] with p hp
  rw [hp]

end Yau.F04Proof
