import Yau.Proofs.V02Sigma
import Yau.Proofs.V03DiscSmooth

/-! Actual chart-smooth coefficients compose with any original cotangent
disc. No fixed chart or continuation across the circle is imposed. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {n q b : ℕ} {M : ComplexManifold n}

theorem cotangentDisc_comp_complex_smooth {f : ℂ → CotangentPoint M}
    (hf : CotangentDisc f) {F : CotangentPoint M → ℂ}
    (hF : ∀ x, ContDiffOn ℂ ∞ (fun z => F (cotangentChartInv x z)) (cotangentTarget x)) :
    ContDiffOn ℂ ∞ (fun ζ => F (f ζ)) (Metric.closedBall (0 : ℂ) 1) := by
  intro ζ hζ
  obtain ⟨V, hV, hζV, hsource, hcoord⟩ := (V03Proof.cotangentDisc_holomorphicOn hf).2 ζ hζ
  have hself : f ζ ∈ cotangentSource (f ζ).1 := mem_extChartAt_source _
  have htarget := V03Proof.cotangentChart_mapsTo (f ζ).1 hself
  have hFA := (hF (f ζ).1).contDiffAt
    (((isOpen_extChartAt_target (I := ComplexModel n) (f ζ).1).prod isOpen_univ).mem_nhds htarget)
  have hmodel := hFA.comp_contDiffWithinAt ζ (hcoord ζ ⟨hζ, hζV⟩)
  apply (contDiffWithinAt_inter (hV.mem_nhds hζV)).mp
  apply hmodel.congr_of_eventuallyEq_of_mem ?_ ⟨hζ, hζV⟩
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact (congrArg F (V03Proof.cotangentChart_left_inv (f ζ).1 (hsource η hη))).symm

theorem cotangentDisc_comp_real_smooth {f : ℂ → CotangentPoint M}
    (hf : CotangentDisc f) {F : CotangentPoint M → ℂ}
    (hF : ∀ x, ContDiffOn ℝ ∞ (fun z => F (cotangentChartInv x z)) (cotangentTarget x)) :
    ContDiffOn ℝ ∞ (fun ζ => F (f ζ)) (Metric.closedBall (0 : ℂ) 1) := by
  intro ζ hζ
  obtain ⟨V, hV, hζV, hsource, hcoord⟩ := (V03Proof.cotangentDisc_holomorphicOn hf).2 ζ hζ
  have hself : f ζ ∈ cotangentSource (f ζ).1 := mem_extChartAt_source _
  have htarget := V03Proof.cotangentChart_mapsTo (f ζ).1 hself
  have hFA := (hF (f ζ).1).contDiffAt
    (((isOpen_extChartAt_target (I := ComplexModel n) (f ζ).1).prod isOpen_univ).mem_nhds htarget)
  have hmodel := hFA.comp_contDiffWithinAt ζ ((hcoord ζ ⟨hζ, hζV⟩).restrict_scalars ℝ)
  apply (contDiffWithinAt_inter (hV.mem_nhds hζV)).mp
  apply hmodel.congr_of_eventuallyEq_of_mem ?_ ⟨hζ, hζV⟩
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact (congrArg F (V03Proof.cotangentChart_left_inv (f ζ).1 (hsource η hη))).symm

theorem spanningMinor_disc_contDiffOn
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) (k : SpanningMinorIndex n q b) :
    ContDiffOn ℂ ∞ (fun ζ => spanningMinor G Z k (f ζ)) (Metric.closedBall (0 : ℂ) 1) :=
  cotangentDisc_comp_complex_smooth hf (fun x => spanning_minor_chart_contDiffOn hG hZ x k.1 k.2)

theorem spanningSigma_disc_contDiffOn
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) (k : SpanningMinorIndex n q b) :
    ContDiffOn ℝ ∞ (fun ζ => spanningSigma G Z k (f ζ)) (Metric.closedBall (0 : ℂ) 1) :=
  cotangentDisc_comp_real_smooth hf (fun x => spanningSigma_chart_contDiffOn hG hZ hspan x k)

end Yau.Blueprint.V02Proof
