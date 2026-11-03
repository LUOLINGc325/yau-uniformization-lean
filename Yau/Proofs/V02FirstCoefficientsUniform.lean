import Yau.Proofs.V02DampedCoronaUniform
import Yau.Proofs.V02CramerCoefficientBounds
import Yau.Proofs.V02FiniteTraceControl

/-! Actual holomorphic coefficients in the original global spanning fields
are uniformly bounded before the whole sequence of discs, frames and columns. -/

open scoped Topology ContDiff Manifold Matrix

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {n q b : ℕ} {X : KahlerManifold n}

theorem exists_uniform_spanningFirstCoefficients
    {d : VariationData X q} (hd : VariationSetup d) (j : ℕ)
    {Z : Fin b → CotangentPoint X.manifold → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤)
    {K : Set (CotangentPoint X.manifold)} (hK : CotangentCompact K)
    (L : ℝ) (hL : 0 ≤ L) (E₀ D₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ P C S : ℝ, 0 < P ∧ 0 ≤ C ∧ 0 ≤ S ∧
      ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
        (l : ℂ → CotangentIndex n → ℂ),
      AdmissibleVariationDisc d j F → (variationEnergy d j F).toReal ≤ E₀ →
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, F.f z ∈ K) →
      NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      boundaryDSq (fun θ => l (circlePoint θ)) ≤ ENNReal.ofReal (D₀ ^ 2) →
      ContDiffOn ℂ ∞ (spanningDamping P d.G Z F.f) (Metric.closedBall (0 : ℂ) 1) ∧
      (spanningDamping P d.G Z F.f 0).im = 0 ∧
      0 < (spanningDamping P d.G Z F.f 0).re ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖spanningDamping P d.G Z F.f z‖ ≤ 1) ∧
      boundaryDSq (fun θ (_ : Unit) => spanningDamping P d.G Z F.f (circlePoint θ)) ≤ 1 ∧
      -Real.log (spanningDamping P d.G Z F.f 0).re ≤ η ∧
      circleAverage (fun θ => 1 - ‖spanningDamping P d.G Z F.f (circlePoint θ)‖ ^ 2) ≤ η ∧
      ∀ i : Fin b,
        ContDiffOn ℂ ∞ (fun ζ =>
          spanningFirstCoefficients d.G Z F.f E l (spanningDamping P d.G Z F.f) ζ i)
          (Metric.closedBall (0 : ℂ) 1) ∧
        (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
          ‖spanningFirstCoefficients d.G Z F.f E l (spanningDamping P d.G Z F.f) ζ i‖ ≤ C) ∧
        boundaryDSq (fun θ (_ : Unit) =>
          spanningFirstCoefficients d.G Z F.f E l (spanningDamping P d.G Z F.f)
            (circlePoint θ) i) ≤ ENNReal.ofReal S := by
  classical
  let ι := SpanningMinorIndex n q b
  let κ := ι × Fin q
  obtain ⟨P, Mγ, Dγ, hP, hMγ, hDγ, hγall⟩ :=
    exists_uniform_dampedSpanningCorona hd j hZ hspan hK E₀ hη
  obtain ⟨Dk, Mk, hDk, hMk, hkall⟩ :=
    spanningCramerCoefficient_uniform_boundary_control hd j E₀ hZ
  obtain ⟨DY, hDY, hYall⟩ := boundaryColumnField_uniform_control_of_energy_bound hd j L hL E₀ D₀
  let Mγk := Mγ * Mk
  let Dγk := 2 * Mk ^ 2 * Dγ + 2 * Mγ ^ 2 * Dk
  let MT := Mγk * L
  let DT := 2 * L ^ 2 * Dγk + 2 * Mγk ^ 2 * DY
  have hMγk : 0 ≤ Mγk := mul_nonneg hMγ hMk
  have hDγk : 0 ≤ Dγk := by dsimp [Dγk]; positivity
  have hMT : 0 ≤ MT := mul_nonneg hMγk hL
  have hDT : 0 ≤ DT := by dsimp [DT]; positivity
  refine ⟨P, (Fintype.card κ : ℝ) * MT, (Fintype.card κ : ℝ) ^ 2 * DT,
    hP, by positivity, by positivity, fun F E l hF hE hfK hframe hl hlL hlD => ?_⟩
  obtain ⟨hα, hphase, hpos, hsup, hDα, hcenter, hloss, hγ⟩ := hγall F hF hE hfK
  obtain ⟨hYnorm, hYD⟩ := hYall F E l hF hE hframe hl hlL hlD
  let α := spanningDamping P d.G Z F.f
  let γ := dampedSpanningCorona P d.G Z F.f
  have hγc (k : ι) : Continuous (fun θ => γ k (circlePoint θ)) :=
    (hγ k).1.continuousOn.comp_continuous
      V03Proof.circlePoint_contDiff.continuous V03Proof.circlePoint_mem_closedBall
  have hkclosed (k : ι) (i : Fin b) (a : Fin q) :
      ContDiffOn ℂ ∞ (fun ζ => spanningCramerCoefficient d.G Z k i a (F.f ζ))
        (Metric.closedBall (0 : ℂ) 1) :=
    cotangentDisc_comp_complex_smooth (F := spanningCramerCoefficient d.G Z k i a) hF.1
      (spanningCramerCoefficient_chart_contDiffOn hd.2.2.2.2.1.1 hZ k i a)
  have hkc (k : ι) (i : Fin b) (a : Fin q) :
      Continuous (fun θ => spanningCramerCoefficient d.G Z k i a (F.f (circlePoint θ))) :=
    (hkclosed k i a).continuousOn.comp_continuous
      V03Proof.circlePoint_contDiff.continuous V03Proof.circlePoint_mem_closedBall
  have hYc (a : Fin q) := V03Proof.boundaryColumnField_continuous hd F E hframe l hl a
  have hYp (a : Fin q) := V03Proof.boundaryColumnField_periodic d F E l a
  have hYDscalar (a : Fin q) : boundaryDSq
      (fun θ (_ : Unit) => V03Proof.boundaryColumnField d F E l θ a) ≤ ENNReal.ofReal DY := by
    rw [V03Proof.boundaryDSq_eq_sum_singleton] at hYD
    exact (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ a)).trans hYD
  refine ⟨hα, hphase, hpos, hsup, hDα, hcenter, hloss, fun i => ?_⟩
  let T : κ → ℝ → ℂ := fun p θ =>
    γ p.1 (circlePoint θ) * spanningCramerCoefficient d.G Z p.1 i p.2 (F.f (circlePoint θ)) *
      V03Proof.boundaryColumnField d F E l θ p.2
  have hTc (p : κ) : Continuous (T p) :=
    ((hγc p.1).mul (hkc p.1 i p.2)).mul (hYc p.2)
  have hTp (p : κ) : Function.Periodic (T p) (2 * Real.pi) :=
    V03Proof.circleTrace_periodic (fun ζ => γ p.1 ζ *
      spanningCramerCoefficient d.G Z p.1 i p.2 (F.f ζ) * (ambientFrame d.G F.f E ζ *ᵥ l ζ) p.2)
  have hTnorm (p : κ) (θ : ℝ) : ‖T p θ‖ ≤ MT := by
    have hgn := (hγ p.1).2.1 _ (V03Proof.circlePoint_mem_closedBall θ)
    have hln := (hkall F hF hE p.1 i p.2).1 θ
    have hpn := mul_le_mul hgn hln (norm_nonneg _) hMγ
    have hh := mul_le_mul hpn (hYnorm θ p.2) (norm_nonneg _) hMγk
    simpa only [T, MT, Mγk, norm_mul] using hh
  have hTD (p : κ) : boundaryDSq (fun θ (_ : Unit) => T p θ) ≤ ENNReal.ofReal DT := by
    have hgn := fun θ => (hγ p.1).2.1 _ (V03Proof.circlePoint_mem_closedBall θ)
    have hln := (hkall F hF hE p.1 i p.2).1
    have hgd := (hγ p.1).2.2
    have hld := (hkall F hF hE p.1 i p.2).2
    have hglD := finiteTrace_product_boundaryDSq_le (hγc p.1) (hkc p.1 i p.2)
      (V03Proof.circleTrace_periodic (γ p.1))
      (V03Proof.circleTrace_periodic (fun ζ => spanningCramerCoefficient d.G Z p.1 i p.2 (F.f ζ)))
      hMγ hMk hDγ hDk hgn hln hgd hld
    have hglN (θ : ℝ) : ‖γ p.1 (circlePoint θ) *
        spanningCramerCoefficient d.G Z p.1 i p.2 (F.f (circlePoint θ))‖ ≤ Mγk := by
      rw [norm_mul]
      exact mul_le_mul (hgn θ) (hln θ) (norm_nonneg _) hMγ
    exact finiteTrace_product_boundaryDSq_le ((hγc p.1).mul (hkc p.1 i p.2)) (hYc p.2)
      (V03Proof.circleTrace_periodic (fun ζ => γ p.1 ζ *
        spanningCramerCoefficient d.G Z p.1 i p.2 (F.f ζ))) (hYp p.2)
      hMγk hL hDγk hDY hglN (fun θ => hYnorm θ p.2) hglD (hYDscalar p.2)
  have heq (θ : ℝ) : spanningFirstCoefficients d.G Z F.f E l α (circlePoint θ) i =
      ∑ p : κ, T p θ :=
    spanningFirstCoefficients_as_sum d.G Z F.f E l α (circlePoint θ) i
  have hc := spanningFirstCoefficients_contDiffOn hd.2.2.2.2.1 hZ hspan hframe.1 hl hα i
  refine ⟨hc, ?_, ?_⟩
  · apply V03Proof.norm_le_of_circle_bound hc
    intro θ
    rw [heq]
    exact finiteTrace_sum_norm_le _ hTnorm θ
  have hh := finiteTrace_sum_boundaryDSq_le hTc hTp hDT hTD
  simpa only [← heq] using hh

end Yau.Blueprint.V02Proof
