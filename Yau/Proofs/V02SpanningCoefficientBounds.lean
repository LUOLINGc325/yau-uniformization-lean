import Yau.Proofs.V02Sigma
import Yau.Proofs.V03FiniteCoefficientBoundaryControl

/-! The actual minors and normalized conjugate minors have common boundary
bounds before every original admissible disc with bounded full energy. -/

open scoped Topology ContDiff Manifold Matrix

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

theorem finiteCoefficients_boundary_control_of_energy_bound
    {n q : ℕ} {X : KahlerManifold n} {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) (E₀ : ℝ)
    {ι : Type*} [Fintype ι] {B : ι → CotangentPoint X.manifold → ℂ}
    (hB : ∀ k x, ContDiffOn ℝ ∞ (fun z => B k (cotangentChartInv x z)) (cotangentTarget x)) :
    ∃ D M : ℝ, 0 ≤ D ∧ 0 ≤ M ∧ ∀ F : VariationDisc X,
      AdmissibleVariationDisc d j F → (variationEnergy d j F).toReal ≤ E₀ → ∀ k,
      (∀ θ, ‖B k (F.f (circlePoint θ))‖ ≤ M) ∧
      boundaryDSq (fun θ (_ : Unit) => B k (F.f (circlePoint θ))) ≤ ENNReal.ofReal D := by
  obtain ⟨C, M, hC, hM, hbound⟩ := V03Proof.finiteCoefficients_uniform_boundary_control hd j hB
  refine ⟨C * max E₀ 0, M, mul_nonneg hC (le_max_right _ _), hM,
    fun F hF hE k => ⟨(hbound F hF k).1, ?_⟩⟩
  have hEn : variationEnergy d j F ≤ ENNReal.ofReal (max E₀ 0) := by
    rw [← ENNReal.ofReal_toReal hF.2.2.2.2.2.2.2.2]
    exact ENNReal.ofReal_le_ofReal (hE.trans (le_max_left _ _))
  rw [ENNReal.ofReal_mul hC]
  exact (hbound F hF k).2.trans (mul_le_mul_right hEn (ENNReal.ofReal C))

theorem spanningMinorSigma_uniform_boundary_control
    {n q b : ℕ} {X : KahlerManifold n} {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ)
    {Z : Fin b → CotangentPoint X.manifold → CotangentIndex n → ℂ}
    (hZ : ∀ k x i, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z k (cotangentChartInv x z)) i) (cotangentTarget x))
    (hspan : ∀ y, Submodule.span ℂ (Set.range (fun k => Z k y)) = ⊤) (E₀ : ℝ) :
    ∃ M D : ℝ, 0 ≤ M ∧ 0 ≤ D ∧ ∀ F : VariationDisc X,
      AdmissibleVariationDisc d j F → (variationEnergy d j F).toReal ≤ E₀ →
      ∀ k : SpanningMinorIndex n q b,
        (∀ θ, ‖spanningMinor d.G Z k (F.f (circlePoint θ))‖ ≤ M) ∧
        (∀ θ, ‖spanningSigma d.G Z k (F.f (circlePoint θ))‖ ≤ M) ∧
        boundaryDSq (fun θ (_ : Unit) => spanningMinor d.G Z k (F.f (circlePoint θ))) ≤
          ENNReal.ofReal D ∧
        boundaryDSq (fun θ (_ : Unit) => spanningSigma d.G Z k (F.f (circlePoint θ))) ≤
          ENNReal.ofReal D := by
  let ι := SpanningMinorIndex n q b
  let B : ι ⊕ ι → CotangentPoint X.manifold → ℂ :=
    Sum.elim (spanningMinor d.G Z) (spanningSigma d.G Z)
  have hB (k : ι ⊕ ι) (x : Pt X) :
      ContDiffOn ℝ ∞ (fun z => B k (cotangentChartInv x z)) (cotangentTarget x) := by
    cases k with
    | inl k => exact (spanning_minor_chart_contDiffOn hd.2.2.2.2.1.1 hZ x k.1 k.2).restrict_scalars ℝ
    | inr k => exact spanningSigma_chart_contDiffOn hd.2.2.2.2.1 hZ hspan x k
  obtain ⟨D, M, hD, hM, hbound⟩ := finiteCoefficients_boundary_control_of_energy_bound hd j E₀ hB
  exact ⟨M, D, hM, hD, fun F hF hE k =>
    ⟨(hbound F hF hE (.inl k)).1, (hbound F hF hE (.inr k)).1,
      (hbound F hF hE (.inl k)).2, (hbound F hF hE (.inr k)).2⟩⟩

end Yau.Blueprint.V02Proof
