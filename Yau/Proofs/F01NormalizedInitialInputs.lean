import Yau.Proofs.F01NormalizedInitialPotential
import Yau.Proofs.F01NormalizedPotentialSup
import Yau.Proofs.F01NormalizedTransformedRange

/-! Every input of the original normalized initial-surface estimate is
constructed from the actual bounded geometry, scalar potential equation and
coarse native metric comparison. Its numerical budgets precede all flow
realizations, chart centers and admissible scales. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_normalized_initial_inputs
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {C α β : ℝ} (hC : 1 ≤ C) (hα : α ≤ 1) (hβ : β ≤ 1) :
    ∃ ell upper K B : ℝ, 0 < ell ∧ ell ≤ upper ∧ 0 < K ∧ 0 ≤ B ∧
      ∀ (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T ρ : ℝ),
      0 < ρ → ρ ≤ A.radius → ρ ≤ 1 → ρ ^ 2 ≤ T →
      SmoothSpaceTime U (Icc 0 T) → h 0 = g → (∀ x, U x 0 = 0) →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
        (flowLogDetRatio g h x s) (Icc 0 T) s) →
      (∀ x s, s ∈ Icc 0 T →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) →
      ∀ a : M.Carrier,
      let H := fun z => pullbackMatrix g (A.chart a) (ρ • z)
      let v := forwardZeroSpaceTime
        (parabolicRescalePotential ρ (fun q : Point n => U (A.chart a q.1) q.2))
      let Q := cylinder (ball (0 : Space n) 1) (-1) 1
      ContDiffOn ℝ ∞ H (ball 0 1) ∧ (∀ x ∈ ball 0 1, (H x).PosDef) ∧
      HolderBound β Q (clampedBackground H) K ∧ HolderBound α Q (backgroundSource H) K ∧
      C2 Q v ∧ (∀ p ∈ Q, |v p| ≤ B) ∧ (∀ p ∈ Q, p.2 ≤ 0 → v p = 0) ∧
      (∀ p ∈ Q,
        (((clampedBackground H p + complexHessianMap (hessian v p) : Sym n) : Mat n) -
          ell • (1 : Mat n)).PosSemidef ∧
        (upper • (1 : Mat n) -
          ((clampedBackground H p + complexHessianMap (hessian v p) : Sym n) : Mat n)).PosSemidef) ∧
      (∀ p ∈ Q, timeD Q v p - logDetReal (clampedBackground H p + complexHessianMap (hessian v p)) =
        backgroundSource H p) := by
  obtain ⟨ell, upper, hell, hlu, hrange⟩ := exists_normalized_transformed_range g hg A hC
  obtain ⟨K, hK, hholder⟩ := bounded_geometry_initial_holder A hα hβ
  refine ⟨ell, upper, K, (n : ℝ) * Real.log C, hell, hlu, hK,
    mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hC), ?_⟩
  intro h U T ρ hρ hρr hρ1 hρT hU hh0 hU0 hpot hpde hflow a
  dsimp only
  refine ⟨dilated_background_smooth A a hρ hρr,
    (fun x hx => dilated_background_posDef A a hρ hρr hx),
    (hholder ρ hρ hρr hρ1 a).1, (hholder ρ hρ hρr hρ1 a).2,
    normalized_initial_potential_C2 g A h U hρ hρr hρT hU hh0 hU0 hpde a,
    normalized_potential_sup_of_metric_sandwich g h U hρ hρr hρT hC hU0 hpde hflow (A.chart a),
    ?_, hrange h U T ρ hρ hρr hρT hU hh0 hpot hflow a,
    (fun p hp => normalized_zero_potential_initial_equation g hg A h U
      hρ hρr hρT hU hh0 hU0 hpot hpde a hp)⟩
  intro p hp ht
  exact forwardZeroExtension_eq_of_nonpos _ ht

end Yau.NodeProofs.F01Aux
