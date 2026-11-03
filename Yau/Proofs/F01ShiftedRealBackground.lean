import Yau.Proofs.F01ShiftedBackgroundJets
import Yau.Proofs.F01ZeroSpatialJetHolder
import Yau.Proofs.F01ScalarProductHolder

/-! The exact realified background used by Chu has its own original
Frobenius Holder bound. Its transformed real Hessian is identified with
the genuine complex potential matrix, without changing matrix norms. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
attribute [local instance] backgroundRealSymNormedSpace backgroundRealSymContinuousSMul

theorem shifted_real_background_holder_budget (A : BoundedChartFamily g)
    {T β : ℝ} (hT : 0 ≤ T) (hβ : β ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ρ τ : ℝ), 0 < ρ → ρ ≤ A.radius → ρ ≤ 1 → |τ| ≤ T →
      ∀ a : M.Carrier, HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iota (shiftedComplexBackground A a ρ τ p)) K := by
  obtain ⟨Kf, hKf, hF⟩ := dilated_spatial_holder_budget
    (n := n) (F := Sym n) (realified_background_uniform_jets A 1) (realified_background_smooth A) hβ
  obtain ⟨Kg, hKg, hG⟩ := dilated_spatial_holder_budget
    (n := n) (F := Sym n) (realified_backgroundRicci_uniform_jets A 1) (realified_backgroundRicci_smooth A) hβ
  obtain ⟨Kt, hKt, hClock⟩ := affine_clock_holder_budget (n := n) hT hβ
  refine ⟨Kf + 2 * Kt * Kg, by positivity, ?_⟩
  intro ρ τ hρ hρr hρ1 hτ a
  have hSlope : |-(ρ ^ 2)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hTime := hClock (-τ) (-(ρ ^ 2)) (by simpa only [abs_neg] using hτ) hSlope
  have hProduct := holderBound_scalar_smul_product hTime (hG ρ hρ hρr hρ1 a)
  apply holderBound_congr_on_native (holderBound_add (hF ρ hρ hρr hρ1 a) hProduct)
  intro p hp
  simp only [shiftedComplexBackground, chartAffineBackground, affineParabolicPoint,
    add_zero, iota_sub, iota_real_smul]
  rw [show -τ + -(ρ ^ 2) * p.2 = -(τ + ρ ^ 2 * p.2) by ring, neg_smul]
  rfl

theorem real_chart_potential_matrix {S : Point n → Matrix (Fin n) (Fin n) ℂ}
    {u : Point n → ℝ} {Q : Set (Point n)} (hu : C2 Q u) {p : Point n} (hp : p ∈ Q) :
    iota (S p) + complexHessianMap (hessian u p) = iota (chartPotentialMatrix S u p) := by
  rw [complexHessianMap_spaceTime (hu.2.2.2.2.1 p hp), ← iota_add]
  rfl

end Yau.NodeProofs.F01Aux
