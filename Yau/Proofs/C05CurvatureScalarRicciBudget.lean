import Yau.Proofs.C05ScalarJetBounds
import Yau.Proofs.C05RealRicciJets

/-! A single finite intrinsic budget follows from the actual curvature jets.
The bound is uniform before any point, flow slice, or chart is selected. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_uniform_scalar_ricci_jet_budget (C : ℕ → ℝ) (hC : ∀ j, 0 < C j) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (k : HermitianField M), MetricSmooth k → KahlerClosed k →
      ∀ x, (∀ j ≤ m, curvatureJetNorm k j x ≤ C j) →
        (∀ j ≤ m, scalarJetNorm k (scalarCurvature k) j x ≤ B) ∧
        (∀ j ≤ m, realRicciJetNorm k j x ≤ B) := by
  let T := ∑ j ∈ Finset.range (m+1), C j
  let B := 1+((n:ℝ)+Real.sqrt (2*n:ℕ))*T
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => (hC j).le)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro k hk hK x hcurv
  have hCj (j : ℕ) (hj : j ≤ m) : C j ≤ T :=
    Finset.single_le_sum (fun l _ => (hC l).le) (Finset.mem_range.mpr (by omega))
  have hbScalar (j : ℕ) (hj : j ≤ m) : (n:ℝ)*curvatureJetNorm k j x ≤ B := by
    have h1 := mul_le_mul_of_nonneg_left ((hcurv j hj).trans (hCj j hj)) (Nat.cast_nonneg n : (0:ℝ)≤n)
    have h2 := mul_nonneg (Real.sqrt_nonneg (2*n:ℕ)) hT
    dsimp [B]
    nlinarith
  have hbRicci (j : ℕ) (hj : j ≤ m) : Real.sqrt (2*n:ℕ)*curvatureJetNorm k j x ≤ B := by
    have h1 := mul_le_mul_of_nonneg_left ((hcurv j hj).trans (hCj j hj)) (Real.sqrt_nonneg (2*n:ℕ))
    have h2 := mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) hT
    dsimp [B]
    nlinarith
  exact ⟨fun j hj => (scalarJetNorm_le_curvatureJetNorm k hk hK j x).trans (hbScalar j hj),
    fun j hj => (realRicciJetNorm_le_curvatureJetNorm k hk j x).trans (hbRicci j hj)⟩

end Yau.Proofs.C05Aux
