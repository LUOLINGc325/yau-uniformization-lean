import Yau.Proofs.Y06FiniteStages
import Yau.Proofs.Y06WeightedDeterminant
import Yau.Proofs.Y06VolumeInduction
import Yau.Proofs.Y06TriangularBounds

/-! Volume is proved backwards after completing every homogeneous layer. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n d : ℕ}

theorem constantVolume_linearPolynomial (A : Herm n) (hd : 1 ≤ d) (hA : A.det ≠ 0) :
    IsConstantVolumeJet (linearPolynomial A) d := by
  refine ⟨linearPoly_fixesZero A, (linearPoly_degree_le A).trans hd, ?_,
    positiveJacFlat_linearPolynomial A d⟩
  simpa only [linearPolynomial_as_linearPoly, linearPoly_linearPart] using hA

theorem constantVolume_id (hd : 1 ≤ d) : IsConstantVolumeJet (PolyMap.id : PolyMap n) d := by
  simpa only [linearPolynomial_as_linearPoly, linearPoly_one] using
    constantVolume_linearPolynomial (1 : Herm n) hd (by simp)

theorem finiteStage_model_data {active : ℕ → Prop} {a : ℕ → Fin n → ℂ}
    (ha : ∀ k i, a k i ≠ 0) {J : ℕ → Herm n} {w : ℕ → Fin n → ℝ}
    {P H G : ℕ → PolyMap n}
    (hSpec : FiniteStageSpec active (fun k => Matrix.diagonal (a k)) J w P H G d)
    (hw : ∀ k, active k → ∀ i, 1 ≤ w k i) (hd : 1 ≤ d) :
    ∀ k, active k →
      IsPolyAutomorphism (G k) (triangularInverseApprox (G k) (a k) n) ∧
      (triangularInverseApprox (G k) (a k) n).degree ≤ d ^ n ∧
      (G k).jacDet = C (Matrix.diagonal (a k)).det := by
  intro k hk
  obtain ⟨hG0, hGlin, hGdeg, hGall, hGjet⟩ := hSpec.2.2 k hk
  have hN := nonlinearPart_strict_variables hG0 hGall (hw k hk)
  exact ⟨strict_triangular_inverse (G k) (a k) (w k) (ha k) hGlin hN,
    triangularInverseApprox_degree (G k) (a k) hd hGdeg n,
    strict_triangular_jacDet (G k) (a k) (w k) hGlin hN⟩

theorem finiteStage_correction_volume (b : ℕ) {active : ℕ → Prop}
    (hactive : ∀ k, active k → k < b) {a : ℕ → Fin n → ℂ}
    (ha : ∀ k i, a k i ≠ 0) {J : ℕ → Herm n} {w : ℕ → Fin n → ℝ}
    {P H G : ℕ → PolyMap n} (hd : 1 ≤ d)
    (hP : ∀ k, active k → IsConstantVolumeJet (P k) d)
    (hSpec : FiniteStageSpec active (fun k => Matrix.diagonal (a k)) J w P H G d)
    (hw : ∀ k, active k → ∀ i, 1 ≤ w k i) :
    ∀ k, IsConstantVolumeJet (H k) d := by
  have hinactive (k : ℕ) (hk : ¬active k) : IsConstantVolumeJet (H k) d := by
    rw [(hSpec.1 k hk).1]
    exact constantVolume_id hd
  have hstep (k : ℕ) (hk : active k) (hnext : IsConstantVolumeJet (H (k + 1)) d) :
      IsConstantVolumeJet (H k) d := by
    obtain ⟨hG0, hGlin, hGdeg, hGall, hGjet⟩ := hSpec.2.2 k hk
    obtain ⟨hAuto, hInvDeg, hJac⟩ := finiteStage_model_data ha hSpec hw hd k hk
    have hdet : (G k).linearPart.det ≠ 0 := by
      rw [hGlin, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => ha k i)
    have hJac' : (G k).jacDet = C (G k).linearPart.det := by rw [hGlin]; exact hJac
    exact volume_of_backward_jet_identity (P k) (H k) (H (k + 1)) (G k) (J k) hd
      (hP k hk) hnext (hSpec.2.1 k).1.1 (hSpec.2.1 k).2.1 (hSpec.2.1 k).1.2
      hG0 hdet hJac' hGjet
  have hbelow : ∀ k, k ≤ b → IsConstantVolumeJet (H k) d := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self => exact hinactive b (fun h => Nat.lt_irrefl b (hactive b h))
    | of_succ k hk ih =>
      by_cases hact : active k
      · exact hstep k hact ih
      · exact hinactive k hact
  intro k
  by_cases hk : k ≤ b
  · exact hbelow k hk
  · exact hinactive k (fun h => by have := hactive k h; omega)

end Yau.Proofs.Y06Aux
