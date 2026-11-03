import Yau.Proofs.F04ClassicalWeakEquation
import Yau.LeafProofs.L16LocalWeakEvolution

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem weak_divergence_restrict {n : ℕ} {O V : Set (Space n)} {I J : Set ℝ}
    (hsub : V ×ˢ J ⊆ O ×ˢ I) {u R : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (heq : WeakDivergenceEvolution O I u P R) :
    WeakDivergenceEvolution V J u P R := by
  intro φ hφ
  have hφO : Test (O ×ˢ I) φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hsub⟩
  have hh := heq φ hφO
  rw [dg_productVolume_eq_restrict] at hh ⊢
  simp_rw [test_timeDerivative_eq_joint_fderiv (hφ.1.differentiable (by simp) _),
    d_eq_joint_fderiv (hφ.1.differentiable (by simp) _)] at hh ⊢
  rw [divergence_test_integral_restrict_eq_global hφO] at hh
  rw [divergence_test_integral_restrict_eq_global hφ]
  exact hh

theorem weak_homogeneous_equation_restrict {n : ℕ} {O V : Set (Space n)} {I J : Set ℝ}
    (hsub : V ×ˢ J ⊆ O ×ˢ I) {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (heq : WeakEquation O I a b (fun _ => 0) u G) :
    WeakEquation V J a b (fun _ => 0) u G := by
  have hdiv := weak_divergence_restrict hsub (weakEquation_homogeneous_divergence heq)
  intro φ hφ
  have hh := hdiv φ hφ
  simpa only [zero_mul, integral_zero, energyFlux, energyDrift, Finset.sum_mul] using hh

end Yau.F04Proof
