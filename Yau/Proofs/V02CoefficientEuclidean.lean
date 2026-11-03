import Yau.Proofs.V02FirstCoefficientsUniform
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Finite coefficient data use the same scalar entries in the raw Pi
spray times and in the Euclidean input of the actual area estimate. -/

open scoped Topology ContDiff
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

variable {b : ℕ}

def coefficientsEuclidean (c : ℂ → Fin b → ℂ) (ζ : ℂ) : ComplexVector b :=
  WithLp.toLp 2 (c ζ)

theorem coefficientsEuclidean_contDiffOn {c : ℂ → Fin b → ℂ}
    (hc : ∀ k, ContDiffOn ℂ ∞ (fun ζ => c ζ k) (closedBall (0 : ℂ) 1)) :
    ContDiffOn ℂ ∞ (coefficientsEuclidean c) (closedBall (0 : ℂ) 1) :=
  (contDiffOn_piLp 2).mpr hc

theorem coefficientsEuclidean_norm_bound {c : ℂ → Fin b → ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hc : ∀ ζ ∈ closedBall (0 : ℂ) 1, ∀ k, ‖c ζ k‖ ≤ C) :
    ∀ ζ ∈ closedBall (0 : ℂ) 1,
      ‖coefficientsEuclidean c ζ‖ ≤ ((b : ℝ) + 1) * C := by
  intro ζ hζ
  have hsum : ∑ k : Fin b, ‖c ζ k‖ ^ 2 ≤ (b : ℝ) * C ^ 2 := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
      show ‖c ζ k‖ ^ 2 ≤ C ^ 2 from by
        simpa only [sq] using mul_self_le_mul_self (norm_nonneg _) (hc ζ hζ k))
    simpa using hs
  have hdim : (b : ℝ) ≤ ((b : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (b : ℝ), (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
  have hs : ‖coefficientsEuclidean c ζ‖ ^ 2 ≤ (((b : ℝ) + 1) * C) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact hsum.trans ((mul_le_mul_of_nonneg_right hdim (sq_nonneg C)).trans_eq (by ring))
  nlinarith [norm_nonneg (coefficientsEuclidean c ζ),
    mul_nonneg (by positivity : 0 ≤ (b : ℝ) + 1) hC]

theorem coefficientsEuclidean_boundary_budget {c : ℂ → Fin b → ℂ} {S : ℝ}
    (hc : ∀ k, boundaryDSq (fun θ (_ : Unit) => c (circlePoint θ) k) ≤ ENNReal.ofReal S) :
    boundaryDSq (fun θ k => coefficientsEuclidean c (circlePoint θ) k) ≤
      ENNReal.ofReal ((b : ℝ) * S) := by
  change boundaryDSq (fun θ k => c (circlePoint θ) k) ≤ _
  rw [boundaryDSq_eq_sum_singleton]
  calc
    _ ≤ ∑ _k : Fin b, ENNReal.ofReal S := Finset.sum_le_sum (fun k _ => hc k)
    _ = (b : ENNReal) * ENNReal.ofReal S := by simp
    _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg b), ENNReal.ofReal_natCast]

end Yau.Blueprint.V02Proof
