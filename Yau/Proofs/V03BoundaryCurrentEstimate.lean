import Yau.Proofs.V03BoundaryDerivativePairing

/-! The genuine signed derivative pairing controls each boundary current
linearly by the original half-order seminorms, on the paper's angular interval. -/

open scoped Topology
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem sqrt_ennreal_toReal_product_le_half (A B : ENNReal) :
    Real.sqrt A.toReal * Real.sqrt B.toReal ≤ (A.toReal + B.toReal) / 2 := by
  nlinarith [sq_nonneg (Real.sqrt A.toReal - Real.sqrt B.toReal),
    Real.sq_sqrt (ENNReal.toReal_nonneg (a := A)),
    Real.sq_sqrt (ENNReal.toReal_nonneg (a := B))]

theorem abs_boundaryDerivativePair_le_half {u v v' : ℝ → ℂ}
    (hu : Continuous u) (hv' : Continuous v')
    (hup : Function.Periodic u (2 * Real.pi))
    (hv'p : Function.Periodic v' (2 * Real.pi))
    (hd : ∀ θ, HasDerivAt v (v' θ) θ) (hvp : Function.Periodic v (2 * Real.pi))
    (huf : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hvf : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤) :
    |circleAverage (fun θ => (star (u θ) * v' θ).re)| ≤
      ((boundaryDSq (fun θ (_ : Unit) => u θ)).toReal +
        (boundaryDSq (fun θ (_ : Unit) => v θ)).toReal) / 2 :=
  (abs_boundaryDerivativePair_le hu hv' hup hv'p hd hvp huf hvf).trans
    (sqrt_ennreal_toReal_product_le_half _ _)

theorem periodic_integral_eq_two_pi_average {g : ℝ → ℝ}
    (hg : Function.Periodic g (2 * Real.pi)) :
    (∫ θ in (-Real.pi)..Real.pi, g θ) = (2 * Real.pi) * circleAverage g := by
  have hs := hg.intervalIntegral_add_eq (-Real.pi) 0
  have hs' : (∫ θ in (-Real.pi)..Real.pi, g θ) = ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ := by
    have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
    simpa only [he, zero_add] using hs
  rw [hs', circleAverage, ← mul_assoc, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul]

theorem abs_boundaryDerivativeCurrent_le {u v v' : ℝ → ℂ}
    (hu : Continuous u) (hv' : Continuous v')
    (hup : Function.Periodic u (2 * Real.pi))
    (hv'p : Function.Periodic v' (2 * Real.pi))
    (hd : ∀ θ, HasDerivAt v (v' θ) θ) (hvp : Function.Periodic v (2 * Real.pi))
    (huf : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hvf : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤) :
    |∫ θ in (-Real.pi)..Real.pi, (star (u θ) * v' θ).re| ≤
      Real.pi * ((boundaryDSq (fun θ (_ : Unit) => u θ)).toReal +
        (boundaryDSq (fun θ (_ : Unit) => v θ)).toReal) := by
  have hp : Function.Periodic (fun θ => (star (u θ) * v' θ).re) (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [hup θ, hv'p θ]
  rw [periodic_integral_eq_two_pi_average hp, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  calc
    _ ≤ (2 * Real.pi) * (((boundaryDSq (fun θ (_ : Unit) => u θ)).toReal +
        (boundaryDSq (fun θ (_ : Unit) => v θ)).toReal) / 2) :=
      mul_le_mul_of_nonneg_left (abs_boundaryDerivativePair_le_half hu hv' hup hv'p hd hvp huf hvf)
        (by positivity)
    _ = _ := by ring

end Yau.Blueprint.V03Proof
