import Yau.Proofs.V03SignedAngularMultiplier
import Yau.Proofs.V03PeriodicInnerParseval
import Yau.Proofs.V03FourierDerivativeAll

/-! The actual signed boundary derivative current is bounded by the
original homogeneous half-order seminorms, with exact circle normalization. -/

open scoped Topology lp
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem dirichletCoeff_signedAngular_pair (u v : ℝ → ℂ) (k : ℤ) :
    inner ℂ (dirichletCoeff u k) (signedAngularMultiplier k * dirichletCoeff v k) =
      star (circleFourier u k) * (Complex.I * (k : ℂ) * circleFourier v k) := by
  have hs : (Real.sqrt |(k : ℝ)| : ℂ) ^ 2 = ((|(k : ℝ)| : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (abs_nonneg (k : ℝ))
  calc
    _ = signedAngularMultiplier k * (Real.sqrt |(k : ℝ)| : ℂ) ^ 2 *
        star (circleFourier u k) * circleFourier v k := by
      simp only [dirichletCoeff, RCLike.inner_apply, Complex.star_def, map_mul, Complex.conj_ofReal]
      ring
    _ = _ := by rw [hs, signedAngularMultiplier_abs]; ring

theorem boundaryDerivativePair_eq_inner {u v v' : ℝ → ℂ}
    (hu : Continuous u) (hv' : Continuous v')
    (hup : Function.Periodic u (2 * Real.pi))
    (hv'p : Function.Periodic v' (2 * Real.pi))
    (hd : ∀ θ, HasDerivAt v (v' θ) θ) (hvp : Function.Periodic v (2 * Real.pi))
    (huf : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hvf : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤) :
    inner ℂ (dirichletVector u huf) (signedAngularMap (dirichletVector v hvf)) =
      circleFourier (fun θ => star (u θ) * v' θ) 0 := by
  have hp : v (2 * Real.pi) = v 0 := by simpa only [zero_add] using hvp 0
  have hi : IntervalIntegrable v' volume 0 (2 * Real.pi) := hv'.intervalIntegrable _ _
  have hh := periodic_parseval_inner hu hv' hup hv'p
  rw [← hh.tsum_eq]
  change (∑' k : ℤ, inner ℂ (dirichletCoeff u k)
    (signedAngularMultiplier k * dirichletCoeff v k)) = _
  apply tsum_congr
  intro k
  rw [dirichletCoeff_signedAngular_pair, circleFourier_derivative_all (fun θ _ => hd θ) hi hp]

theorem abs_boundaryDerivativePair_le {u v v' : ℝ → ℂ}
    (hu : Continuous u) (hv' : Continuous v')
    (hup : Function.Periodic u (2 * Real.pi))
    (hv'p : Function.Periodic v' (2 * Real.pi))
    (hd : ∀ θ, HasDerivAt v (v' θ) θ) (hvp : Function.Periodic v (2 * Real.pi))
    (huf : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hvf : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤) :
    |circleAverage (fun θ => (star (u θ) * v' θ).re)| ≤
      Real.sqrt (boundaryDSq (fun θ (_ : Unit) => u θ)).toReal *
        Real.sqrt (boundaryDSq (fun θ (_ : Unit) => v θ)).toReal := by
  have hc := periodic_parseval_inner hu hv' hup hv'p
  have hr := periodic_parseval_inner_real hu hv' hup hv'p
  have heq : (circleFourier (fun θ => star (u θ) * v' θ) 0).re =
      circleAverage (fun θ => (star (u θ) * v' θ).re) :=
    (hc.mapL Complex.reCLM).unique hr
  rw [← heq, ← boundaryDerivativePair_eq_inner hu hv' hup hv'p hd hvp huf hvf]
  calc
    _ ≤ ‖inner ℂ (dirichletVector u huf) (signedAngularMap (dirichletVector v hvf))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖dirichletVector u huf‖ * ‖signedAngularMap (dirichletVector v hvf)‖ := norm_inner_le_norm _ _
    _ ≤ ‖dirichletVector u huf‖ * ‖dirichletVector v hvf‖ := by
      gcongr
      exact signedAngularMap_norm_apply_le _
    _ = _ := by rw [dirichletVector_norm, dirichletVector_norm]

end Yau.Blueprint.V03Proof
