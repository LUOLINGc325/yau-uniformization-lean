import Yau.Proofs.V03RealizedVelocityRegularity
import Yau.Proofs.V03AmbientVelocitySeminorm
import Yau.Proofs.V03ConstantDisc
import Yau.Proofs.V03EnergyTraceBounds

/-! The finitely indexed factors in the actual boundary-current expansion
are genuine first velocities or the constant one, and genuine immersion or velocity traces. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def currentVelocityFactor {q : ℕ} (V : ℂ → ComplexVector q) : Option (Fin q) → ℂ → ℂ
  | none, _ => 1
  | some a, ζ => V ζ a

def currentDerivativeFunction {n q : ℕ} {M : ComplexManifold n}
    (G : CotangentPoint M → ComplexVector q) (f : ℂ → CotangentPoint M)
    (V : ℂ → ComplexVector q) : Fin q ⊕ Fin q → ℂ → ℂ
  | .inl a, ζ => G (f ζ) a
  | .inr a, ζ => V ζ a

theorem currentVelocityFactor_contDiffOn {q : ℕ} {V : ℂ → ComplexVector q}
    (hV : ContDiffOn ℂ ∞ V (Metric.closedBall (0 : ℂ) 1)) (i : Option (Fin q)) :
    ContDiffOn ℂ ∞ (currentVelocityFactor V i) (Metric.closedBall (0 : ℂ) 1) := by
  cases i with
  | none => exact contDiffOn_const
  | some a => exact (contDiffOn_piLp 2).mp hV a

theorem currentVelocityFactor_boundaryDSq_le {q : ℕ} (V : ℂ → ComplexVector q)
    (i : Option (Fin q)) :
    boundaryDSq (fun θ (_ : Unit) => currentVelocityFactor V i (circlePoint θ)) ≤
      boundaryDSq (fun θ a => V (circlePoint θ) a) := by
  cases i with
  | none =>
    have hc : boundaryDSq (fun (_ : ℝ) (_ : Unit) => (1 : ℂ)) = 0 := by
      simpa only [scalarDSq, Complex.ofReal_one] using scalarDSq_const (1 : ℝ)
    rw [show (fun θ (_ : Unit) => currentVelocityFactor V none (circlePoint θ)) =
      (fun (_ : ℝ) (_ : Unit) => (1 : ℂ)) from rfl, hc]
    exact bot_le
  | some a => exact boundaryDSq_component_le (fun θ b => V (circlePoint θ) b) a

theorem currentVelocityFactor_boundary_norm_le {q : ℕ} {V : ℂ → ComplexVector q}
    {L : ℝ} (hL : 0 ≤ L) (hV : ∀ θ, ‖V (circlePoint θ)‖ ≤ L)
    (i : Option (Fin q)) (θ : ℝ) : ‖currentVelocityFactor V i (circlePoint θ)‖ ≤ L + 1 := by
  cases i with
  | none => simpa only [currentVelocityFactor, norm_one] using (by linarith : (1 : ℝ) ≤ L + 1)
  | some a => exact ((PiLp.norm_apply_le (V (circlePoint θ)) a).trans (hV θ)).trans (by linarith)

theorem currentDerivativeFunction_contDiffOn {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) {V : ℂ → ComplexVector q}
    (hV : ContDiffOn ℂ ∞ V (Metric.closedBall (0 : ℂ) 1)) (i : Fin q ⊕ Fin q) :
    ContDiffOn ℂ ∞ (currentDerivativeFunction G f V i) (Metric.closedBall (0 : ℂ) 1) := by
  cases i with
  | inl a => exact (contDiffOn_piLp 2).mp (cotangentDisc_ambient_contDiffOn hf hG) a
  | inr a => exact (contDiffOn_piLp 2).mp hV a

theorem admissible_ambientTrace_boundaryDSq_le_energy {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j : ℕ) {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    boundaryDSq (fun θ a => d.G (F.f (circlePoint θ)) a) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹) * variationEnergy d j F := by
  rw [boundaryDSq_vector_eq_inverse_area (cotangentDisc_ambient_contDiffOn hF.1 hd.2.2.2.2.1.1)]
  gcongr
  exact euclideanArea_le_variationEnergy d j F

end Yau.Blueprint.V03Proof
