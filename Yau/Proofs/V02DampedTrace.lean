import Yau.Proofs.V02OuterDamping
import Yau.Proofs.V02RadialTrace

/-! The actual outer-damped vector correction has a uniform half-order
bound. Its phase is controlled separately from the radial damping. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {ι : Type*} [Fintype ι]

theorem outerDamping_mul_factorization {P : ℝ} (hP : 0 < P) {u : ℝ → ι → ℂ}
    (hu : ∀ i, ContDiff ℝ ∞ (fun θ => u θ i))
    (hp : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) (i : ι) (θ : ℝ) :
    outerDamping P u (circlePoint θ) * u θ i =
      circlePoint (V03Proof.harmonicConjugateTrace (dampingLogTrace P u) θ) *
        radialDampingTrace P u i θ := by
  have hq := dampingLogTrace_contDiff hP hu
  have hqp := dampingLogTrace_periodic P hp
  have he : Real.exp (dampingLogTrace P u θ) = reciprocalDamping P (∑ k, ‖u θ k‖ ^ 2) := by
    rw [dampingLogTrace, Real.exp_neg, Real.exp_log (by
      have hs : 0 ≤ ∑ k, ‖u θ k‖ ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
      positivity)]
    rfl
  rw [outerDamping, V03Proof.outerCandidate_boundary_factorization hq hqp]
  simp only [Nat.cast_one, one_mul, he, radialDampingTrace]
  ring

theorem outerDamping_mul_norm_le {P : ℝ} (hP : 0 < P) {u : ℝ → ι → ℂ}
    (hu : ∀ i, ContDiff ℝ ∞ (fun θ => u θ i))
    (hp : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) (i : ι) (θ : ℝ) :
    ‖outerDamping P u (circlePoint θ) * u θ i‖ ≤ Real.sqrt P / 2 := by
  rw [outerDamping_mul_factorization hP hu hp, norm_mul, V03Proof.circlePoint_norm, one_mul]
  exact radialDampingTrace_norm_le hP u i θ

theorem outerDamping_mul_boundaryDSq_le {P : ℝ} (hP : 0 < P) {u : ℝ → ι → ℂ}
    (hu : ∀ i, ContDiff ℝ ∞ (fun θ => u θ i))
    (hp : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) (i : ι) :
    boundaryDSq (fun θ (_ : Unit) => outerDamping P u (circlePoint θ) * u θ i) ≤
      ENNReal.ofReal 20 * boundaryDSq u := by
  let q := dampingLogTrace P u
  let phase : ℝ → ℂ := fun θ => circlePoint (V03Proof.harmonicConjugateTrace q θ)
  have hq := dampingLogTrace_contDiff hP hu
  have hqp := dampingLogTrace_periodic P hp
  have hc : Continuous phase := V03Proof.circlePoint_contDiff.continuous.comp
    (V03Proof.harmonicConjugateTrace_contDiff hq hqp).continuous
  have hcp : Function.Periodic phase (2 * Real.pi) := fun θ =>
    congrArg circlePoint (V03Proof.harmonicConjugateTrace_periodic q θ)
  have hc1 : ∀ θ, ‖phase θ‖ ≤ 1 := fun θ => (V03Proof.circlePoint_norm _).le
  have hr := radialDampingTrace_continuous hP (fun i => (hu i).continuous) i
  have hrp := radialDampingTrace_periodic P hp i
  have hprod := V03Proof.boundaryDSq_mul_le hc hr hcp hrp
    (M := 1) (N := Real.sqrt P) (by norm_num) (Real.sqrt_nonneg P) hc1 (fun θ =>
      (radialDampingTrace_norm_le hP u i θ).trans (half_le_self (Real.sqrt_nonneg P)))
  have hphase : boundaryDSq (fun θ (_ : Unit) => phase θ) ≤
      ENNReal.ofReal P⁻¹ * boundaryDSq u := by
    have h := V03Proof.outer_phase_boundaryDSq_le hq hqp 1
    simp only [Nat.cast_one, one_pow, ENNReal.ofReal_one, one_mul] at h
    exact h.trans (dampingLogTrace_boundaryDSq_le hP (fun i => (hu i).continuous) hp)
  have hrad := radialDampingTrace_boundaryDSq_le hP (fun i => (hu i).continuous) hp i
  have heq : (fun θ (_ : Unit) => outerDamping P u (circlePoint θ) * u θ i) =
      fun θ (_ : Unit) => phase θ * radialDampingTrace P u i θ := by
    funext θ _
    exact outerDamping_mul_factorization hP hu hp i θ
  rw [heq]
  have hm := hprod.trans (add_le_add
    (mul_le_mul_right hphase (ENNReal.ofReal (2 * Real.sqrt P ^ 2)))
    (mul_le_mul_right hrad (ENNReal.ofReal (2 * (1 : ℝ) ^ 2))))
  rw [Real.sq_sqrt hP.le] at hm
  have he : ENNReal.ofReal (2 * P) * ENNReal.ofReal P⁻¹ = 2 := by
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, mul_inv_cancel₀ hP.ne', mul_one]
    norm_num
  have htwo : ENNReal.ofReal (2 * (1 : ℝ) ^ 2) = 2 := by norm_num
  have hnine : ENNReal.ofReal (9 : ℝ) = 9 := by norm_num
  rw [← mul_assoc, he, htwo, hnine] at hm
  convert hm using 1 <;> norm_num <;> ring

end Yau.Blueprint.V02Proof
