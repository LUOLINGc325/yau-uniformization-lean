import Yau.LeafProofs.L17BanachLogarithm
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow

open Set Metric
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17BanachRadialLogarithmAux
open Yau.LeafProofs.L17BanachLogarithmAux

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]

def radialLogTerm (z : A) (t : ℝ) (k : ℕ) : A :=
  ((-1 : ℝ)^k*t^k) • z^(k+1)

def radialLogDerivative (z : A) (t : ℝ) : A := ∑' k : ℕ, radialLogTerm A z t k

def radialLogPrimitiveTerm (z : A) (k : ℕ) (s : ℝ) : A :=
  logCoefficient (k+1) • ((s • z)^(k+1))

theorem radialLog_coefficient_succ_mul (k : ℕ) :
    logCoefficient (k+1)*((k+1 : ℕ) : ℝ)=(-1 : ℝ)^k := by
  have hk : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [logCoefficient,div_mul_cancel₀ _ hk]
  rw [show k+1+1=k+2 by omega,pow_add]
  norm_num

theorem radialLogPrimitiveTerm_hasDerivAt (z : A) (k : ℕ) (t : ℝ) :
    HasDerivAt (radialLogPrimitiveTerm A z k) (radialLogTerm A z t k) t := by
  have h := ((hasDerivAt_pow (k+1) t).const_mul (logCoefficient (k+1))).smul_const (z^(k+1))
  convert h using 1
  · funext s
    simp only [radialLogPrimitiveTerm,smul_pow,smul_smul]
  · simp only [Nat.add_sub_cancel,← mul_assoc,radialLog_coefficient_succ_mul,radialLogTerm]

theorem radialLogTerm_norm_le (z : A) {a t : ℝ} (ha : 0 ≤ a) (ht : |t| ≤ a) (k : ℕ) :
    ‖radialLogTerm A z t k‖ ≤ ‖z‖*(a*‖z‖)^k := by
  calc
    ‖radialLogTerm A z t k‖ = |t|^k*‖z^(k+1)‖ := by
      simp only [radialLogTerm,norm_smul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,
        one_mul,Real.norm_eq_abs]
    _ ≤ a^k*‖z‖^(k+1) := mul_le_mul
      (pow_le_pow_left₀ (abs_nonneg t) ht k)
      (norm_pow_succ_le_radius (norm_nonneg z) (le_refl ‖z‖) k)
      (norm_nonneg _) (pow_nonneg ha _)
    _ = ‖z‖*(a*‖z‖)^k := by rw [mul_pow,pow_succ]; ring

theorem radialLog_buffer {z : A} (hz : ‖z‖ < 1) :
    ∃ a : ℝ, 1 < a ∧ 0 ≤ a*‖z‖ ∧ a*‖z‖ < 1 := by
  let a := 2/(1+‖z‖)
  have hd : 0 < 1+‖z‖ := by positivity
  have ha : 1 < a := (lt_div_iff₀ hd).mpr (by linarith)
  refine ⟨a,ha,mul_nonneg (by linarith) (norm_nonneg z),?_⟩
  change (2/(1+‖z‖))*‖z‖ < 1
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hd).mpr
  linarith

variable [CompleteSpace A]

theorem radialLogTerm_summable_on_buffer (z : A) {a t : ℝ} (ha : 0 ≤ a)
    (hq : a*‖z‖ < 1) (ht : |t| ≤ a) : Summable (radialLogTerm A z t) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (mul_nonneg ha (norm_nonneg z)) hq).mul_left ‖z‖)
  exact radialLogTerm_norm_le A z ha ht

theorem radialLogDerivative_summable {z : A} (hz : ‖z‖ < 1) {t : ℝ} (ht : |t| ≤ 1) :
    Summable (fun k : ℕ => ((-1 : ℝ)^k*t^k) • z^(k+1)) := by
  obtain ⟨a,ha,hq0,hq⟩ := radialLog_buffer A hz
  exact radialLogTerm_summable_on_buffer A z (by linarith) hq (ht.trans ha.le)

end Yau.LeafProofs.L17BanachRadialLogarithmAux
