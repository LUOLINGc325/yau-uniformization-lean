import Yau.Proofs.V02DampingRadial
import Yau.Proofs.V02DampingTrace

/-! The finite-vector radial damping gives uniform supremum and half-order
control of each corrected coordinate, including vectors with zero entries. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {ι : Type*} [Fintype ι]

def radialDampingTrace (P : ℝ) (u : ℝ → ι → ℂ) (i : ι) (θ : ℝ) : ℂ :=
  (reciprocalDamping P (∑ k, ‖u θ k‖ ^ 2) : ℂ) * u θ i

theorem radialDampingTrace_continuous {P : ℝ} (hP : 0 < P) {u : ℝ → ι → ℂ}
    (hu : ∀ i, Continuous (fun θ => u θ i)) (i : ι) :
    Continuous (radialDampingTrace P u i) := by
  have hs : Continuous (fun θ => ∑ k, ‖u θ k‖ ^ 2) :=
    continuous_finsetSum _ (fun k _ => (hu k).norm.pow 2)
  have hr : Continuous (fun θ => reciprocalDamping P (∑ k, ‖u θ k‖ ^ 2)) := by
    apply Continuous.inv₀ (continuous_const.add (hs.div_const P))
    intro θ
    have hh : 0 ≤ ∑ k, ‖u θ k‖ ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    change 1 + (∑ k, ‖u θ k‖ ^ 2) / P ≠ 0
    positivity
  exact (Complex.continuous_ofReal.comp hr).mul (hu i)

theorem radialDampingTrace_periodic (P : ℝ) {u : ℝ → ι → ℂ}
    (hu : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) (i : ι) :
    Function.Periodic (radialDampingTrace P u i) (2 * Real.pi) := by
  intro θ
  have he : u (θ + 2 * Real.pi) = u θ := funext (fun i => hu i θ)
  change (reciprocalDamping P (∑ k, ‖u (θ + 2 * Real.pi) k‖ ^ 2) : ℂ) *
    u (θ + 2 * Real.pi) i = _
  rw [he]
  rfl

theorem radialDampingTrace_norm_le {P : ℝ} (hP : 0 < P)
    (u : ℝ → ι → ℂ) (i : ι) (θ : ℝ) :
    ‖radialDampingTrace P u i θ‖ ≤ Real.sqrt P / 2 := by
  let v : PiLp 2 (fun _ : ι => ℂ) := WithLp.toLp 2 (u θ)
  have hv : ‖v‖ ^ 2 = ∑ k, ‖u θ k‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  have hcoord : ‖u θ i‖ ≤ ‖v‖ := PiLp.norm_apply_le v i
  have hs : 0 ≤ ∑ k, ‖u θ k‖ ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  calc
    _ = reciprocalDamping P (∑ k, ‖u θ k‖ ^ 2) * ‖u θ i‖ := by
      simp only [radialDampingTrace, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (reciprocalDamping_pos hP hs)]
    _ ≤ reciprocalDamping P (∑ k, ‖u θ k‖ ^ 2) * ‖v‖ :=
      mul_le_mul_of_nonneg_left hcoord (reciprocalDamping_pos hP hs).le
    _ ≤ _ := by rw [← hv]; exact reciprocalDamping_mul_norm_bound hP (norm_nonneg v)

theorem radialDampingTrace_difference_sq_le {P : ℝ} (hP : 0 < P)
    (u : ℝ → ι → ℂ) (i : ι) (θ t : ℝ) :
    ‖radialDampingTrace P u i θ - radialDampingTrace P u i t‖ ^ 2 ≤
      9 * ∑ k, ‖u θ k - u t k‖ ^ 2 := by
  let v : ℝ → PiLp 2 (fun _ : ι => ℂ) := fun θ => WithLp.toLp 2 (u θ)
  have hv (θ : ℝ) : ‖v θ‖ ^ 2 = ∑ k, ‖u θ k‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  have hd : ‖v θ - v t‖ ^ 2 = ∑ k, ‖u θ k - u t k‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ _
  have he : radialDampingTrace P u i θ - radialDampingTrace P u i t =
      (radialDamping P (v θ) - radialDamping P (v t)) i := by
    simp [radialDampingTrace, radialDamping, hv, v, Complex.real_smul]
  have hc := PiLp.norm_apply_le (radialDamping P (v θ) - radialDamping P (v t)) i
  have hl := (radialDamping_lipschitz (E := PiLp 2 (fun _ : ι => ℂ)) hP).norm_sub_le
    (v θ) (v t)
  have hnorm : ‖radialDampingTrace P u i θ - radialDampingTrace P u i t‖ ≤
      3 * ‖v θ - v t‖ := by
    rw [he]
    exact hc.trans (by simpa using hl)
  have hs := mul_self_le_mul_self (norm_nonneg _) hnorm
  simpa only [← sq, mul_pow, hd, show (3 : ℝ) ^ 2 = 9 by norm_num] using hs

theorem radialDampingTrace_boundaryDSq_le {P : ℝ} (hP : 0 < P)
    {u : ℝ → ι → ℂ} (hu : ∀ i, Continuous (fun θ => u θ i))
    (hp : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) (i : ι) :
    boundaryDSq (fun θ (_ : Unit) => radialDampingTrace P u i θ) ≤
      ENNReal.ofReal 9 * boundaryDSq u :=
  V03Proof.boundaryDSq_le_of_sum_square_bound hu
    (radialDampingTrace_continuous hP hu i) hp (radialDampingTrace_periodic P hp i)
    (by norm_num) (radialDampingTrace_difference_sq_le hP u i)

end Yau.Blueprint.V02Proof
