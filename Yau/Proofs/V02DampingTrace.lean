import Yau.Proofs.V02DampingHilbert
import Yau.Proofs.V03GagliardoVector

/-! The logarithmic damping trace of a genuine finite complex vector has
half-order seminorm controlled by the vector's actual Fourier seminorm. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {ι : Type*} [Fintype ι]

def dampingLogTrace (P : ℝ) (u : ℝ → ι → ℂ) (θ : ℝ) : ℝ :=
  -Real.log (1 + (∑ i, ‖u θ i‖ ^ 2) / P)

theorem dampingLogTrace_contDiff {P : ℝ} (hP : 0 < P) {u : ℝ → ι → ℂ}
    (hu : ∀ i, ContDiff ℝ ∞ (fun θ => u θ i)) :
    ContDiff ℝ ∞ (dampingLogTrace P u) := by
  have hs : ContDiff ℝ ∞ (fun θ => ∑ i, ‖u θ i‖ ^ 2) :=
    ContDiff.sum (fun i _ => (hu i).norm_sq ℂ)
  exact ((contDiff_const.add (hs.div_const P)).log (fun θ => by
    have hh : 0 ≤ ∑ i, ‖u θ i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    positivity)).neg

theorem dampingLogTrace_periodic (P : ℝ) {u : ℝ → ι → ℂ}
    (hu : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) :
    Function.Periodic (dampingLogTrace P u) (2 * Real.pi) := by
  intro θ
  have he : u (θ + 2 * Real.pi) = u θ := funext (fun i => hu i θ)
  change -Real.log (1 + (∑ i, ‖u (θ + 2 * Real.pi) i‖ ^ 2) / P) = _
  rw [he]
  rfl

theorem dampingLogTrace_nonpos {P : ℝ} (hP : 0 < P) (u : ℝ → ι → ℂ) (θ : ℝ) :
    dampingLogTrace P u θ ≤ 0 := by
  have hs : 0 ≤ ∑ i, ‖u θ i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  exact neg_nonpos.mpr (Real.log_nonneg (by linarith [div_nonneg hs hP.le]))

theorem dampingLogTrace_difference_sq_le {P : ℝ} (hP : 0 < P)
    (u : ℝ → ι → ℂ) (θ t : ℝ) :
    ‖(dampingLogTrace P u θ : ℂ) - (dampingLogTrace P u t : ℂ)‖ ^ 2 ≤
      P⁻¹ * ∑ i, ‖u θ i - u t i‖ ^ 2 := by
  letI : InnerProductSpace ℝ (PiLp 2 (fun _ : ι => ℂ)) :=
    InnerProductSpace.rclikeToReal ℂ _
  let v : ℝ → PiLp 2 (fun _ : ι => ℂ) := fun θ => WithLp.toLp 2 (u θ)
  have hn (θ : ℝ) : ‖v θ‖ ^ 2 = ∑ i, ‖u θ i‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ _
  have hd : ‖v θ - v t‖ ^ 2 = ∑ i, ‖u θ i - u t i‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ _
  have hh := (dampingLog_lipschitz (H := PiLp 2 (fun _ : ι => ℂ)) hP).norm_sub_le
    (v θ) (v t)
  rw [Real.coe_toNNReal _ (by positivity)] at hh
  have he : ‖(dampingLogTrace P u θ : ℂ) - (dampingLogTrace P u t : ℂ)‖ =
      ‖Real.log (1 + ‖v θ‖ ^ 2 / P) - Real.log (1 + ‖v t‖ ^ 2 / P)‖ := by
    rw [hn θ, hn t]
    simp only [dampingLogTrace, ← Complex.ofReal_sub, Complex.norm_real,
      neg_sub_neg, norm_sub_rev]
  rw [he]
  have hs := mul_self_le_mul_self (norm_nonneg _) hh
  simpa only [← sq, mul_pow, inv_pow, Real.sq_sqrt hP.le, hd] using hs

theorem dampingLogTrace_boundaryDSq_le {P : ℝ} (hP : 0 < P)
    {u : ℝ → ι → ℂ} (hu : ∀ i, Continuous (fun θ => u θ i))
    (hup : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) :
    scalarDSq (dampingLogTrace P u) ≤ ENNReal.ofReal P⁻¹ * boundaryDSq u := by
  have hs : Continuous (fun θ => ∑ i, ‖u θ i‖ ^ 2) :=
    continuous_finsetSum _ (fun i _ => (hu i).norm.pow 2)
  have hcont : Continuous (dampingLogTrace P u) := by
    apply Continuous.neg
    exact (continuous_const.add (hs.div_const P)).log (fun θ => by
      have hh : 0 ≤ ∑ i, ‖u θ i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      change 1 + (∑ i, ‖u θ i‖ ^ 2) / P ≠ 0
      positivity)
  exact V03Proof.boundaryDSq_le_of_sum_square_bound hu
    (Complex.continuous_ofReal.comp hcont) hup
    (fun θ => congrArg Complex.ofReal (dampingLogTrace_periodic P hup θ))
    (inv_nonneg.mpr hP.le) (dampingLogTrace_difference_sq_le hP u)

end Yau.Blueprint.V02Proof
