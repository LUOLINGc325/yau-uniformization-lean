import Yau.Proofs.V03DiscSmooth

/-! An extended cotangent disc retains the original admissible closed-disc
predicate by restriction along inverse dilation. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau

variable {n : ℕ} {M : ComplexManifold n}

theorem extendedCotangentDisc_holomorphicOn {f : ℂ → CotangentPoint M}
    (hf : ExtendedCotangentDisc f) :
    ∃ R : ℝ, 1 < R ∧ CotangentHolomorphicOn f (Metric.closedBall (0 : ℂ) R) := by
  obtain ⟨R, hR, hg⟩ := hf
  have hRp : 0 < R := lt_trans zero_lt_one hR
  have hRn : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hRp
  have hcomp := (V03Proof.cotangentDisc_holomorphicOn hg).comp
    (g := fun z : ℂ => z / (R : ℂ)) (by fun_prop)
    (T := Metric.closedBall (0 : ℂ) R) (by
      intro z hz
      simp only [Metric.mem_closedBall, dist_zero_right] at hz ⊢
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRp]
      exact (div_le_one hRp).mpr hz)
  refine ⟨R, hR, ?_⟩
  convert hcomp using 1
  funext z
  congr 1
  exact (mul_div_cancel₀ z hRn).symm

theorem extendedCotangentDisc_cotangentDisc {f : ℂ → CotangentPoint M}
    (hf : ExtendedCotangentDisc f) : CotangentDisc f := by
  obtain ⟨R, hR, hfR⟩ := extendedCotangentDisc_holomorphicOn hf
  exact (hfR.comp (g := fun z : ℂ => z) contDiff_id
    (fun _ hz => Metric.closedBall_subset_closedBall hR.le hz)).cotangentDisc

end Yau.Blueprint.D05Proof
