import Yau.Proofs.C07LogNormSupport

open scoped ContDiff Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n m : ℕ}

/-- Add one constant holomorphic coordinate, so the vector never vanishes. -/
def augmentNorm (f : ComplexVector n → ComplexVector m) (ε : ℝ)
    (z : ComplexVector n) : ComplexVector (m + 1) :=
  WithLp.toLp 2 (Fin.cons (ε : ℂ) (WithLp.ofLp (f z)))

theorem augmentNorm_sq (f : ComplexVector n → ComplexVector m) (ε : ℝ)
    (z : ComplexVector n) : ‖augmentNorm f ε z‖ ^ 2 = ε ^ 2 + ‖f z‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, augmentNorm, Fin.sum_univ_succ,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem augmentNorm_bounds (f : ComplexVector n → ComplexVector m) {ε : ℝ}
    (hε : 0 ≤ ε) (z : ComplexVector n) :
    ‖f z‖ ≤ ‖augmentNorm f ε z‖ ∧ ‖augmentNorm f ε z‖ ≤ ‖f z‖ + ε := by
  have hsq := augmentNorm_sq f ε z
  constructor <;> nlinarith [norm_nonneg (f z), norm_nonneg (augmentNorm f ε z)]

/-- The logarithms of these genuine holomorphic augmentations are psh on
the complete original open domain, including all zeros of the original map. -/
theorem augmentNorm_log_isPshOn {Ω : Set (ComplexVector n)} (hΩ : IsOpen Ω)
    {f : ComplexVector n → ComplexVector m} (hf : DifferentiableOn ℂ f Ω)
    {ε : ℝ} (hε : 0 < ε) :
    IsPshOn (fun z => (Real.log ‖augmentNorm f ε z‖ : EReal)) Ω := by
  apply log_norm_isPshOn_of_nonvanishing hΩ
  · apply (differentiableOn_piLp 2).mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [augmentNorm, PiLp.toLp_apply, Fin.cons_zero] using
        (differentiableOn_const (ε : ℂ) : DifferentiableOn ℂ (fun _ : ComplexVector n => (ε : ℂ)) Ω)
    · simpa only [augmentNorm, PiLp.toLp_apply, Fin.cons_succ] using
        ((differentiableOn_piLp 2).mp hf j)
  · intro z hz hzero
    have hc := congrArg (fun v : ComplexVector (m + 1) => v 0) hzero
    have hεzero : (ε : ℂ) = 0 := by simpa [augmentNorm] using hc
    exact hε.ne' (Complex.ofReal_eq_zero.mp hεzero)

end Yau.Proofs.C07Aux
