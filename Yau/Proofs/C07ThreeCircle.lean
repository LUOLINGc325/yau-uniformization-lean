import Mathlib

/-! Vector-valued three-circle interpolation, obtained from Mathlib's
three-lines theorem by the actual exponential parametrization of a line. -/

namespace Yau.Proofs.C07Aux

open Set Complex.HadamardThreeLines

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The exponential parametrization gives the three-circle estimate for a
holomorphic vector-valued map.  The outer circle lies strictly inside the
holomorphic domain, so continuity on both boundary circles is automatic. -/
theorem three_circle_on_line {f : E → G} {R l u x A B : ℝ} {v : E}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hlu : l < u) (huR : Real.exp u < R) (hx : x ∈ Icc l u)
    (hv : ‖v‖ = 1)
    (hA : ∀ z : E, ‖z‖ = Real.exp l → ‖f z‖ ≤ A)
    (hB : ∀ z : E, ‖z‖ ≤ Real.exp u → ‖f z‖ ≤ B) :
    ‖f ((Real.exp x : ℂ) • v)‖ ≤
      A ^ (1 - (x - l) / (u - l)) * B ^ ((x - l) / (u - l)) := by
  let p : ℂ → E := fun w => Complex.exp w • v
  have hp : Differentiable ℂ p := Complex.differentiable_exp.smul_const v
  have hpn (w : ℂ) : ‖p w‖ = Real.exp w.re := by
    simp [p, norm_smul, hv, Complex.norm_exp]
  have hclosed : closure (verticalStrip l u) ⊆ verticalClosedStrip l u := by
    apply closure_minimal
    · intro w hw
      exact ⟨hw.1.le, hw.2.le⟩
    · exact isClosed_Icc.preimage Complex.continuous_re
  have hmaps : MapsTo p (verticalClosedStrip l u) (Metric.ball 0 R) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right, hpn]
    exact (Real.exp_le_exp.mpr hw.2).trans_lt huR
  have hd : DiffContOnCl ℂ (f ∘ p) (verticalStrip l u) := by
    apply DifferentiableOn.diffContOnCl
    exact hf.comp hp.differentiableOn (hmaps.mono_left hclosed)
  have hbounded : BddAbove ((norm ∘ (f ∘ p)) '' verticalClosedStrip l u) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hB _ (by rw [hpn]; exact Real.exp_le_exp.mpr hw.2)
  have hleft : ∀ w ∈ Complex.re ⁻¹' {l}, ‖(f ∘ p) w‖ ≤ A := by
    intro w hw
    exact hA _ (by rw [hpn]; congr 1)
  have hright : ∀ w ∈ Complex.re ⁻¹' {u}, ‖(f ∘ p) w‖ ≤ B := by
    intro w hw
    exact hB _ (by rw [hpn]; exact Real.exp_le_exp.mpr (le_of_eq hw))
  have h := norm_le_interp_of_mem_verticalClosedStrip' hlu
    (z := (x : ℂ)) (by exact hx) hd hbounded hleft hright
  simpa only [Function.comp_apply, p, ← Complex.ofReal_exp, Complex.ofReal_re] using h

end Yau.Proofs.C07Aux
