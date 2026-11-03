import Yau.Proofs.V01ContactCylinder

/-! The physical-time derivative of the genuine smooth support is a
continuous field, so the original ordered center convergence controls it. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.Blueprint.V01Proof
variable {n : ℕ}

def coordinateTimeSlope (ψ : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (p : ComplexVector n × ComplexVector n × ℝ) : ℝ :=
  deriv (fun t => ψ (p.1, p.2.1, t)) p.2.2

theorem coordinateTimeSlope_eq_fderiv
    {ψ : ComplexVector n × ComplexVector n × ℝ → ℝ}
    (p : ComplexVector n × ComplexVector n × ℝ) (hψ : DifferentiableAt ℝ ψ p) :
    coordinateTimeSlope ψ p = fderiv ℝ ψ p (0, 0, 1) := by
  have hline : HasDerivAt (fun t : ℝ => (p.1, p.2.1, t))
      (0, 0, 1) p.2.2 :=
    (hasDerivAt_const p.2.2 p.1).prodMk
      ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id p.2.2))
  have ht : HasDerivAt (fun t => ψ (p.1, p.2.1, t))
      (fderiv ℝ ψ p (0, 0, 1)) p.2.2 := by
    simpa only [Function.comp_def] using
      hψ.hasFDerivAt.comp_hasDerivAt p.2.2 (by simpa using hline)
  exact ht.deriv

theorem coordinateTimeSlope_continuous
    {ψ : ComplexVector n × ComplexVector n × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (coordinateTimeSlope ψ) := by
  have heq : coordinateTimeSlope ψ = fun p => fderiv ℝ ψ p (0, 0, 1) := by
    funext p
    exact coordinateTimeSlope_eq_fderiv p (hψ.differentiable one_ne_zero p)
  rw [heq]
  exact (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem localizedZero_continuousAt
    {E : Type*} [NormedAddCommGroup E]
    {p : ℕ → ℝ → ℕ → E} {a : E}
    (hp : LocalizedZero (fun j ε ν => ‖p j ε ν - a‖))
    (f : E → ℝ) (hf : ContinuousAt f a) :
    LocalizedZero (fun j ε ν => f (p j ε ν) - f a) := by
  intro r hr
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp hf r hr
  filter_upwards [hp (δ / 2) (half_pos hδ)] with j hj
  filter_upwards [hj] with ε hε
  filter_upwards [hε] with ν hν
  have hn : ‖p j ε ν - a‖ ≤ δ / 2 := by simpa only [abs_norm] using hν
  have hd : dist (p j ε ν) a < δ := by rw [dist_eq_norm]; linarith
  simpa only [Real.dist_eq] using (hfδ hd).le

theorem localized_time_slope
    {ψ : ComplexVector n × ComplexVector n × ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    {p : ℕ → ℝ → ℕ → CotangentCoord n × ℝ} {a : CotangentCoord n × ℝ}
    (hp : LocalizedZero (fun j ε ν => ‖p j ε ν - a‖)) :
    LocalizedZero (fun j ε ν => coordinateTimeSlope ψ (contactAssoc (p j ε ν)) -
      coordinateTimeSlope ψ (contactAssoc a)) := by
  let f : CotangentCoord n × ℝ → ℝ := fun y => coordinateTimeSlope ψ (contactAssoc y)
  have hf : Continuous f :=
    (coordinateTimeSlope_continuous hψ).comp (contactAssoc (n := n)).continuous
  exact localizedZero_continuousAt (E := CotangentCoord n × ℝ)
    (p := p) (a := a) hp f hf.continuousAt

end Yau.Blueprint.V01Proof
