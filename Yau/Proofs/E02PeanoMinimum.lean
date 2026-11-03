import Yau.Proofs.E02PeanoFirst

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Second-order necessary positivity for an actual Peano tensor at a
local minimum. No differentiability of the first derivative is assumed. -/
theorem realSecondJet_localMin_quadratic_nonneg {f : E → ℝ} {x : E}
    {p : E →L[ℝ] ℝ} {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : RealSecondJet f x p A) (hmin : IsLocalMin f x) : ∀ v, 0 ≤ A v v := by
  have hp : p = 0 := realSecondJet_localMin_linear_zero hf hmin
  intro v
  by_cases hv : v = 0
  · subst v
    simp
  by_contra h
  have ha : A v v < 0 := lt_of_not_ge h
  have hn : 0 < ‖v‖^2 := pow_pos (norm_pos_iff.mpr hv) 2
  let ε := -(A v v)/(4*‖v‖^2)
  have hε : 0 < ε := div_pos (neg_pos.mpr ha) (by positivity)
  have hεRel : ε*(4*‖v‖^2) = -(A v v) := div_mul_cancel₀ _ (by positivity)
  have hCoeff : (1/2)*A v v+ε*‖v‖^2 = A v v/4 := by nlinarith
  have hBound := realSecondJet_quadratic_bounds hf hε
  have hCont : Continuous (fun t : ℝ => x+t • v) := by fun_prop
  have hPath0 : Tendsto (fun t : ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using hCont.tendsto 0
  have hPath : Tendsto (fun t : ℝ => x+t • v) (𝓝[>] 0) (𝓝 x) := hPath0.mono_left inf_le_left
  have hAll : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ f x ≤ f (x+t • v) ∧
      f (x+t • v) ≤ f x+(1/2)*A (t • v) (t • v)+ε*‖t • v‖^2 := by
    filter_upwards [self_mem_nhdsWithin,hPath.eventually hmin,hPath.eventually hBound]
      with t ht hm hb
    refine ⟨ht,hm,?_⟩
    have hsub : x+t • v-x = t • v := by abel
    simpa only [hsub,hp,ContinuousLinearMap.zero_apply,add_zero] using hb.2
  obtain ⟨t,ht,hm,hup⟩ := hAll.exists
  have hScaleA : A (t • v) (t • v) = t^2*A v v := by
    simp only [map_smul,smul_apply,smul_eq_mul,pow_two,mul_assoc]
  have hScaleN : ‖t • v‖^2 = t^2*‖v‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hNeg : (1/2)*(t^2*A v v)+ε*(t^2*‖v‖^2) < 0 := by
    calc
      _ = t^2*((1/2)*A v v+ε*‖v‖^2) := by ring
      _ = t^2*(A v v/4) := by rw [hCoeff]
      _ < 0 := mul_neg_of_pos_of_neg (pow_pos ht 2) (by linarith)
  rw [hScaleA,hScaleN] at hup
  linarith

end Yau.NodeProofs.E02Aux
