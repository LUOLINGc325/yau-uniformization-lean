import Yau.Proofs.P06SpectralReal

noncomputable section
open ContinuousLinearMap
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus

namespace Yau.NodeProofs.P06Aux.Spectral
open Yau.LeafProofs.L19Aux ComplexHilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (R : H →L[ℝ] H) (hRs : R.IsSymmetric)
  (hRp : ∀ x, 0 ≤ inner ℝ (R x) x) (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R)

theorem complexHeat_commute_resolvent (t : ℝ) :
    Commute (complexHeat R hRs hRp hRb hRi t) (complexResolvent R hRs hRp hRb hRi) := by
  unfold complexHeat
  split_ifs with ht
  · have hc := cfc_commute_cfc (scalarHeatMultiplier t) (fun s : ℝ => s)
      (complexResolvent R hRs hRp hRb hRi)
    simpa only [cfc_id' ℝ _ (complexResolvent_selfAdjoint R hRs hRp hRb hRi)] using hc
  · exact Commute.one_left _

theorem complexHeatInverse_commute_resolvent (t : ℝ) :
    Commute (complexHeatInverse R hRs hRp hRb hRi t) (complexResolvent R hRs hRp hRb hRi) := by
  have hc := cfc_commute_cfc (scalarHeatInverseMultiplier t) (fun s : ℝ => s)
    (complexResolvent R hRs hRp hRb hRi)
  simpa only [complexHeatInverse,
    cfc_id' ℝ _ (complexResolvent_selfAdjoint R hRs hRp hRb hRi)] using hc

theorem realHeat_commute_resolvent (t : ℝ) : Commute (realHeat R hRs hRp hRb hRi t) R := by
  apply ContinuousLinearMap.ext
  intro x
  have hc := congrArg (fun A : ComplexHilbert H →L[ℂ] ComplexHilbert H => re (A (ofRealCLM x)))
    (complexHeat_commute_resolvent R hRs hRp hRb hRi t).eq
  simpa only [mul_apply_eq_comp, complexResolvent, complexify_ofReal,
    complexify_re, realHeat, comp_apply, coe_restrictScalars', reCLM_apply] using hc

theorem realHeatInverse_commute_resolvent (t : ℝ) :
    Commute (realHeatInverse R hRs hRp hRb hRi t) R := by
  apply ContinuousLinearMap.ext
  intro x
  have hc := congrArg (fun A : ComplexHilbert H →L[ℂ] ComplexHilbert H => re (A (ofRealCLM x)))
    (complexHeatInverse_commute_resolvent R hRs hRp hRb hRi t).eq
  simpa only [mul_apply_eq_comp, complexResolvent, complexify_ofReal,
    complexify_re, realHeatInverse, comp_apply, coe_restrictScalars', reCLM_apply] using hc

theorem realHeat_nat_mul {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    realHeat R hRs hRp hRb hRi ((m : ℝ) * t) = (realHeat R hRs hRp hRb hRi t) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, add_mul, one_mul,
      realHeat_add R hRs hRp hRb hRi (mul_nonneg (Nat.cast_nonneg m) ht) ht, ih, pow_succ]

/-- Every positive-time heat operator factors through every finite power of
the actual resolvent. This gives genuine higher generator domains. -/
theorem realHeat_factor_power {t : ℝ} (ht : 0 < t) (m : ℕ) (hm : 0 < m) :
    realHeat R hRs hRp hRb hRi t = R ^ m *
      (realHeatInverse R hRs hRp hRb hRi (t / m)) ^ m := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have htdiv : 0 < t / m := div_pos ht hmR
  have heq : (m : ℝ) * (t / m) = t := by field_simp
  conv_lhs => rw [← heq, realHeat_nat_mul R hRs hRp hRb hRi htdiv.le]
  rw [realHeat_factor R hRs hRp hRb hRi htdiv]
  exact (realHeatInverse_commute_resolvent R hRs hRp hRb hRi (t / m)).symm.mul_pow m

end Yau.NodeProofs.P06Aux.Spectral
