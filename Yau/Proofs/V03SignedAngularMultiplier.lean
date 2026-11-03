import Yau.Proofs.V03DirichletOperator

/-! A norm-one signed Fourier multiplier realizes the genuine boundary
angular derivative pairing at every integer frequency. -/

open scoped Topology lp

noncomputable section
namespace Yau.Blueprint.V03Proof

def signedAngularMultiplier (k : ℤ) : ℂ := if 0 ≤ k then Complex.I else -Complex.I

theorem signedAngularMultiplier_norm (k : ℤ) : ‖signedAngularMultiplier k‖ = 1 := by
  unfold signedAngularMultiplier
  split_ifs <;> simp

theorem signedAngularMultiplier_abs (k : ℤ) :
    signedAngularMultiplier k * ((|(k : ℝ)| : ℝ) : ℂ) = Complex.I * (k : ℂ) := by
  by_cases hk : 0 ≤ k
  · rw [signedAngularMultiplier, if_pos hk, abs_of_nonneg (by exact_mod_cast hk)]
    simp only [Complex.ofReal_intCast]
  · have hkr : (k : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hk
    rw [signedAngularMultiplier, if_neg hk, abs_of_neg hkr]
    simp only [Complex.ofReal_neg, Complex.ofReal_intCast]
    ring

def signedAngularMap : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ) :=
  lp.mapCLM 2 (fun k => signedAngularMultiplier k • ContinuousLinearMap.id ℂ ℂ)
    zero_le_one (fun k => by
      simp only [norm_smul, ContinuousLinearMap.norm_id, signedAngularMultiplier_norm, mul_one]
      exact le_rfl)

theorem signedAngularMap_norm_le : ‖signedAngularMap‖ ≤ 1 := lp.norm_mapCLM_le 2 _ zero_le_one _

theorem signedAngularMap_apply (u : ℓ²(ℤ, ℂ)) (k : ℤ) :
    signedAngularMap u k = signedAngularMultiplier k * u k := rfl

theorem signedAngularMap_norm_apply_le (u : ℓ²(ℤ, ℂ)) : ‖signedAngularMap u‖ ≤ ‖u‖ := by
  simpa only [one_mul] using signedAngularMap.le_of_opNorm_le signedAngularMap_norm_le u

end Yau.Blueprint.V03Proof
