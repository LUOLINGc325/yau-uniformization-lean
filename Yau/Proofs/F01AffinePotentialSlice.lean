import Yau.Proofs.F01AffinePotentialNormalization

/-! The normalized Levi identity is local to its spatial slice.
The clock chain rule works on the actual source and target time sets.
Neither identity assumes a future-time neighborhood. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem leviC_affineParabolicPotential_slice {ρ τ : ℝ} {c : Space n}
    {u : Point n → ℝ} {p : Point n} (hρ : ρ ≠ 0)
    (hu : ContDiffAt ℝ 2 (fun z => u (z, (affineParabolicPoint ρ c τ p).2))
      (affineParabolicPoint ρ c τ p).1) :
    leviC (fun z => affineParabolicPotential ρ c τ u (z, p.2)) p.1 =
      leviC (fun z => u (z, (affineParabolicPoint ρ c τ p).2)) (affineParabolicPoint ρ c τ p).1 := by
  have hAffine : ContDiffAt ℝ 2 (fun z : Space n => ρ • z + c) p.1 := by fun_prop
  have hComp := hu.comp p.1 hAffine
  have hNew : ContDiffAt ℝ 2 (fun z => affineParabolicPotential ρ c τ u (z, p.2)) p.1 := by
    change ContDiffAt ℝ 2 (fun z => (ρ ^ 2)⁻¹ * u (ρ • z + c, τ + ρ ^ 2 * p.2)) p.1
    exact contDiffAt_const.mul hComp
  rw [← leviSecondMatrixCLM_eq_native hNew, ← leviSecondMatrixCLM_eq_native hu]
  change leviSecondMatrixCLM (spatialDD (affineParabolicPotential ρ c τ u) p) =
    leviSecondMatrixCLM (spatialDD u (affineParabolicPoint ρ c τ p))
  rw [spatialDD_affineParabolicPotential hρ]

theorem affine_potential_clock_jet {I J : Set ℝ} {ρ τ : ℝ} {c x : Space n}
    {u P : Point n → ℝ} {t : ℝ} (hρ : ρ ≠ 0) (ht : t ∈ I)
    (hClock : MapsTo (fun s : ℝ => τ + ρ ^ 2 * s) I J)
    (hJet : ∀ s ∈ J, HasDerivWithinAt (fun r => u (ρ • x + c, r))
      (P (ρ • x + c, s)) J s) :
    HasDerivWithinAt (fun s => affineParabolicPotential ρ c τ u (x, s))
      (P (affineParabolicPoint ρ c τ (x, t))) I t := by
  have hArg : HasDerivWithinAt (fun s : ℝ => τ + ρ ^ 2 * s) (ρ ^ 2) I t := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id t).const_mul (ρ ^ 2)).const_add τ).hasDerivWithinAt
  have hc := ((hJet _ (hClock ht)).comp t hArg hClock).const_mul ((ρ ^ 2)⁻¹)
  convert hc using 1
  · rfl
  · dsimp only [affineParabolicPoint]
    field_simp [pow_ne_zero 2 hρ]

end Yau.NodeProofs.F01Aux
