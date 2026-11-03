import Yau.Proofs.F05BootstrapDatumCoefficients
import Yau.Proofs.F05BootstrapSchauderLinear

/-! Subtracting the actual smooth physical datum preserves the full
operator and gives the exact zero-trace nonlinear equation. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_datum_exp_mul (u p : ℝ) : Real.exp (-(u-p))*Real.exp (-p) = Real.exp (-u) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem F05_datum_principal_identity (u p : Point n → ℝ) (A : Point n → Mat n) :
    (fun z => Real.exp (-(u z-p z)) • F05DatumPrincipal p A z) =
      (fun z => Real.exp (-u z) • A z) := by
  funext z
  simp only [F05DatumPrincipal,smul_smul,F05_datum_exp_mul]

theorem F05_datum_drift_identity (u p : Point n → ℝ) (B : Point n → RIdx n → ℝ) :
    (fun z j => Real.exp (-(u z-p z))*F05DatumDrift p B z j) =
      (fun z j => Real.exp (-u z)*B z j) := by
  funext z j
  rw [F05DatumDrift,← mul_assoc,F05_datum_exp_mul]

theorem F05_subtract_datum_equation {ν : Option (RIdx n)} {T : ℝ}
    (A : Point n → Mat n) (B : Point n → RIdx n → ℝ) (R p u : Point n → ℝ)
    (hp : ContDiffOn ℝ ∞ p (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hu : F05RelC2 (F05PosSpace ν) (Ioc 0 T) u)
    (hPDE : ∀ z ∈ F05PosPatch ν T,
      F05RelOp (F05PosSpace ν) (Ioc 0 T) (fun z => Real.exp (-u z) • A z)
        (fun z j => Real.exp (-u z)*B z j) u z = (1-Real.exp (-u z))*R z) :
    ∀ z ∈ F05PosPatch ν T,
      F05RelOp (F05PosSpace ν) (Ioc 0 T)
        (fun z => Real.exp (-(u z-p z)) • F05DatumPrincipal p A z)
        (fun z j => Real.exp (-(u z-p z))*F05DatumDrift p B z j)
        (fun z => u z-p z) z =
      Real.exp (-(u z-p z))*F05DatumSource p A B R z+F05DatumFree T p R z := by
  have hPC2 := F05_smooth_background_relative_c2 (ν := ν) hp
  have hPJets := F05_smooth_background_relative_jets (ν := ν) hp
  intro z hz
  rw [F05_datum_principal_identity,F05_datum_drift_identity,
    F05_relative_operator_sub (F05_posSpace_uniqueDiffOn ν) hu hPC2 _ _ hz,hPDE z hz]
  have hSecond : (∑ j,∑ k,(Real.exp (-u z)*A z j k)*spatialDD p z (realVec j) (realVec k)) =
      Real.exp (-u z)*(∑ j,∑ k,A z j k*spatialDD p z (realVec j) (realVec k)) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hFirst : (∑ j,(Real.exp (-u z)*B z j)*spatialD p z (realVec j)) =
      Real.exp (-u z)*(∑ j,B z j*spatialD p z (realVec j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold F05RelOp F05DatumSource F05DatumFree
  rw [hPJets.1 hz,hPJets.2 hz]
  simp only [Matrix.smul_apply,smul_eq_mul]
  rw [hSecond,hFirst,← mul_assoc,F05_datum_exp_mul]
  change (1-Real.exp (-u z))*R z-
      (F05RelT (Ioc 0 T) p z-Real.exp (-u z)*(∑ j,∑ k,A z j k*spatialDD p z (realVec j) (realVec k))-
        Real.exp (-u z)*(∑ j,B z j*spatialD p z (realVec j))) = _
  change _ = Real.exp (-u z)*((∑ j,∑ k,A z j k*spatialDD p z (realVec j) (realVec k))+
    (∑ j,B z j*spatialD p z (realVec j))-R z)+(R z-F05RelT (Ioc 0 T) p z)
  ring

end Yau.Proofs.F05Aux
