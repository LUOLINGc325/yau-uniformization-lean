import Yau.Proofs.V03GaussPositive

/-! The literal normalized-frame seminorm condition is controlled by the
actual Gauss summand of the original full energy. -/

open scoped Topology Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem gaussSummand_le_variationEnergy (d : VariationData X q) (j : ℕ) (F : VariationDisc X) :
    ENNReal.ofReal (gaussArea d.G F.f) ≤ variationEnergy d j F := by
  unfold variationEnergy
  exact (le_add_left le_rfl).trans ((le_add_right le_rfl).trans (le_add_right le_rfl))

theorem normalizedFrame_matrixDSq_le_energy {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) {F : VariationDisc X} {E : ℂ → CotangentMatrix n}
    (hE : NormalizedDiscFrame d.G F.f E) :
    matrixDSq (fun θ => ambientFrame d.G F.f E (circlePoint θ)) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹) * variationEnergy d j F := by
  rw [hE.2.2.2, div_eq_mul_inv,
    ENNReal.ofReal_mul (gaussArea_nonneg_of_immersion hd.2.2.2.2.1 F.f)]
  rw [mul_comm]
  gcongr
  exact gaussSummand_le_variationEnergy d j F

end Yau.Blueprint.V03Proof
