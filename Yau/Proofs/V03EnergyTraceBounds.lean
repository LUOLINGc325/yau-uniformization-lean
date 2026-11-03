import Yau.Proofs.V03VectorAreaFourier
import Yau.Proofs.V03FrameEnergyBound

/-! All three actual traces used by the symbol estimate are bounded by
the original computed energy, with exact area normalization. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem euclideanArea_le_variationEnergy (d : VariationData X q) (j : ℕ) (F : VariationDisc X) :
    euclideanArea (fun ζ => d.G (F.f ζ)) ≤ variationEnergy d j F := by
  unfold variationEnergy
  exact (le_add_left le_rfl).trans ((le_add_right le_rfl).trans
    ((le_add_right le_rfl).trans (le_add_right le_rfl)))

theorem clockArea_le_variationEnergy (d : VariationData X q) (j : ℕ) (F : VariationDisc X) :
    clockArea F ≤ variationEnergy d j F := by
  unfold variationEnergy
  exact (le_add_left le_rfl).trans (le_add_right le_rfl)

theorem admissible_three_traces_le_energy {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {F : VariationDisc X} {E : ℂ → CotangentMatrix n}
    (hF : AdmissibleVariationDisc d j F) (hE : NormalizedDiscFrame d.G F.f E) :
    matrixDSq (fun θ => ambientFrame d.G F.f E (circlePoint θ)) +
      boundaryDSq (fun θ b => d.G (F.f (circlePoint θ)) b) +
        boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ)) ≤
      ENNReal.ofReal (3 * (2 * Real.pi)⁻¹) * variationEnergy d j F := by
  have hG := boundaryDSq_vector_eq_inverse_area
    (cotangentDisc_ambient_contDiffOn hF.1 hd.2.2.2.2.1.1)
  have hw := boundaryDSq_scalar_eq_inverse_area hF.2.1
  have hframe := normalizedFrame_matrixDSq_le_energy hd j hE
  have hamb : boundaryDSq (fun θ b => d.G (F.f (circlePoint θ)) b) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹) * variationEnergy d j F := by
    rw [hG]
    gcongr
    exact euclideanArea_le_variationEnergy d j F
  have hclock : boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ)) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹) * variationEnergy d j F := by
    rw [hw]
    gcongr
    exact clockArea_le_variationEnergy d j F
  calc
    _ ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹) * variationEnergy d j F +
        ENNReal.ofReal ((2 * Real.pi)⁻¹) * variationEnergy d j F +
          ENNReal.ofReal ((2 * Real.pi)⁻¹) * variationEnergy d j F :=
      add_le_add (add_le_add hframe hamb) hclock
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring

end Yau.Blueprint.V03Proof
