import Yau.Proofs.C04ClockBasic
import Yau.Proofs.C04Scaling

/-! The clock-rescaling identity for the actual physical time and metric family. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem rescaled_clock_hasDerivAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (ti z : ℝ) (hR : 0 < scalarCurvature (h ti) o)
    (ht : 0 < ti + z / scalarCurvature (h ti) o) :
    HasDerivAt (fun w => ρ o (ti + w / scalarCurvature (h ti) o))
      (scalarCurvature (scaleField (scalarCurvature (h ti) o) hR
        (h (ti + z / scalarCurvature (h ti) o))) o) z := by
  have hp := ((hasDerivAt_id z).div_const (scalarCurvature (h ti) o)).const_add ti
  have hs := (rho_hasDerivAt X o h U P ρ hf o ht).comp z hp
  rw [scalar_scaleField]
  simpa only [Function.comp_def, id_eq, one_div, mul_comm] using hs

theorem rescaled_scalar_eq_clock_ratio (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (ti z : ℝ) (hR : 0 < scalarCurvature (h ti) o)
    (ht : 0 < ti + z / scalarCurvature (h ti) o) :
    scalarCurvature (scaleField (scalarCurvature (h ti) o) hR
      (h (ti + z / scalarCurvature (h ti) o))) o =
      clockSpeed o h (ti + z / scalarCurvature (h ti) o) / (clockSpeed o h ti + z) := by
  rw [scalar_scaleField]
  have hden : clockSpeed o h ti + z =
      scalarCurvature (h ti) o * (ti + z / scalarCurvature (h ti) o) := by
    dsimp only [clockSpeed]
    field_simp
  rw [hden]
  have halg : ∀ R t v : ℝ, R ≠ 0 → t ≠ 0 → R⁻¹ * v = (t * v) / (R * t) := by
    intro R t v hR ht
    field_simp
  exact halg _ _ _ hR.ne' ht.ne'

theorem rescaled_clock_ratio_hasDerivAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (ti z : ℝ) (hR : 0 < scalarCurvature (h ti) o)
    (ht : 0 < ti + z / scalarCurvature (h ti) o) :
    HasDerivAt (fun w => ρ o (ti + w / scalarCurvature (h ti) o))
      (clockSpeed o h (ti + z / scalarCurvature (h ti) o) / (clockSpeed o h ti + z)) z := by
  rw [← rescaled_scalar_eq_clock_ratio X o h ti z hR ht]
  exact rescaled_clock_hasDerivAt X o h U P ρ hf ti z hR ht

end Yau.Proofs.C04Aux
