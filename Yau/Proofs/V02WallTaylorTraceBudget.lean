import Yau.Proofs.V02WallTaylorAuxiliary
import Yau.Proofs.V03CoefficientBoundaryEnergy

/-! The genuine ambient/outer-phase/coefficient boundary data have one
fixed energy budget. The parameter is constant along the boundary circle. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem closedDisc_circle_contDiff {f : ℂ → E}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiff ℝ ∞ (fun θ => f (circlePoint θ)) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  apply contDiffWithinAt_univ.mp
  exact ((hf _ (circlePoint_mem_closedBall θ)).restrict_scalars ℝ).comp θ
    circlePoint_contDiff.contDiffAt.contDiffWithinAt (fun t _ => circlePoint_mem_closedBall t)

variable {n q b : ℕ} {X : KahlerManifold n}

theorem actual_aux_encode_continuous {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (a : ℕ) (z : ℂ)
    {c : ℂ → Fin b → ℂ}
    (hc : ∀ k, ContDiffOn ℂ ∞ (fun ζ => c ζ k) (Metric.closedBall (0 : ℂ) 1)) :
    Continuous (fun θ => incrementAuxEncode (z, (outerWallPhase d j a F.f θ, c (circlePoint θ)))) := by
  have hcc := closedDisc_circle_contDiff (contDiffOn_pi.mpr hc)
  exact incrementAuxEncode_contDiff.continuous.comp
    (continuous_const.prodMk ((outerWallPhase_contDiff hd hF a).continuous.prodMk hcc.continuous))

theorem actual_aux_encode_periodic (d : VariationData X q) (j a : ℕ)
    (F : VariationDisc X) (c : ℂ → Fin b → ℂ) (z : ℂ) :
    Function.Periodic
      (fun θ => incrementAuxEncode (z, (outerWallPhase d j a F.f θ, c (circlePoint θ))))
      (2 * Real.pi) := by
  intro θ
  change incrementAuxEncode (z, (outerWallPhase d j a F.f (θ + 2 * Real.pi), c (circlePoint (θ + 2 * Real.pi)))) = _
  rw [outerWallPhase_periodic d j a F.f θ]
  have hc : c (circlePoint (θ + 2 * Real.pi)) = c (circlePoint θ) := circleTrace_periodic c θ
  rw [hc]

def combinedTraceBudget (a : ℕ) (E0 D0 : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * E0 + ((a : ℝ) ^ 2 * E0 + D0)

theorem combinedTraceBudget_nonneg (a : ℕ) {E0 D0 : ℝ} (hE0 : 0 ≤ E0) (hD0 : 0 ≤ D0) :
    0 ≤ combinedTraceBudget a E0 D0 := by dsimp [combinedTraceBudget]; positivity

theorem actual_combined_trace_budget {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {E0 D0 : ℝ} (hE0 : 0 ≤ E0) (hD0 : 0 ≤ D0)
    (hE : (variationEnergy d j F).toReal ≤ E0) {c : ℂ → Fin b → ℂ}
    (hcD : boundaryDSq (fun θ k => c (circlePoint θ) k) ≤ ENNReal.ofReal D0) (z : ℂ) :
    boundaryDSq (fun θ k => d.G (F.f (circlePoint θ)) k) +
      boundaryDSq (fun θ i => incrementAuxEncode
        (z, (outerWallPhase d j a F.f θ, c (circlePoint θ))) i) ≤
      ENNReal.ofReal (combinedTraceBudget a E0 D0) := by
  have henergy : variationEnergy d j F ≤ ENNReal.ofReal E0 :=
    (ENNReal.le_ofReal_iff_toReal_le hF.2.2.2.2.2.2.2.2 hE0).mpr hE
  have hG : boundaryDSq (fun θ k => d.G (F.f (circlePoint θ)) k) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * E0) := by
    rw [boundaryDSq_vector_eq_inverse_area (cotangentDisc_ambient_contDiffOn hF.1 hd.2.2.2.2.1.1)]
    calc
      _ ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹) * ENNReal.ofReal E0 := by
        gcongr
        exact (euclideanArea_le_variationEnergy d j F).trans henergy
      _ = _ := (ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹)).symm
  have hphase := outerWallPhase_uniform_boundaryDSq_le hd hF a hE0 hE
  rw [boundaryDSq_incrementAuxEncode_const_parameter]
  calc
    _ ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ * E0) +
        (ENNReal.ofReal ((a : ℝ) ^ 2 * E0) + ENNReal.ofReal D0) :=
      add_le_add hG (add_le_add hphase hcD)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ (a : ℝ) ^ 2 * E0) hD0,
        ← ENNReal.ofReal_add (by positivity : 0 ≤ (2 * Real.pi)⁻¹ * E0) (by positivity)]
      rfl

end Yau.Blueprint.V02WallTaylorProof
