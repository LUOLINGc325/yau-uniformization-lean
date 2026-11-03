import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Compact

/-! Finite actual jet suprema on the already fixed compact radius. These
numbers are only intermediate unknowns in the radial absorption inequalities;
the radius is not chosen from a higher derivative of the individual field. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def compactJetField (f : E → F) (hf : ContDiff ℝ ∞ f) (m : ℕ) (ρ : ℝ) :
    C(Metric.closedBall (0 : E) ρ, E [×m]→L[ℝ] F) :=
  ⟨fun x => iteratedFDeriv ℝ m f x,
    (ContDiff.continuous_iteratedFDeriv (show (m : ℕ∞ω) ≤ ∞ by simp) hf).comp
      continuous_subtype_val⟩

def compactJetNorm (f : E → F) (hf : ContDiff ℝ ∞ f) (m : ℕ) (ρ : ℝ) : ℝ := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  letI : CompactSpace (Metric.closedBall (0 : E) ρ) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) ρ)
  exact ‖compactJetField f hf m ρ‖

theorem compactJetNorm_nonneg (f : E → F) (hf : ContDiff ℝ ∞ f) (m : ℕ) (ρ : ℝ) :
    0 ≤ compactJetNorm f hf m ρ := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  letI : CompactSpace (Metric.closedBall (0 : E) ρ) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) ρ)
  exact norm_nonneg (compactJetField f hf m ρ)

theorem norm_iteratedFDeriv_le_compactJetNorm (f : E → F) (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (ρ : ℝ) {x : E} (hx : x ∈ Metric.closedBall (0 : E) ρ) :
    ‖iteratedFDeriv ℝ m f x‖ ≤ compactJetNorm f hf m ρ := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  letI : CompactSpace (Metric.closedBall (0 : E) ρ) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) ρ)
  exact (compactJetField f hf m ρ).norm_coe_le_norm ⟨x, hx⟩

theorem compactJetNorm_le (f : E → F) (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (ρ C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) ρ, ‖iteratedFDeriv ℝ m f x‖ ≤ C) :
    compactJetNorm f hf m ρ ≤ C := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  letI : CompactSpace (Metric.closedBall (0 : E) ρ) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) ρ)
  exact ((compactJetField f hf m ρ).norm_le hC).mpr (fun x => hb x x.property)

end Yau.Blueprint.C02Proof
