import Yau.Proofs.V03OuterPhase
import Yau.Proofs.V03OuterUniqueness

/-! The actual original wall outer function supplies all scalar spray data
and a boundary Dirichlet budget depending only on the original energy. -/

open scoped Topology ContDiff
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem original_outer_properties {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (a : ℕ) :
    ContDiffOn ℂ ∞ (outerCandidate (logTrace d j F.f) a) (closedBall 0 1) ∧
      (outerCandidate (logTrace d j F.f) a 0).im = 0 ∧
      (outerCandidate (logTrace d j F.f) a 0).re = outerCenter d j a F ∧
      (∀ θ, ‖outerCandidate (logTrace d j F.f) a (circlePoint θ)‖ =
        wallPower d j a (F.f (circlePoint θ))) ∧
      ∀ ζ ∈ closedBall (0 : ℂ) 1, ‖outerCandidate (logTrace d j F.f) a ζ‖ ≤ 1 := by
  have hh := outerCandidate_contDiffOn (admissible_logTrace_contDiff hd hF)
    (logTrace_periodic d j F) a
  refine ⟨hh, (outerCandidate_center_phase _ a).1, ?_,
    outerCandidate_logTrace_modulus hd hF a, ?_⟩
  · rw [outerCandidate_logTrace_zero]
    simp
  · apply norm_le_of_circle_bound hh
    intro θ
    rw [outerCandidate_logTrace_modulus hd hF a θ]
    exact (admissible_wallPower_bounds hd hF a θ).2

theorem original_outer_boundary_budget {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (E₀ : ℝ) :
    ∀ F : VariationDisc X, AdmissibleVariationDisc d j F →
      (variationEnergy d j F).toReal ≤ E₀ →
      boundaryDSq (fun θ (_ : Unit) =>
        outerCandidate (logTrace d j F.f) a (circlePoint θ)) ≤
          ENNReal.ofReal (4 * (a : ℝ) ^ 2 * max E₀ 0) := by
  intro F hF hE
  have hfin := hF.2.2.2.2.2.2.2.2
  have hlogfin := (energy_components_ne_top hfin).2.2.2
  have hlog : scalarDSq (logTrace d j F.f) ≤ ENNReal.ofReal (max E₀ 0) := by
    rw [← ENNReal.ofReal_toReal hlogfin]
    exact ENNReal.ofReal_le_ofReal
      (((logSeminorm_toReal_le_energy hfin).trans hE).trans (le_max_left _ _))
  calc
    _ ≤ ENNReal.ofReal (4 * (a : ℝ) ^ 2) * scalarDSq (logTrace d j F.f) :=
      outerCandidate_boundaryDSq_le (admissible_logTrace_contDiff hd hF)
        (logTrace_periodic d j F) (admissible_logTrace_nonpos hd hF) a
    _ ≤ ENNReal.ofReal (4 * (a : ℝ) ^ 2) * ENNReal.ofReal (max E₀ 0) :=
      mul_le_mul_right hlog _
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

end Yau.Blueprint.V02Proof
