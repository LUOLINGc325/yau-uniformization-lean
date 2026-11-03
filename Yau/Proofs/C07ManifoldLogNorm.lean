import Yau.Proofs.C07LogNorm
import Yau.Proofs.C07PshScaling

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n m : ℕ} {M : ComplexManifold n}

/-- Logarithmic norm on a genuine manifold domain, in every actual chart. -/
theorem manifold_logNorm_psh {V : Set M.Carrier} (hV : IsOpen V)
    {f : M.Carrier → ComplexVector m}
    (hf : MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector m) f V) :
    PshOnManifold (fun y => ENNReal.log (ENNReal.ofReal ‖f y‖)) V := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    simp only [ENNReal.log_lt_top_iff, ENNReal.ofReal_lt_top]
  · exact (ENNReal.continuous_log.comp_continuousOn
      (ENNReal.continuous_ofReal.comp_continuousOn hf.continuousOn.norm)).upperSemicontinuousOn
  · intro x
    let D : Set (ComplexVector n) := {z | z ∈ chartTarget x ∧ chartInv x z ∈ V}
    have hD : IsOpen D := (continuousOn_extChartAt_symm (I := ComplexModel n) x).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := ComplexModel n) x) hV
    have hinv := mdifferentiableOn_extChartAt_symm (I := ComplexModel n) (x := x)
    have hc : DifferentiableOn ℂ (fun z => f (chartInv x z)) D := by
      exact (hf.comp (hinv.mono Set.inter_subset_left) (fun z hz => hz.2)).differentiableOn
    exact extendedLogNorm_isPshOn hD hc

/-- Positive normalization of a manifold psh function preserves the same
domain and all original chart tests. -/
theorem manifold_psh_positive_scale {V : Set M.Carrier} {u : M.Carrier → EReal}
    (hu : PshOnManifold u V) {a : ℝ} (ha : 0 < a) :
    PshOnManifold (fun y => (a : EReal) * u y) V := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have h := (positiveScaleIso a ha).strictMono (hu.1 y hy)
    change (a : EReal) * u y < (a : EReal) * ⊤ at h
    simpa only [EReal.coe_mul_top_of_pos ha] using h
  · exact (positiveScaleIso a ha).continuous.comp_upperSemicontinuousOn hu.2.1
      (positiveScaleIso a ha).monotone
  · intro x
    exact isPshOn_positive_scale (hu.2.2 x) ha

end Yau.Proofs.C07Aux
