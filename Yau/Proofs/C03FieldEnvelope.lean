import Yau.Proofs.C03GlobalGeometry
import Yau.Proofs.C03GeodesicRetreat

/-! The actual field-distance moving-ball maximum is continuous, including
where maximizing endpoints lie on the cut locus. -/

noncomputable section
open Set
open scoped Topology

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def fieldBallMaximum (h : HermitianField M) (ψ : M.Carrier → ℝ)
    (ρ : ℝ) (z : M.Carrier) : ℝ :=
  sSup (ψ '' {y | inducedDistance h y z ≤ ρ})

theorem fieldBallMaximum_spec (h : HermitianField M) (hh : MetricSmooth h)
    (hcompact : ∀ p R, IsCompact {x | inducedDistance h p x ≤ R})
    (ψ : M.Carrier → ℝ) (hψ : Continuous ψ) (ρ : ℝ) (hρ : 0 ≤ ρ) (z : M.Carrier) :
    ∃ y, inducedDistance h z y ≤ ρ ∧ ψ y = fieldBallMaximum h ψ ρ z ∧
      ∀ w, inducedDistance h z w ≤ ρ → ψ w ≤ fieldBallMaximum h ψ ρ z := by
  letI := metricSpaceOfField h hh
  letI := fieldMetric_proper_of_compact_sublevels h hh hcompact
  obtain ⟨y, hy, heq, hmax⟩ := metricBallMaximum_spec ψ hψ ρ hρ z
  refine ⟨y, ?_, heq, ?_⟩
  · change inducedDistance h y z ≤ ρ at hy
    rwa [inducedDistance_symm h hh y z] at hy
  · intro w hw
    apply hmax w
    change inducedDistance h w z ≤ ρ
    rwa [inducedDistance_symm h hh w z]

theorem fieldBallMaximum_continuous (h : HermitianField M) (hh : MetricSmooth h)
    (hcompact : ∀ p R, IsCompact {x | inducedDistance h p x ≤ R})
    (ψ : M.Carrier → ℝ) (hψ : Continuous ψ) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (fieldBallMaximum h ψ ρ) := by
  letI := metricSpaceOfField h hh
  letI := fieldMetric_proper_of_compact_sublevels h hh hcompact
  exact metricBallMaximum_continuous ψ hψ ρ hρ.le
    (fun z => field_closedBall_subset_closure_ball h hh hcompact z ρ hρ)

end Yau.Proofs.C03Aux
