import Yau.Proofs.D02LeviCharts
import Yau.Proofs.D04CircleMean

/-! The continuous real circle inequality gives the original EReal
continuous-majorant psh predicate. -/

noncomputable section
open scoped Manifold Topology ContDiff
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

theorem isPshOn_of_complexLinePshOn {n : ℕ} {O : Set (ComplexVector n)}
    {f : ComplexVector n → ℝ} (hf : LeafCandidates.ComplexLinePshOn O f) :
    IsPshOn (fun z => (f z : EReal)) O := by
  refine ⟨fun _ _ => EReal.coe_lt_top _,
    (continuous_coe_real_ereal.comp_continuousOn hf.1).upperSemicontinuousOn, ?_⟩
  intro z w hdisc φ hφ hmajor
  have hmaps : ∀ θ : ℝ, z + Complex.exp (θ * Complex.I) • w ∈ O := by
    intro θ
    exact hdisc _ (by rw [Complex.norm_exp_ofReal_mul_I])
  have hc : Continuous (fun θ : ℝ => f (z + Complex.exp (θ * Complex.I) • w)) :=
    hf.1.comp_continuous (by fun_prop) hmaps
  apply EReal.coe_le_coe_iff.mpr
  exact (hf.2 z w hdisc).trans (Yau.Proofs.D04Aux.circleAverage_mono hc hφ
    (fun θ => EReal.coe_le_coe_iff.mp (hmajor θ)))

end Yau.NodeProofs.D02Aux
