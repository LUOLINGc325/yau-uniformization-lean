import Yau.Proofs.P06HodgeRegularityWordCalculus
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Finite basis and genuine joint evaluation calculus for chart jet maps. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace Yau.NodeProofs.P06Aux

variable {E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι]

theorem regularityBasis_fderiv_apply (b : Basis ι ℝ E) (u : E → ℝ) (z dx : E) :
    fderiv ℝ u z dx = ∑ i, b.repr dx i * regularityDirection (b i) u z := by
  conv_lhs => rw [← b.sum_repr dx]
  simp only [map_sum,map_smul,smul_eq_mul,regularityDirection]

def regularityJetCurve (L : List ι → H →L[ℝ] (E →ᵇ ℝ)) (h : ℝ → H)
    (w : List ι) (p : E × ℝ) : ℝ := L w (h p.2) p.1

theorem regularityJetCurve_continuousOn
    (L : List ι → H →L[ℝ] (E →ᵇ ℝ)) {T : Set ℝ} {h : ℝ → H}
    (hh : ContinuousOn h T) (w : List ι) :
    ContinuousOn (regularityJetCurve L h w) (Set.univ ×ˢ T) := by
  have htime : ContinuousOn (fun p : E × ℝ => h p.2) (Set.univ ×ˢ T) :=
    hh.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have heval : Continuous (fun p : (E →ᵇ ℝ) × E => p.1 p.2) := continuous_eval
  exact heval.comp_continuousOn
    (((L w).continuous.comp_continuousOn htime).prodMk continuous_fst.continuousOn)

end Yau.NodeProofs.P06Aux
