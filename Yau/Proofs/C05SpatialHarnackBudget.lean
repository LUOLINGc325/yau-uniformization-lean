import Yau.Proofs.C05SpatialHarnackBudgetPointwise
import Yau.Proofs.C05SpatialRicciBall

/-! The radius and third-jet budget precede all geometry. Actual finite
scalar/Ricci jets and center pinching control the original minimized Harnack function. -/

noncomputable section
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.Proofs.C05SpatialHarnackBudgetAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L12Aux
variable {n : ℕ}

theorem exists_spatial_harnack_jet_budget (n : ℕ) (lam B b K : ℝ)
    (hlam : 0 < lam) (hB : 0 ≤ B) (hb : 0 < b) (hKcap : 0 ≤ K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ b ∧ ∃ J : ℝ, 0 < J ∧
      ∀ (M : ComplexManifold n) (g : SmoothMetric M) (o : M.Carrier) (κ : ℝ),
        (∀ y, (ricci g.form y).PosDef) →
        lam ≤ relMinEigenvalue (gMat g.form o) (ricci g.form o) → |κ| ≤ K →
        (∀ x ∈ distBall g.form o (2*b),
          (∀ j ≤ 6, scalarJetNorm g.form (scalarCurvature g.form) j x ≤ B) ∧
          (∀ j ≤ 4, realRicciJetNorm g.form j x ≤ B)) →
        ∀ x ∈ distBall g.form o r,
          scalarJetNorm g.form (intrinsicHarnackMinimum g.form κ) 3 x ≤ J := by
  obtain ⟨r, hr, hrb, hcoercive⟩ := C05SpatialRicciBallAux.exists_uniform_coercive_ricci_ball
    n lam B b hlam hB hb
  refine ⟨r, hr, hrb, spatialHarnackJetBudget n (lam / 2) B K,
    spatialHarnackJetBudget_pos n (by positivity) hB hKcap, ?_⟩
  intro M g o κ hRic hpin hκ hJets x hx
  have hxlarge : x ∈ distBall g.form o (2*b) := by
    apply (mem_distBall_iff g o x (show 0 < 2*b by positivity)).mpr
    exact ((mem_distBall_iff g o x hr).mp hx).trans (hrb.trans_lt (by linarith))
  exact pointwise_harnack_jet_bound g (lam / 2) B K (by positivity) hB hKcap hRic κ hκ x
    (hcoercive M g o hpin (fun y hy => (hJets y hy).2 1 (by omega)) x hx)
    (hJets x hxlarge).1 (hJets x hxlarge).2

end Yau.Proofs.C05SpatialHarnackBudgetAux
