import Yau.Proofs.C01ClockSpatialJets
import Yau.Proofs.C01FlowTimeJets

/-! The original Ricci matrix is nonnegative at positive time, as the
actual pure spatial Levi block of the negative log determinant clock. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_ricci_posSemidef_posTime
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    (ricci (h t) x).PosSemidef := by
  have hA := localizedFlow_ricci_isHermitian hflow x ht
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hA.im_star_dotProduct_mulVec_self v).symm⟩
  let w : ℂ := ((Real.log t / 2 : ℝ) : ℂ)
  let d : ComplexVector n := WithLp.toLp 2 v
  have htime : Real.exp (2 * w.re) = t := by
    have he : 2 * w.re = Real.log t := by
      simp only [w, Complex.ofReal_re]
      ring
    rw [he, Real.exp_log ht]
  have hp := localizedFlow_negativeLogDetClock_levi_nonneg hflow hjoint x
    (chartPt x x) d (mem_extChartAt_target (I := ComplexModel n) x) w 0
  rw [negativeLogDetClock_mixed_spatial hflow x d w] at hp
  simpa only [htime, d, WithLp.ofLp_toLp] using hp

end Yau.NodeProofs.C01Aux
