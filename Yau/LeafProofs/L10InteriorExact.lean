import Yau.LeafProofs.L10InteriorInduction

/-! The frozen variable-coefficient leaf conclusion, with no source assumptions. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace Yau.LeafProofs

theorem interiorEllipticEstimate : LeafCandidates.InteriorEllipticEstimate := by
  intro n s r R ell A hr hrR hell hA
  by_cases hn : n = 0
  · subst n
    refine ⟨1, one_pos, ?_⟩
    intro a b _ha _hb _hEll _hBound u _hu _hi _hFi
    simpa only [one_mul] using interiorEllipticEstimate_dimension_zero_bound s hr (hr.trans hrR) a b u
  · obtain ⟨C, hC, hEnergy⟩ := elliptic_interior_energy_estimate n (Nat.pos_of_ne_zero hn)
      s r R ell A hr hrR hell hA
    refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
    intro a b ha hb hEll hBound u hu hi hFi
    have hE := hEnergy a b ha hb (fun z hz => (hEll z hz).2) hBound u hu hi hFi
    let U := LeafCandidates.sobolevNormSq (Metric.ball (0 : ComplexVector n) R) u 0
    let F := LeafCandidates.sobolevNormSq (Metric.ball (0 : ComplexVector n) R) (LeafCandidates.ellipticOp a b u) s
    have hU : 0 ≤ U := sobolevNormSq_nonneg _ _ _
    have hF : 0 ≤ F := sobolevNormSq_nonneg _ _ _
    have hAdd : Real.sqrt (U + F) ≤ Real.sqrt U + Real.sqrt F := by
      have hUU := Real.sq_sqrt hU
      have hFF := Real.sq_sqrt hF
      have hUF := Real.sq_sqrt (add_nonneg hU hF)
      nlinarith [Real.sqrt_nonneg U, Real.sqrt_nonneg F, Real.sqrt_nonneg (U + F),
        mul_nonneg (Real.sqrt_nonneg U) (Real.sqrt_nonneg F)]
    calc
      _ ≤ Real.sqrt (C * (U + F)) := Real.sqrt_le_sqrt hE
      _ = Real.sqrt C * Real.sqrt (U + F) := Real.sqrt_mul hC.le _
      _ ≤ _ := mul_le_mul_of_nonneg_left hAdd (Real.sqrt_nonneg C)

end Yau.LeafProofs
