import Yau.Proofs.F01RelativeScalarSandwich
import Yau.Proofs.F01PotentialChartIdentity
import Yau.Proofs.F01SpaceTimeChart

/-! The actual original potential identity identifies the clamped
transformed Hessian with the same flow metric at the clamped time. -/
noncomputable section
open Set
open scoped ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem flow_potential_matrix_in_chart
    (α k : HermitianField M) (hα : MetricSmooth α)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (t : ℝ)
    (hpot : ∀ x, gMat k x = gMat α x - (t : ℂ) • ricci α x + levi u x)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    pullbackMatrix k e z = pullbackMatrix α e z -
      (t : ℂ) • backgroundRicci (pullbackMatrix α e) z + leviC (fun w => u (e w)) z := by
  let a := e z
  let J := linearMatrix (coordinateDifferential e a z)
  have ha : e z ∈ (extChartAt (ComplexModel n) a).source := mem_extChartAt_source a
  have hαc : pullbackMatrix α e z = Jᴴ * gMat α a * J :=
    pullbackMatrix_eq_congruence α e a z ha
  have hkc : pullbackMatrix k e z = Jᴴ * gMat k a * J :=
    pullbackMatrix_eq_congruence k e a z ha
  have hRc : pullbackRicci α e z = Jᴴ * ricci α a * J :=
    pullbackRicci_eq_ricci α hα e he hei hz
  have hUc : leviC (fun w => u (e w)) z = Jᴴ * levi u a * J :=
    leviC_holomorphic_chart u hu e he hz
  rw [hkc, hpot a]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  rw [← hαc, ← hRc, ← hUc]
  rfl

theorem clamped_flow_transformed_matrix
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T : ℝ}
    (hU : SmoothSpaceTime U (Icc 0 T)) (hh0 : h 0 = α)
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {p : Point n} (hp : p.1 ∈ e.source) (ht : p.2 ≤ T) :
    clampedBackground (pullbackMatrix α e) p + complexHessianMap
      (hessian (forwardZeroSpaceTime (fun q : Point n => U (e q.1) q.2)) p) =
        iota (pullbackMatrix (h (max p.2 0)) e p.1) := by
  rw [clamped_transformed_matrix_identity (pullbackMatrix α e) e.open_source
    (smoothSpaceTime_holomorphic_chart hU e he) hp ht]
  by_cases hn : p.2 ≤ 0
  · rw [if_pos hn, max_eq_right hn, hh0]
  · have hpt : p.2 ∈ Icc 0 T := ⟨(lt_of_not_ge hn).le, ht⟩
    rw [if_neg hn, max_eq_left hpt.1, ← flow_potential_matrix_in_chart α (h p.2) hα
      (fun y => U y p.2) (smoothSpaceTime_slice hU hpt) p.2 (hpot p.2 hpt) e he hei hp]

end Yau.NodeProofs.F01Aux
