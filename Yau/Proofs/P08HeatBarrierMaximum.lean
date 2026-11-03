import Yau.LeafProofs.L19GaussianWeightComparison

/-! The proved Gaussian local-maximum argument extends to supersolutions
by subtracting its nonnegative tangent-time defect at the maximizing point. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.P08Aux
open Yau Yau.LeafProofs L12Aux L18Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem gaussian_supersolution_no_local_max
    (g : SmoothMetric M) (hK : IsKahler g)
    (o : M.Carrier) {a C ε t d : ℝ} (hε : 0 < ε) (ht : 0 < t) (q : M.Carrier)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (hd : HasDerivAt (u q) d t)
    (hineq : laplacian g.form (fun y => u y t) q ≤ d)
    (hS : ∃ S : M.Carrier → ℝ,
      ∃ b : letI := underlyingRealTangentNormedAddCommGroup g.form q
        letI := underlyingRealTangentInnerProductSpace g.form q
        OrthonormalBasis (Fin (2 * n)) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) q),
        ContDiffAt ℝ 2 (S ∘ chartInv q) (chartPt q q) ∧
        S q = gaussianWeight g o a q ∧
        -2 * C * gaussianWeight g o a q ≤
          endpointFrameHessianTrace g q b (S ∘ chartInv q) (chartPt q q) ∧
        IsLocalMax (fun z => Real.exp (-(C * t)) * S (chartInv q z) -
          u (chartInv q z) t) (chartPt q q))
    (htmax : IsLocalMaxOn
      (fun r => Real.exp (-(C * r)) * gaussianWeight g o a q -
        u q r - ε * (1 + r)) (Set.Iic t) t) : False := by
  let e := d - laplacian g.form (fun y => u y t) q
  let v : M.Carrier → ℝ → ℝ := fun y s => u y s - e * (s - t)
  have he : 0 ≤ e := sub_nonneg.mpr hineq
  have hv : SmoothSpaceTime v (Set.Ioi 0) := by
    intro x
    exact (hu x).sub (contDiffOn_const.mul (contDiffOn_snd.sub contDiffOn_const))
  have hvt : (fun y => v y t) = (fun y => u y t) := by
    funext y
    simp only [v, sub_self, mul_zero, sub_zero]
  have hheat : HasDerivAt (v q) (laplacian g.form (fun y => v y t) q) t := by
    rw [hvt]
    have hder := hd.sub (((hasDerivAt_id t).sub_const t).const_mul e)
    simp only [mul_one] at hder
    have heq : d - e = laplacian g.form (fun y => u y t) q := by dsimp only [e]; ring
    rw [heq] at hder
    convert hder using 1 <;> funext s <;> rfl

  apply gaussian_comparison_no_local_max g hK o hε ht q hv hheat
  · simpa only [v, sub_self, mul_zero, sub_zero] using hS
  · filter_upwards [htmax, self_mem_nhdsWithin] with r hr hrt
    have her : e * (r - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he (sub_nonpos.mpr hrt)
    dsimp only [v]
    simp only [sub_self, mul_zero, sub_zero]
    linarith

end Yau.NodeProofs.P08Aux
