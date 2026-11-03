import Yau.LeafProofs.L24Complete

/-! The native local gradient estimate applies to actual nonnegative heat solutions, including the zero solution. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem gradNormSq_add_constant (h : HermitianField M) {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (c : ℝ) (x : M.Carrier) :
    gradNormSq h (fun y => u y+c) x=gradNormSq h u x := by
  have hs : SmoothFn (fun y => u y+c) := fun a => (hu a).add contDiffOn_const
  have hd : HasDerivAt (fun s : ℝ => s+c) 1 (u x) := by
    simpa only [id_eq] using (hasDerivAt_id (u x)).add_const c
  have hp := scalarGradientPair_scalar_comp_self h hu (fun s : ℝ => s+c) x hd.differentiableAt
  rw [scalarGradientPair_eq_twice_gradNormSq h hs x,
    scalarGradientPair_eq_twice_gradNormSq h hu x,hd.deriv] at hp
  norm_num at hp
  linarith

theorem nonnegative_heat_add_positive (h : HermitianField M)
    (u : M.Carrier → ℝ → ℝ) (hu : SmoothSpaceTime u (Ioi 0))
    (hEq : ∀ x t,0 < t → HasDerivAt (u x) (laplacian h (fun y => u y t) x) t)
    (hNonnegative : ∀ x t,0 < t → 0 ≤ u x t) {ε : ℝ} (hε : 0 < ε) :
    LeafCandidates.PositiveHeatSolution h (fun x t => u x t+ε) := by
  refine ⟨fun a => (hu a).add contDiffOn_const,?_⟩
  intro x t ht
  refine ⟨add_pos_of_nonneg_of_pos (hNonnegative x t ht) hε,?_⟩
  rw [laplacian_add_const h (smoothSpaceTime_slice hu ht) ε x]
  exact ((hEq x t ht).add_const ε).deriv

theorem nonnegative_heat_gradient_at_sqrt_scale
    (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ z,(ricci g.form z).PosSemidef)
    (u : M.Carrier → ℝ → ℝ) (hu : SmoothSpaceTime u (Ioi 0))
    (hEq : ∀ x t,0 < t → HasDerivAt (u x) (laplacian g.form (fun y => u y t) x) t)
    (hNonnegative : ∀ x t,0 < t → 0 ≤ u x t)
    (x : M.Carrier) {t A : ℝ} (ht : 0 < t) (hA : 0 ≤ A)
    (hbound : ∀ z s,inducedDistance g.form x z ≤ Real.sqrt t →
      s ∈ Icc (t/2) t → u z s ≤ A) :
    Real.sqrt (gradNormSq g.form (fun z => u z t) x) ≤
      LeafProofs.L24Aux.localGradientConstant n*A/Real.sqrt t := by
  have hεpos (j : ℕ) : 0 < 1/((j : ℝ)+1) := by positivity
  have hEstimate (j : ℕ) : Real.sqrt (gradNormSq g.form (fun z => u z t) x) ≤
      LeafProofs.L24Aux.localGradientConstant n*(A+1/((j : ℝ)+1))/Real.sqrt t := by
    have hh := LeafProofs.L24Aux.positiveHeatSolution_gradient_at_sqrt_scale g hK hRic
      (nonnegative_heat_add_positive g.form u hu hEq hNonnegative (hεpos j))
      x ht (add_pos_of_nonneg_of_pos hA (hεpos j))
      (fun z s hz hs => by linarith [hbound z s hz hs])
    simpa only [gradNormSq_add_constant g.form (smoothSpaceTime_slice hu ht)] using hh
  have hLimit : Tendsto (fun j : ℕ => LeafProofs.L24Aux.localGradientConstant n*
      (A+1/((j : ℝ)+1))/Real.sqrt t) atTop
      (𝓝 (LeafProofs.L24Aux.localGradientConstant n*A/Real.sqrt t)) := by
    simpa only [add_zero] using (tendsto_const_nhds.mul
      (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))).div_const (Real.sqrt t)
  exact ge_of_tendsto hLimit (Eventually.of_forall hEstimate)

end Yau.Proofs.F03Aux
