import Yau.LeafProofs.L19HeatClassical
import Yau.LeafProofs.L19HeatFixedSlabDuality

/-! Uniform Gaussian weighted mass near the initial time, derived internally. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

/-- Every original arbitrary positive heat solution has finite uniformly
bounded Gaussian weighted mass all the way to zero.  The auxiliary heat,
its comparison and the fixed-slab duality are internally constructed. -/
theorem positiveHeatSolution_uniform_gaussian_weighted_mass (hn : 0 < n)
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u : M.Carrier → ℝ → ℝ}
    (hu : LeafCandidates.PositiveHeatSolution g.form u) (o : M.Carrier)
    {a T : ℝ} (ha : 0 < a) (hT : 0 < T) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℝ, 0 < s → s ≤ T →
      Integrable (fun x => u x s * gaussianWeight g o a x) μ ∧
      (∫ x, u x s * gaussianWeight g o a x ∂μ) ≤ B := by
  let f := scalarGaussianL2 g hK hRic μ hμ o a ha
  let U := scalarClassicalHeat hn g hK μ hμ f
  let v : M.Carrier → ℝ → ℝ := fun x s => U x (T + 1 - s)
  have hUs : SmoothSpaceTime U (Ioi 0) := scalarClassicalHeat_smooth hn g hK μ hμ f
  have hv : SmoothSpaceTime v (Ioo 0 (T + 1)) := by
    intro x
    exact (LocalTime.smoothSpaceTime_timeReverse hUs (T + 1) x).mono (fun p hp => ⟨hp.1, hp.2.2⟩)
  have hbackward : ∀ x s, s ∈ Ioo 0 (T + 1) →
      HasDerivAt (v x) (-laplacian g.form (fun y => v y s) x) s := by
    intro x s hs
    exact LocalTime.scalarHeat_timeReverse_hasDerivAt g
      (fun y t ht => scalarClassicalHeat_hasDerivAt hn g hK μ hμ f y ht) (T + 1) x hs.2
  obtain ⟨C, β, hC, hβ, htail⟩ := scalarClassicalGaussianHeat_tail hn g hcomplete hK hRic μ hμ o ha
    (l := 1) (b := T + 1) (by norm_num) (by linarith)
  have hslab {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) : Icc s T ⊆ Ioo 0 (T + 1) := by
    intro r hr
    exact ⟨hs.trans_le hr.1, by linarith [hr.2]⟩
  have hdecay {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) (x : M.Carrier) (r : ℝ) (hr : r ∈ Icc s T) :
      |v x r| ≤ C * Real.exp (-β * inducedDistance g.form o x ^ 2) := by
    apply htail x (T + 1 - r)
    exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
  let Q := ∫ x, u x T * v x T ∂μ
  let m : ℝ := (2 * n : ℕ) * a
  have hm : 0 ≤ m := mul_nonneg (Nat.cast_nonneg _) ha.le
  let E := Real.exp (m * (T + 1))
  refine ⟨max (E * Q) 0 + 1, by positivity, ?_⟩
  intro s hs hsT
  obtain ⟨his, _hiT, heq⟩ := positiveHeatSolution_gaussian_backward_duality g hcomplete hK hRic μ hμ hu
    isOpen_Ioo (fun _ ht => ht.1) hv hbackward o hs (hslab hs hsT) hsT hC hβ (hdecay hs hsT)
  have hi : Integrable (fun x => u x s * gaussianWeight g o a x) μ := by
    change Integrable (fun x => u x s * Real.exp (-(a * inducedDistance g.form o x ^ 2))) μ
    simpa only [neg_mul] using positiveHeatSolution_gaussian_weight_integrable
      g hcomplete hK hRic μ hμ hu o ha hs
  refine ⟨hi, ?_⟩
  have hτ : 0 < T + 1 - s := by linarith
  have hpoint (x : M.Carrier) :
      Real.exp (-(m * (T + 1))) * (u x s * gaussianWeight g o a x) ≤ u x s * v x s := by
    have hlow := scalarClassicalGaussianHeat_lower hn g hK hRic μ hμ o ha x hτ
    have htime : Real.exp (-(m * (T + 1))) ≤ Real.exp (-(m * (T + 1 - s))) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hm hs.le]
    have hφ := (mul_le_mul_of_nonneg_right htime (gaussianWeight_pos g o a x).le).trans hlow
    have hh := mul_le_mul_of_nonneg_left hφ (hu.2 x s hs).1.le
    simpa only [v, U, f, m, mul_left_comm, mul_assoc] using hh
  have hmom := integral_mono (hi.const_mul (Real.exp (-(m * (T + 1))))) his hpoint
  rw [integral_const_mul] at hmom
  have hQ : (∫ x, u x s * v x s ∂μ) = Q := heq.symm
  rw [hQ] at hmom
  have hexp : E * Real.exp (-(m * (T + 1))) = 1 := by
    dsimp only [E]
    rw [← Real.exp_add]
    simp
  have hbound : (∫ x, u x s * gaussianWeight g o a x ∂μ) ≤ E * Q := by
    calc
      _ = (E * Real.exp (-(m * (T + 1)))) * (∫ x, u x s * gaussianWeight g o a x ∂μ) := by rw [hexp, one_mul]
      _ = E * (Real.exp (-(m * (T + 1))) * (∫ x, u x s * gaussianWeight g o a x ∂μ)) := by ring
      _ ≤ E * Q := mul_le_mul_of_nonneg_left hmom (Real.exp_pos _).le
  exact hbound.trans (by linarith [le_max_left (E * Q) 0])

end Yau.LeafProofs.L19Aux
