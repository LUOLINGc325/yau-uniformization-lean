import Yau.LeafProofs.L17BootstrapHolderTaylor

/-! A direct finite-order interface using ordinary budgets only at k, k+1 and k+2. -/

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Yau.LeafProofs.L17BootstrapHolderTaylorAux
open L17Aux L17HolderAux L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {Param F : Type*} [NormedAddCommGroup Param] [NormedSpace ℝ Param]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_holder_coefficient_jet_of_mixed_bounds
    (P : UniformChartPartition g) {R T beta : ℝ}
    (c : Param → P.centers → ComplexVector n → ℝ → F)
    (hSmooth : ∀ q, ContDiffOn ℝ ∞
      (fun a : Param × (ComplexVector n × ℝ) => c a.1 q a.2.1 a.2.2)
      (ball 0 R ×ˢ (ball 0 (2*P.radius) ×ˢ Set.univ)))
    (hT : T ≤ P.radius^2) (hb : beta < 1) (k : ℕ)
    {theta : Param} (ha : theta ∈ ball 0 R) {A Z U : ℝ}
    (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hU : 0 ≤ U)
    (hMixed : ∀ q z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      ‖coeffParamJet c k theta q z t‖ ≤ A ∧
      ‖fderiv ℝ (fun w => coeffParamJet c k theta q w t) z‖ ≤ Z ∧
      ‖deriv (fun s => coeffParamJet c k theta q z s) t‖ ≤ U) :
    ∃ u : LocalHolderSpace (ParamJet Param k F) P T beta,
      (∀ q : LocalCylinder P T, localFun _ u q = coeffParamJet c k theta q.1 q.2.1 q.2.2) ∧
      ‖u‖ ≤ mixedHolderBudget P beta A Z U := by
  have hjet : ∀ q z, z ∈ ball 0 P.radius → ∀ t : ℝ,
      ContDiffAt ℝ ∞
        (fun a : Param × (ComplexVector n × ℝ) => coeffParamJet c k a.1 q a.2.1 a.2.2)
        (theta,(z,t)) := by
    intro q z hz t
    exact coeffParamJet_contDiffAt P c hSmooth k ha q
      ((ball_subset_ball (by linarith [P.radius_pos])) hz) t
  have hf : ∀ q, ContinuousOn (fun b : ComplexVector n × ℝ => coeffParamJet c k theta q b.1 b.2)
      (ball 0 P.radius ×ˢ Icc (0:ℝ) T) := by
    intro q b hb
    exact ((hjet q b.1 hb.1 b.2).comp b
      (contDiffAt_const.prodMk contDiffAt_id)).continuousAt.continuousWithinAt
  have hzD : ∀ q z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      DifferentiableAt ℝ (fun w => coeffParamJet c k theta q w t) z := by
    intro q z hz t _
    exact ((hjet q z hz t).comp z
      (contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const))).differentiableAt (by simp)
  have htD : ∀ q z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      DifferentiableAt ℝ (fun s => coeffParamJet c k theta q z s) t := by
    intro q z hz t _
    exact ((hjet q z hz t).comp t
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)
  let u := localMixedElement P hT hb.le hZ hU (coeffParamJet c k theta) hf hzD htD
    (fun q z hz t ht => (hMixed q z hz t ht).1)
    (fun q z hz t ht => (hMixed q z hz t ht).2.1)
    (fun q z hz t ht => (hMixed q z hz t ht).2.2)
  refine ⟨u, fun q => rfl, ?_⟩
  have hrho := P.radius_pos
  dsimp only [u, localMixedElement, mixedHolderBudget]
  apply localOfBounds_norm_le <;> positivity

/-- This finite theorem assumes no numerical derivative budget above k+2. -/
theorem exists_holder_parameter_finite_lifts
    (P : UniformChartPartition g) {R T beta : ℝ}
    (c : Param → P.centers → ComplexVector n → ℝ → F)
    (hSmooth : ∀ q, ContDiffOn ℝ ∞
      (fun a : Param × (ComplexVector n × ℝ) => c a.1 q a.2.1 a.2.2)
      (ball 0 R ×ˢ (ball 0 (2*P.radius) ×ˢ Set.univ)))
    (hT : T ≤ P.radius^2) (hb : beta < 1) (k : ℕ)
    (M0 Mz Mt : ℕ → ℝ)
    (hBudget : ∀ j ∈ Icc k (k+2), 0 ≤ M0 j ∧ 0 ≤ Mz j ∧ 0 ≤ Mt j)
    (hMixed : ∀ j ∈ Icc k (k+2), ∀ theta, theta ∈ ball 0 R → ∀ q z,
      z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
        ‖coeffParamJet c j theta q z t‖ ≤ M0 j ∧
        ‖fderiv ℝ (fun w => coeffParamJet c j theta q w t) z‖ ≤ Mz j ∧
        ‖deriv (fun s => coeffParamJet c j theta q z s) t‖ ≤ Mt j) :
    ∃ u : (j : ℕ) → Param → LocalHolderSpace (ParamJet Param j F) P T beta,
      (∀ j ∈ Icc k (k+2), ∀ a ∈ ball 0 R, ∀ q : LocalCylinder P T,
        localFun _ (u j a) q = coeffParamJet c j a q.1 q.2.1 q.2.2) ∧
      (∀ j ∈ Icc k (k+2), ∀ a ∈ ball 0 R,
        ‖u j a‖ ≤ mixedHolderBudget P beta (M0 j) (Mz j) (Mt j)) ∧
      (∀ a ∈ ball 0 R, HasFDerivAt (u k)
        (holderJetDerivativeCLM (Param := Param) (F := F) k (u (k+1) a)) a) ∧
      ∀ x ∈ ball 0 R, ∀ y ∈ ball 0 R,
        ‖u k y-u k x-holderJetDerivativeCLM (Param := Param) (F := F) k (u (k+1) x) (y-x)‖ ≤
          mixedHolderBudget P beta (M0 (k+2)) (Mz (k+2)) (Mt (k+2))*‖y-x‖^2 := by
  classical
  have hex : ∀ j ∈ Icc k (k+2), ∀ a, a ∈ ball 0 R →
      ∃ u : LocalHolderSpace (ParamJet Param j F) P T beta,
        (∀ q : LocalCylinder P T, localFun _ u q = coeffParamJet c j a q.1 q.2.1 q.2.2) ∧
        ‖u‖ ≤ mixedHolderBudget P beta (M0 j) (Mz j) (Mt j) := by
    intro j hj a ha
    exact exists_holder_coefficient_jet_of_mixed_bounds P c hSmooth hT hb j ha
      (hBudget j hj).1 (hBudget j hj).2.1 (hBudget j hj).2.2 (hMixed j hj a ha)
  let u : (j : ℕ) → Param → LocalHolderSpace (ParamJet Param j F) P T beta :=
    fun j a => if hj : j ∈ Icc k (k+2) then
      if ha : a ∈ ball 0 R then Classical.choose (hex j hj a ha) else 0 else 0
  have hval : ∀ j ∈ Icc k (k+2), ∀ a ∈ ball 0 R, ∀ q : LocalCylinder P T,
      localFun _ (u j a) q = coeffParamJet c j a q.1 q.2.1 q.2.2 := by
    intro j hj a ha q
    simpa only [u, dite_eq_left hj, dite_eq_left ha] using (Classical.choose_spec (hex j hj a ha)).1 q
  have hnorm : ∀ j ∈ Icc k (k+2), ∀ a ∈ ball 0 R,
      ‖u j a‖ ≤ mixedHolderBudget P beta (M0 j) (Mz j) (Mt j) := by
    intro j hj a ha
    simpa only [u, dite_eq_left hj, dite_eq_left ha] using (Classical.choose_spec (hex j hj a ha)).2
  have hd : ∀ j ∈ Icc k (k+1), ∀ a ∈ ball 0 R, ∀ q : LocalCylinder P T,
      HasFDerivAt (fun b => localFun _ (u j b) q)
        (jetCurry (Param := Param) (F := F) j (localFun _ (u (j+1) a) q)) a := by
    intro j hj a ha q
    have hj0 : j ∈ Icc k (k+2) := by rcases hj with ⟨h0,h1⟩; constructor <;> omega
    have hj1 : j+1 ∈ Icc k (k+2) := by rcases hj with ⟨h0,h1⟩; constructor <;> omega
    have hz : (q.2.1 : ComplexVector n) ∈ ball 0 (2*P.radius) :=
      (ball_subset_ball (by linarith [P.radius_pos])) q.2.1.property
    have hc : ContDiffAt ℝ ∞ (fun b => c b q.1 q.2.1 q.2.2) a :=
      (coeff_contDiffAt P c hSmooth ha q.1 hz q.2.2).comp a
        (contDiffAt_id.prodMk contDiffAt_const)
    rw [hval (j+1) hj1 a ha q]
    apply (hasFDerivAt_parameterJet hc j).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds ha] with b hb
    exact hval j hj0 b hb q
  have hk2 : k+2 ∈ Icc k (k+2) := ⟨by omega,le_rfl⟩
  have hC := mixedHolderBudget_nonneg P beta (hBudget (k+2) hk2).1
    (hBudget (k+2) hk2).2.1 (hBudget (k+2) hk2).2.2
  refine ⟨u,hval,hnorm,?_,?_⟩
  · intro a ha
    exact holder_parameterJet_hasFDerivAt (convex_ball 0 R) isOpen_ball u k hd hC
      (hnorm (k+2) hk2) ha
  · intro x hx y hy
    exact holder_parameterJet_remainder_le (convex_ball 0 R) u k hd hC
      (hnorm (k+2) hk2) hx hy

end Yau.LeafProofs.L17BootstrapHolderTaylorAux
