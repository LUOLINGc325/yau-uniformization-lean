import Yau.LeafProofs.L17BootstrapHolderTaylorBounds
import Yau.LeafProofs.L17BootstrapHolderTaylorJets

/-! Ordinary mixed coefficient bounds imply genuine Holder-valued Frechet smoothness.
All local norms are the existing weighted-pair graph norms on the unchanged cylinder.
-/

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace Yau.LeafProofs.L17BootstrapHolderTaylorAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderAlgebraAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {Param F : Type*}
  [NormedAddCommGroup Param] [NormedSpace ℝ Param]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def coeffParamJet {P : UniformChartPartition g}
    (c : Param → P.centers → ComplexVector n → ℝ → F)
    (k : ℕ) (theta : Param) (q : P.centers) (z : ComplexVector n) (t : ℝ) :
    ParamJet Param k F := iteratedFDeriv ℝ k (fun a => c a q z t) theta

section Coefficients
variable (P : UniformChartPartition g) {R T beta : ℝ}
variable (c : Param → P.centers → ComplexVector n → ℝ → F)
variable (hSmooth : ∀ q, ContDiffOn ℝ ∞
  (fun a : Param × (ComplexVector n × ℝ) => c a.1 q a.2.1 a.2.2)
  (ball 0 R ×ˢ (ball 0 (2*P.radius) ×ˢ Set.univ)))
include hSmooth

theorem coeff_contDiffAt {theta : Param} (ha : theta ∈ ball 0 R)
    (q : P.centers) {z : ComplexVector n} (hz : z ∈ ball 0 (2*P.radius)) (t : ℝ) :
    ContDiffAt ℝ ∞
      (fun a : Param × (ComplexVector n × ℝ) => c a.1 q a.2.1 a.2.2)
      (theta,(z,t)) := by
  have hs : IsOpen (ball (0:Param) R ×ˢ
      (ball (0:ComplexVector n) (2*P.radius) ×ˢ (univ : Set ℝ))) :=
    isOpen_ball.prod (isOpen_ball.prod isOpen_univ)
  have hmem : (theta,(z,t)) ∈ ball (0:Param) R ×ˢ
      (ball (0:ComplexVector n) (2*P.radius) ×ˢ (univ : Set ℝ)) := ⟨ha,hz,mem_univ t⟩
  exact (hSmooth q).contDiffAt (hs.mem_nhds hmem)

theorem coeffParamJet_contDiffAt (k : ℕ) {theta : Param} (ha : theta ∈ ball 0 R)
    (q : P.centers) {z : ComplexVector n} (hz : z ∈ ball 0 (2*P.radius)) (t : ℝ) :
    ContDiffAt ℝ ∞
      (fun a : Param × (ComplexVector n × ℝ) => coeffParamJet c k a.1 q a.2.1 a.2.2)
      (theta,(z,t)) := by
  exact contDiffAt_parameterJet
    (c := fun a (b : ComplexVector n × ℝ) => c a q b.1 b.2)
    (p := (theta,(z,t))) (coeff_contDiffAt P c hSmooth ha q hz t) k

variable (hT : T ≤ P.radius^2) (hb : beta < 1)
variable (M0 Mz Mt : ℕ → ℝ)
variable (hM0 : ∀ k, 0 ≤ M0 k) (hMz : ∀ k, 0 ≤ Mz k) (hMt : ∀ k, 0 ≤ Mt k)
variable (hMixed : ∀ k theta, theta ∈ ball 0 R → ∀ q z,
  z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
    ‖coeffParamJet c k theta q z t‖ ≤ M0 k ∧
    ‖fderiv ℝ (fun w => coeffParamJet c k theta q w t) z‖ ≤ Mz k ∧
    ‖deriv (fun s => coeffParamJet c k theta q z s) t‖ ≤ Mt k)
include hT hb hM0 hMz hMt hMixed

theorem exists_holder_coefficient_jet (k : ℕ) {theta : Param} (ha : theta ∈ ball 0 R) :
    ∃ u : LocalHolderSpace (ParamJet Param k F) P T beta,
      (∀ q : LocalCylinder P T, localFun _ u q = coeffParamJet c k theta q.1 q.2.1 q.2.2) ∧
      ‖u‖ ≤ mixedHolderBudget P beta (M0 k) (Mz k) (Mt k) := by
  have hzBig : ∀ z : ComplexVector n, z ∈ ball 0 P.radius → z ∈ ball 0 (2*P.radius) :=
    fun z hz => (ball_subset_ball (by linarith [P.radius_pos])) hz
  have hjet : ∀ q z, z ∈ ball 0 P.radius → ∀ t : ℝ,
      ContDiffAt ℝ ∞
        (fun a : Param × (ComplexVector n × ℝ) => coeffParamJet c k a.1 q a.2.1 a.2.2)
        (theta,(z,t)) := fun q z hz t => coeffParamJet_contDiffAt P c hSmooth k ha q (hzBig z hz) t
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
  let u := localMixedElement P hT hb.le (hMz k) (hMt k) (coeffParamJet c k theta)
    hf hzD htD (fun q z hz t ht => (hMixed k theta ha q z hz t ht).1)
    (fun q z hz t ht => (hMixed k theta ha q z hz t ht).2.1)
    (fun q z hz t ht => (hMixed k theta ha q z hz t ht).2.2)
  refine ⟨u, fun q => rfl, ?_⟩
  have hA := hM0 k
  have hZ := hMz k
  have hU := hMt k
  have hrho := P.radius_pos
  dsimp only [u, localMixedElement, mixedHolderBudget]
  apply localOfBounds_norm_le <;> positivity

include hM0 in
/-- All parameter jets have actual Holder lifts, quadratic norm remainders, and the
literal curried Frechet derivatives. This is also the finite-order interface. -/
theorem exists_holder_parameter_jet_lifts :
    ∃ u : (k : ℕ) → Param → LocalHolderSpace (ParamJet Param k F) P T beta,
      (∀ k theta, theta ∈ ball 0 R → ∀ q : LocalCylinder P T,
        localFun _ (u k theta) q = coeffParamJet c k theta q.1 q.2.1 q.2.2) ∧
      (∀ k theta, theta ∈ ball 0 R →
        ‖u k theta‖ ≤ mixedHolderBudget P beta (M0 k) (Mz k) (Mt k)) ∧
      (∀ k theta, theta ∈ ball 0 R →
        HasFDerivAt (u k) ((holderJetDerivativeCLM (P := P) (T := T) (beta := beta) (Param := Param) (F := F) k) (u (k+1) theta)) theta) ∧
      (∀ k x, x ∈ ball 0 R → ∀ y, y ∈ ball 0 R →
        ‖u k y-u k x-(holderJetDerivativeCLM (P := P) (T := T) (beta := beta) (Param := Param) (F := F) k) (u (k+1) x) (y-x)‖ ≤
          mixedHolderBudget P beta (M0 (k+2)) (Mz (k+2)) (Mt (k+2))*‖y-x‖^2) ∧
      ∀ k, ContDiffOn ℝ ∞ (u k) (ball 0 R) := by
  classical
  have hex := exists_holder_coefficient_jet P c hSmooth hT hb M0 Mz Mt hM0 hMz hMt hMixed
  let u : (k : ℕ) → Param → LocalHolderSpace (ParamJet Param k F) P T beta :=
    fun k a => if ha : a ∈ ball 0 R then Classical.choose (hex k ha) else 0
  have hval : ∀ k a, a ∈ ball 0 R → ∀ q : LocalCylinder P T,
      localFun _ (u k a) q = coeffParamJet c k a q.1 q.2.1 q.2.2 := by
    intro k a ha q
    simpa only [u, dif_pos ha] using (Classical.choose_spec (hex k ha)).1 q
  have hnorm : ∀ k a, a ∈ ball 0 R →
      ‖u k a‖ ≤ mixedHolderBudget P beta (M0 k) (Mz k) (Mt k) := by
    intro k a ha
    simpa only [u, dif_pos ha] using (Classical.choose_spec (hex k ha)).2
  have hderiv : ∀ k a, a ∈ ball 0 R → ∀ q : LocalCylinder P T,
      HasFDerivAt (fun b => localFun _ (u k b) q)
        ((jetCurry (Param := Param) (F := F) k) (localFun _ (u (k+1) a) q)) a := by
    intro k a ha q
    have hz : (q.2.1 : ComplexVector n) ∈ ball 0 (2*P.radius) :=
      (ball_subset_ball (by linarith [P.radius_pos])) q.2.1.property
    have hc : ContDiffAt ℝ ∞ (fun b => c b q.1 q.2.1 q.2.2) a :=
      (coeff_contDiffAt P c hSmooth ha q.1 hz q.2.2).comp a
        (contDiffAt_id.prodMk contDiffAt_const)
    rw [hval (k+1) a ha q]
    apply (hasFDerivAt_parameterJet hc k).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds ha] with b hb
    exact hval k b hb q
  let H := fun k => mixedHolderBudget P beta (M0 k) (Mz k) (Mt k)
  have hH : ∀ k, 0 ≤ H k := fun k => mixedHolderBudget_nonneg P beta (hM0 k) (hMz k) (hMt k)
  refine ⟨u,hval,hnorm,?_,?_,?_⟩
  · intro k a ha
    exact holder_parameterJet_hasFDerivAt (convex_ball 0 R) isOpen_ball u k
      (fun j _ b hb => hderiv j b hb) (hH (k+2)) (hnorm (k+2)) ha
  · intro k x hx y hy
    exact holder_parameterJet_remainder_le (convex_ball 0 R) u k
      (fun j _ b hb => hderiv j b hb) (hH (k+2)) (hnorm (k+2)) hx hy
  · exact holder_parameterJet_contDiffOn (convex_ball 0 R) isOpen_ball u hderiv H hH hnorm

include hM0 in
/-- The requested coefficient lift. All assumptions are ordinary finite-coordinate
mixed derivative bounds on one parameter ball. -/
theorem exists_holder_parameter_lift (hR : 0 < R) (hT0 : 0 < T) (hb0 : 0 < beta) :
    ∃ cHat : Param → LocalHolderSpace F P T beta,
      ContDiffOn ℝ ∞ cHat (ball 0 R) ∧
      ∀ theta ∈ ball 0 R, ∀ q : LocalCylinder P T,
        localFun F (cHat theta) q = c theta q.1 q.2.1 q.2.2 := by
  obtain ⟨u,hval,-,-,-,hsmooth⟩ :=
    exists_holder_parameter_jet_lifts P c hSmooth hT hb M0 Mz Mt hM0 hMz hMt hMixed
  let L : ParamJet Param 0 F →L[ℝ] F := continuousMultilinearCurryFin0 ℝ Param F
  refine ⟨fun a => localMapCLM L (u 0 a), (hsmooth 0).continuousLinearMap_comp (localMapCLM L), ?_⟩
  intro a ha q
  change L (localFun _ (u 0 a) q) = _
  rw [hval 0 a ha q]
  rfl

include hM0 in
theorem exists_banach_parameter_lift (hR : 0 < R) (hT0 : 0 < T) (hb0 : 0 < beta) :
    ∃ cHat : Param → L17LocalHolderBanachAlgebraAux.LocalHolderBanach F P T beta,
      ContDiffOn ℝ ∞ cHat (ball 0 R) ∧
      ∀ theta ∈ ball 0 R, ∀ q : LocalCylinder P T,
        localFun F (cHat theta).value q = c theta q.1 q.2.1 q.2.2 := by
  obtain ⟨u,hu,hval⟩ := exists_holder_parameter_lift P c hSmooth hT hb M0 Mz Mt
    hM0 hMz hMt hMixed hR hT0 hb0
  exact ⟨fun a => localToBanachCLM (u a),
    hu.continuousLinearMap_comp localToBanachCLM, hval⟩

end Coefficients
end Yau.LeafProofs.L17BootstrapHolderTaylorAux
