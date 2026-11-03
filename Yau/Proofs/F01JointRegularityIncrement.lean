import Yau.Proofs.F01JointDerivativeFromPartials

/-! Actual continuous space and time derivatives lift finite joint
regularity by one order. The derivative is the computed coproduct
of the two partial derivatives. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem joint_contDiffOn_succ_of_space_time_partials
    (f : E × ℝ → F) (A : E × ℝ → E →L[ℝ] F) (B : E × ℝ → F)
    {W : Set (E × ℝ)} (hW : IsOpen W) (m : ℕ)
    (hSpace : ∀ p ∈ W, HasFDerivAt (fun x => f (x, p.2)) (A p) p.1)
    (hTime : ∀ p ∈ W, HasDerivAt (fun t => f (p.1, t)) (B p) p.2)
    (hA : ContDiffOn ℝ (m : ℕ∞ω) A W) (hB : ContDiffOn ℝ (m : ℕ∞ω) B W) :
    ContDiffOn ℝ ((m : ℕ∞ω) + 1) f W := by
  have hJoint (p : E × ℝ) (hp : p ∈ W) :
      HasFDerivAt f ((A p).coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight (B p))) p :=
    joint_hasFDerivAt_of_space_time_partials f A B p
      ((show ∀ᶠ q in 𝓝 p, q ∈ W from hW.mem_nhds hp).mono (fun q hq => hSpace q hq))
      ((show ∀ᶠ q in 𝓝 p, q ∈ W from hW.mem_nhds hp).mono (fun q hq => hTime q hq))
      (hA.continuousOn.continuousAt (hW.mem_nhds hp))
      (hB.continuousOn.continuousAt (hW.mem_nhds hp))
  have hLeft : ContDiffOn ℝ (m : ℕ∞ω)
      (fun p => (A p).comp (ContinuousLinearMap.fst ℝ E ℝ)) W :=
    hA.clm_comp contDiffOn_const
  have hClock : ContDiffOn ℝ (m : ℕ∞ω)
      (fun p => (ContinuousLinearMap.id ℝ ℝ).smulRight (B p)) W :=
    contDiffOn_const.smulRight hB
  have hRight : ContDiffOn ℝ (m : ℕ∞ω)
      (fun p => ((ContinuousLinearMap.id ℝ ℝ).smulRight (B p)).comp (ContinuousLinearMap.snd ℝ E ℝ)) W :=
    hClock.clm_comp contDiffOn_const
  have hD : ContDiffOn ℝ (m : ℕ∞ω)
      (fun p => (A p).coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight (B p))) W := by
    apply (hLeft.add hRight).congr
    intro p hp
    apply ContinuousLinearMap.ext
    intro q
    rfl
  apply (contDiffOn_succ_iff_fderiv_of_isOpen hW).mpr
  refine ⟨(fun p hp => (hJoint p hp).differentiableAt.differentiableWithinAt), by simp, ?_⟩
  exact hD.congr (fun p hp => (hJoint p hp).fderiv)

end Yau.NodeProofs.F01Aux
