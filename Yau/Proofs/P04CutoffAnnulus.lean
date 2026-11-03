import Yau.Proofs.P04CanonicalCutoff

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem modelTopDbar_zero_of_eventually_const {F : ComplexVector n → ComplexVector 1}
    {z : ComplexVector n} {c : ComplexVector 1} (hF : F =ᶠ[𝓝 z] fun _ => c) :
    L14Aux.modelTopDbar F z=0 := by
  ext i α
  change wirtBar (fun w => F w α) z (stdVec i)=0
  have heq : (fun w => F w α) =ᶠ[𝓝 z] fun _ => c α :=
    hF.mono (fun w hw => congrArg (fun v => v α) hw)
  rw [wirtBar,heq.fderiv_eq]
  simp

theorem cutoff_model_zero_inner {p : M.Carrier} {χ : ComplexVector n → ℝ} {ρ : ℝ}
    (hone : ∀ z ∈ Metric.closedBall (chartPt p p) ρ, χ z=1)
    {z : ComplexVector n} (hz : z ∈ Metric.ball (chartPt p p) ρ) :
    L14Aux.modelTopDbar (cutoffCoefficient χ) z=0 := by
  apply modelTopDbar_zero_of_eventually_const (c := scalarToCoefficient 1)
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  simp only [cutoffCoefficient,hone w (Metric.ball_subset_closedBall hw),Complex.ofReal_one]

theorem oneFormPushforward_zero_at (p x : M.Carrier)
    (F : ComplexVector n → Fin n → ComplexVector 1) (hF : F (chartPt p x)=0) :
    L14Aux.oneFormPushforward (CanonicalCoefficients M) p F x =
      (0 : BundleDbar.NQForm (CanonicalCoefficients M) 1) x := by
  classical
  change (if hx : x ∈ L14Aux.bundleChartSource (CanonicalCoefficients M) p then
    L14Aux.oneTensorFromCoefficients (CanonicalCoefficients M) p x hx (F (chartPt p x)) else 0)=0
  split_ifs
  · rw [hF,L14Aux.oneTensorFromCoefficients_zero]
  · rfl

/-- The ACTUAL dbar source vanishes on an open neighborhood of the pole;
its compact support therefore stays a positive chart distance away. -/
theorem cutoffDbar_support_avoids_center (p : M.Carrier) {χ : ComplexVector n → ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) (hone : ∀ z ∈ Metric.closedBall (chartPt p p) ρ, χ z=1) :
    p ∉ closure {x | cutoffDbar p χ x ≠ (0 : BundleDbar.NQForm (CanonicalCoefficients M) 1) x} := by
  let O : Set M.Carrier := (extChartAt (ComplexModel n) p).source ∩
    (chartPt p) ⁻¹' Metric.ball (chartPt p p) ρ
  have hO : IsOpen O := (continuousOn_extChartAt (I := ComplexModel n) p).isOpen_inter_preimage
    (isOpen_extChartAt_source p) Metric.isOpen_ball
  have hpO : p ∈ O := ⟨mem_extChartAt_source p,Metric.mem_ball_self hρ⟩
  have hzero (x : M.Carrier) (hx : x ∈ O) :
      cutoffDbar p χ x=(0 : BundleDbar.NQForm (CanonicalCoefficients M) 1) x :=
    oneFormPushforward_zero_at p x _ (cutoff_model_zero_inner hone hx.2)
  have hsub : {x | cutoffDbar p χ x ≠ (0 : BundleDbar.NQForm (CanonicalCoefficients M) 1) x} ⊆ Oᶜ :=
    fun x hx hxO => hx (hzero x hxO)
  exact fun hp => (closure_minimal hsub hO.isClosed_compl hp) hpO

end Yau.Proofs.P04Aux
