import Yau.Proofs.F03DirectionalJets

/-! Mean-value promotion from genuine source evaluations to operator norm. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {E H B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Actual scalar-source derivative estimates give a bound in the full
operator norm, with one constant before every source. -/
theorem operator_norm_image_sub_le (A : E → H →L[ℝ] B)
    (D : H → E → E →L[ℝ] B) {s : Set E} (hs : Convex ℝ s)
    (hD : ∀ f, ∀ z ∈ s, HasFDerivAt (fun y => A y f) (D f z) z)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ f, ∀ z ∈ s, ‖D f z‖ ≤ C * ‖f‖)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖A y - A x‖ ≤ C * ‖y-x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro f
  have h := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hD f z hz).hasFDerivWithinAt) (hbound f) hx hy
  simpa only [ContinuousLinearMap.sub_apply,mul_assoc,mul_comm ‖f‖,mul_left_comm ‖f‖] using h

/-- If the actual source evaluations have the displayed derivatives and
the derivative field is norm continuous, then the operator-valued map
has that genuine Fréchet derivative. -/
theorem hasFDerivAt_operator_of_apply (A : E → H →L[ℝ] B)
    (D : E → E →L[ℝ] H →L[ℝ] B) {Q : Set E} (hQ : IsOpen Q)
    (hD : ∀ f, ∀ z ∈ Q, HasFDerivAt (fun y => A y f) ((D z).flip f) z)
    {x : E} (hx : x ∈ Q) (hcont : ContinuousAt D x) :
    HasFDerivAt A (D x) x := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have hd : ContinuousAt (fun z : E => D z-D x) x :=
    hcont.sub continuousAt_const
  have hn : ContinuousAt (fun z => ‖D z-D x‖) x := by
    exact (@continuous_norm (E →L[ℝ] H →L[ℝ] B) inferInstance).continuousAt.comp hd
  have hεx : ‖D x-D x‖ < ε := by
    simpa only [sub_self,ContinuousLinearMap.opNorm_zero] using hε
  have hev : ∀ᶠ z in 𝓝 x, z ∈ Q ∧ ‖D z-D x‖ < ε := by
    filter_upwards [hQ.mem_nhds hx,
      hn.eventually (gt_mem_nhds hεx)]
      with z hz hzε
    exact ⟨hz,hzε⟩
  obtain ⟨r,hr,hrball⟩ := Metric.mem_nhds_iff.mp hev
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hε.le (norm_nonneg _))
  intro f
  have hb (z : E) (hz : z ∈ Metric.ball x r) :
      ‖((D z).flip f) - ((D x).flip f)‖ ≤ ε * ‖f‖ := by
    have heq : ((D z).flip f) - ((D x).flip f) = ((D z-D x).flip f) := by
      ext v
      rfl
    rw [heq]
    exact ((D z-D x).flip.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (by simpa only [ContinuousLinearMap.opNorm_flip] using
        (hrball hz).2.le) (norm_nonneg f))
  have h := (convex_ball x r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hD f z (hrball hz).1).hasFDerivWithinAt) hb
    (Metric.mem_ball_self hr) hy
  simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.flip_apply,
    mul_assoc,mul_comm ‖f‖,mul_left_comm ‖f‖] using h

end Yau.Proofs.F03Aux
