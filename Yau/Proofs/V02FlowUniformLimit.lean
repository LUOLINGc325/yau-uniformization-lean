import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.MetricSpace.Cauchy

/-! Operator Cauchy estimates and joint holomorphic uniform limits.
The domain is an arbitrary complex normed space; derivatives below are actual
Fréchet derivatives in that whole domain. -/

open scoped Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.Blueprint.V02FlowProof

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem norm_fderiv_sub_le_of_cauchy {O : Set P} {f g : P → F}
    {a y : P} {r A : ℝ}
    (hO : IsOpen O) (hf : DifferentiableOn ℂ f O)
    (hg : DifferentiableOn ℂ g O) (hr : 0 < r) (hA : 0 ≤ A)
    (hball : closedBall a (2 * r) ⊆ O)
    (hbound : ∀ z ∈ closedBall a (2 * r), ‖f z - g z‖ ≤ A)
    (hy : y ∈ closedBall a r) :
    ‖fderiv ℂ f y - fderiv ℂ g y‖ ≤ A / r := by
  have hyO : y ∈ O := hball (closedBall_subset_closedBall (by linarith) hy)
  have hfy := (hf y hyO).differentiableAt (hO.mem_nhds hyO)
  have hgy := (hg y hyO).differentiableAt (hO.mem_nhds hyO)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hA hr.le)
  intro v hv
  have hline : ∀ t ∈ closedBall (0 : ℂ) r,
      y + t • v ∈ closedBall a (2 * r) := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    have ht' : ‖t‖ ≤ r := by simpa using ht
    calc
      ‖y + t • v - a‖ = ‖(y - a) + t • v‖ := by congr 1; abel
      _ ≤ ‖y - a‖ + ‖t • v‖ := norm_add_le _ _
      _ = ‖y - a‖ + ‖t‖ := by rw [norm_smul, hv, mul_one]
      _ ≤ 2 * r := by linarith
  have hl : DifferentiableOn ℂ (fun t : ℂ => f (y + t • v) - g (y + t • v))
      (closedBall 0 r) := by
    intro t ht
    have hmem := hball (hline t ht)
    exact (((hf _ hmem).differentiableAt (hO.mem_nhds hmem)).sub
      ((hg _ hmem).differentiableAt (hO.mem_nhds hmem))).comp t
      (((differentiable_id.smul_const v).const_add y).differentiableAt)
      |>.differentiableWithinAt
  have hder : HasDerivAt (fun t : ℂ => f (y + t • v) - g (y + t • v))
      ((fderiv ℂ f y - fderiv ℂ g y) v) 0 := by
    have hlin : HasDerivAt (fun t : ℂ => y + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    have hfg : HasFDerivAt (f - g) (fderiv ℂ f y - fderiv ℂ g y)
        (y + (0 : ℂ) • v) := by
      simpa using hfy.hasFDerivAt.sub hgy.hasFDerivAt
    simpa only [Function.comp_def, Pi.sub_apply, ContinuousLinearMap.coe_sub'] using
      hfg.comp_hasDerivAt 0 hlin
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (hl.diffContOnCl_ball Set.Subset.rfl)
    (fun t ht => hbound _ (hline t (sphere_subset_closedBall ht)))
  simpa only [hder.deriv] using hc

theorem differentiableOn_of_uniform_holomorphic_limit
    {O K : Set P} {f : P → F} {Fseq : ℕ → P → F}
    (hO : IsOpen O) (hOK : O ⊆ K)
    (hF : ∀ m, DifferentiableOn ℂ (Fseq m) O)
    (hlim : TendstoUniformlyOn Fseq f atTop K) :
    DifferentiableOn ℂ f O := by
  classical
  intro p hp
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO p hp
  let r := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hball : closedBall p (2 * r) ⊆ O := by
    intro z hz
    apply hεO
    rw [mem_ball]
    have hz' := mem_closedBall.mp hz
    dsimp [r] at hz'
    linarith
  have hsmall : ball p r ⊆ closedBall p (2 * r) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hD : UniformCauchySeqOn (fun m => fderiv ℂ (Fseq m)) atTop (ball p r) := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro η hη
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hlim.uniformCauchySeqOn
      (η * r / 2) (by positivity)
    refine ⟨N, fun m hm n hn y hy => ?_⟩
    rw [dist_eq_norm]
    calc
      ‖fderiv ℂ (Fseq m) y - fderiv ℂ (Fseq n) y‖ ≤ (η * r / 2) / r :=
        norm_fderiv_sub_le_of_cauchy hO (hF m) (hF n) hr (by positivity) hball
          (fun z hz => (by
            simpa only [dist_eq_norm] using (hN m hm n hn z (hOK (hball hz))).le))
          (ball_subset_closedBall hy)
      _ < η := by field_simp; nlinarith
  have hpoint : ∀ y : ball p r, ∃ L : P →L[ℂ] F,
      Tendsto (fun m => fderiv ℂ (Fseq m) y) atTop (𝓝 L) := by
    intro y
    apply cauchySeq_tendsto_of_complete
    apply Metric.cauchySeq_iff.mpr
    intro η hη
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hD η hη
    exact ⟨N, fun m hm n hn => hN m hm n hn y y.2⟩
  choose D hDt using hpoint
  let Dext : P → P →L[ℂ] F := fun y => if hy : y ∈ ball p r then D ⟨y, hy⟩ else 0
  have hDext : ∀ y ∈ ball p r,
      Tendsto (fun m => fderiv ℂ (Fseq m) y) atTop (𝓝 (Dext y)) := by
    intro y hy
    simpa only [Dext, dite_eq_left hy] using hDt ⟨y, hy⟩
  have hder := hasFDerivAt_of_tendstoUniformlyOn isOpen_ball
    (hD.tendstoUniformlyOn_of_tendsto hDext)
    (fun m y hy => ((hF m y (hball (hsmall hy))).differentiableAt
      (hO.mem_nhds (hball (hsmall hy)))).hasFDerivAt)
    (fun y hy => hlim.tendsto_at (hOK (hball (hsmall hy)))) (mem_ball_self hr)
  exact hder.differentiableAt.differentiableWithinAt

end Yau.Blueprint.V02FlowProof
