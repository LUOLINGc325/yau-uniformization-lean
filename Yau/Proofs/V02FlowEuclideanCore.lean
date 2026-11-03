import Yau.Proofs.V02FlowPicardFixedPoint
import Yau.Proofs.V02FlowTimeDerivative
import Yau.Proofs.V02FlowJets

/-! A genuine joint holomorphic flow from the closed-product fixed point. -/

open scoped Topology ContDiff NNReal
open Filter MeasureTheory Metric

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open V03Proof

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V]

def picardFlow {a : V} {d R : ℝ} (u : C(picardClosedDomain a d R, V))
    (p : ℂ × V) : V := by
  classical
  exact if hp : p ∈ picardClosedDomain a d R then u ⟨p, hp⟩ else p.2

theorem picardFlow_eq_extension {a : V} {d R : ℝ}
    (u : C(picardClosedDomain a d R, V)) {p : ℂ × V}
    (hp : p ∈ picardClosedDomain a d R) : picardFlow u p = compactExtension u p := by
  classical
  simp only [picardFlow, dite_eq_left hp, compactExtension_of_mem _ hp]

theorem exists_quantitative_holomorphic_flow {a : V} {d R M : ℝ} {L : ℝ≥0}
    {Ω : Set V} {W : V → V} (hΩ : IsOpen Ω) (hW : DifferentiableOn ℂ W Ω)
    (hd : 0 < d) (hR : 0 < R) (hM : 0 ≤ M)
    (hball : closedBall a (2 * d) ⊆ Ω)
    (hbound : ∀ z ∈ closedBall a (2 * d), ‖W z‖ ≤ M)
    (hLip : LipschitzOnWith L W (closedBall a (2 * d)))
    (hRM : R * M ≤ d / 2) (hRL : R * L ≤ 1 / 2) :
    ∃ Φ : ℂ × V → V,
      (∀ x, Φ (0, x) = x) ∧
      ContDiffOn ℂ ∞ Φ (picardOpenDomain a d R) ∧
      ContinuousOn Φ (picardClosedDomain a d R) ∧
      (∀ p ∈ picardClosedDomain a d R, ‖Φ p - p.2‖ ≤ ‖p.1‖ * M) ∧
      (∀ t ∈ ball (0 : ℂ) R, ∀ x ∈ ball a d,
        Φ (t, x) ∈ ball a (2 * d) ∧
        HasDerivAt (fun z : ℂ => Φ (z, x)) (W (Φ (t, x))) t) := by
  classical
  obtain ⟨u, hu, hfix⟩ := exists_picard_fixedPoint hΩ hW hd.le hR.le hM hball hbound hLip
    (hRM.trans (by linarith)) hRL
  let Φ := picardFlow u
  have hext : ∀ p ∈ picardClosedDomain a d R, Φ p = compactExtension u p :=
    fun p hp => picardFlow_eq_extension u hp
  have hdiff : DifferentiableOn ℂ Φ (picardOpenDomain a d R) :=
    hu.1.congr (fun p hp => hext p (picardOpenDomain_subset_closedDomain a d R hp))
  have hcont : ContinuousOn Φ (picardClosedDomain a d R) :=
    (continuousOn_compactExtension u).congr hext
  have hΦfix : ∀ p ∈ picardClosedDomain a d R,
      Φ p = p.2 + p.1 • ∫ s in (0 : ℝ)..1, W (Φ ((s : ℂ) * p.1, p.2)) := by
    intro p hp
    rw [hext p hp, compactExtension_of_mem u hp, hfix ⟨p, hp⟩]
    unfold picardRaw picardIntegral
    congr 1
    apply congrArg (fun v => p.1 • v)
    apply intervalIntegral.integral_congr
    intro s hs
    have hm := picardRadialLinear_mem_closed (by simpa using hs) hp
    exact congrArg W (hext _ hm).symm
  have hdispl : ∀ p ∈ picardClosedDomain a d R, ‖Φ p - p.2‖ ≤ ‖p.1‖ * M := by
    intro p hp
    rw [hext p hp, compactExtension_of_mem u hp, hfix ⟨p, hp⟩]
    exact picardRaw_displacement hbound hu hp
  have hΦimage : ∀ p ∈ picardClosedDomain a d R, Φ p ∈ closedBall a (2 * d) := by
    intro p hp
    rw [hext p hp]
    exact picardExtension_image hu hp
  refine ⟨Φ, ?_, complex_holomorphic_contDiffOn (picardOpenDomain_isOpen a d R) hdiff,
    hcont, hdispl, ?_⟩
  · intro x
    by_cases hx : (0, x) ∈ picardClosedDomain a d R
    · simpa using hΦfix (0, x) hx
    · simp only [Φ, picardFlow, dite_eq_right hx]
  · intro t ht x hx
    have hp : (t, x) ∈ picardClosedDomain a d R :=
      picardOpenDomain_subset_closedDomain a d R ⟨ht, hx⟩
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      have hdx : dist (Φ (t, x)) x ≤ R * M := by
        rw [dist_eq_norm]
        exact (hdispl (t, x) hp).trans
          (mul_le_mul_of_nonneg_right (by simpa using (mem_ball.mp ht).le) hM)
      have hxa := mem_ball.mp hx
      have htri := dist_triangle (Φ (t, x)) x a
      linarith
    · have hslice : DifferentiableOn ℂ (fun z : ℂ => Φ (z, x)) (ball 0 R) :=
        hdiff.comp (differentiable_id.prodMk (differentiable_const x)).differentiableOn
          (fun z hz => ⟨hz, hx⟩)
      have hg : DifferentiableOn ℂ (fun z : ℂ => W (Φ (z, x))) (ball 0 R) :=
        hW.comp hslice (fun z hz => hball (hΦimage (z, x)
          (picardOpenDomain_subset_closedDomain a d R ⟨hz, hx⟩)))
      have hder := (radialIntegral_hasDerivAt hg ht).const_add x
      apply hder.congr_of_eventuallyEq
      filter_upwards [isOpen_ball.mem_nhds ht] with z hz
      exact hΦfix (z, x) (picardOpenDomain_subset_closedDomain a d R ⟨hz, hx⟩)

end Yau.Blueprint.V02FlowProof
