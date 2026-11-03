import Yau.Proofs.F01OrdinaryCharts
import Yau.Proofs.F01RescaledDifferential

/-! Recenter the actual original inverse chart by translation. Its coordinate
origin represents a, while spatial derivatives and closed joint jets agree
exactly with the translated original coordinates. No value of chartPt a a
is identified with zero. -/
noncomputable section
open Set
open scoped Manifold ContDiff Pointwise
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def centeredOriginalChart (a : M.Carrier) : OpenPartialHomeomorph (ComplexVector n) M.Carrier :=
  rescaledChart (ordinaryChart a) (chartPt a a) 1 one_ne_zero

theorem centeredOriginalChart_apply (a : M.Carrier) (z : ComplexVector n) :
    centeredOriginalChart a z = chartInv a (chartPt a a + z) := by
  simp only [centeredOriginalChart, rescaledChart_apply, one_smul, ordinaryChart_apply]

theorem centeredOriginalChart_center (a : M.Carrier) : centeredOriginalChart a 0 = a := by
  rw [centeredOriginalChart_apply, add_zero]
  exact (extChartAt (ComplexModel n) a).left_inv (mem_extChartAt_source a)

theorem centeredOriginalChart_contMDiffOn (a : M.Carrier) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞
      (centeredOriginalChart a) (centeredOriginalChart a).source :=
  rescaledChart_contMDiffOn (ordinaryChart a) (ordinaryChart_contMDiffOn a)
    (chartPt a a) 1 one_ne_zero

theorem centeredOriginalChart_inverse_contMDiffOn (a : M.Carrier) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞
      (centeredOriginalChart a).symm (centeredOriginalChart a).target :=
  rescaledChart_inverse_contMDiffOn (ordinaryChart a) (ordinaryChart_inverse_contMDiffOn a)
    (chartPt a a) 1 one_ne_zero

theorem centeredOriginalChart_source_iff (a : M.Carrier) (z : ComplexVector n) :
    z ∈ (centeredOriginalChart a).source ↔ chartPt a a + z ∈ chartTarget a := by
  change (z ∈ (univ : Set (ComplexVector n)) ∧
    rescaleHomeomorph (chartPt a a) 1 one_ne_zero z ∈ (ordinaryChart a).source) ↔ _
  simp only [mem_univ, true_and, rescaleHomeomorph_apply, one_smul, ordinaryChart_source]

theorem centeredOriginalChart_closedBall_source (a : M.Carrier) {R : ℝ}
    (hball : Metric.closedBall (chartPt a a) R ⊆ chartTarget a) :
    Metric.closedBall 0 R ⊆ (centeredOriginalChart a).source := by
  intro z hz
  apply (centeredOriginalChart_source_iff a z).mpr
  apply hball
  simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz

theorem centeredOriginalChart_iteratedFDeriv
    (a : M.Carrier) (F : M.Carrier → ℝ) (k : ℕ) (z : ComplexVector n) :
    iteratedFDeriv ℝ k (fun w => F (centeredOriginalChart a w)) z =
      iteratedFDeriv ℝ k (fun w => F (chartInv a w)) (chartPt a a + z) := by
  simpa only [centeredOriginalChart_apply] using
    (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := fun w => F (chartInv a w)) k (chartPt a a) z)

theorem original_chart_joint_translation_domain
    (a : M.Carrier) (R : ℝ) (I : Set ℝ) :
    (chartPt a a, (0 : ℝ)) +ᵥ (Metric.closedBall (0 : ComplexVector n) R ×ˢ I) =
      Metric.closedBall (chartPt a a) R ×ˢ I := by
  change (fun p : ComplexVector n × ℝ => (chartPt a a, (0 : ℝ)) + p) ''
    (Metric.closedBall (0 : ComplexVector n) R ×ˢ I) = _
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa only [Prod.fst_add, Metric.mem_closedBall, dist_eq_norm,
        add_sub_cancel_left, sub_zero] using hq.1
    · simpa only [Prod.snd_add, zero_add] using hq.2
  · intro hp
    refine ⟨(p.1 - chartPt a a, p.2), ⟨?_, hp.2⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hp.1
    · apply Prod.ext
      · change chartPt a a + (p.1 - chartPt a a) = p.1
        abel
      · exact zero_add p.2

theorem centeredOriginalChart_iteratedFDerivWithin_joint
    (a : M.Carrier) (F : M.Carrier → ℝ → ℝ)
    (R : ℝ) (I : Set ℝ) (k : ℕ) (z : ComplexVector n) (t : ℝ) :
    iteratedFDerivWithin ℝ k
      (fun p : ComplexVector n × ℝ => F (centeredOriginalChart a p.1) p.2)
      (Metric.closedBall 0 R ×ˢ I) (z,t) =
    iteratedFDerivWithin ℝ k
      (fun p : ComplexVector n × ℝ => F (chartInv a p.1) p.2)
      (Metric.closedBall (chartPt a a) R ×ˢ I) (chartPt a a + z,t) := by
  have hshift := iteratedFDerivWithin_comp_add_left (𝕜 := ℝ)
    (f := fun p : ComplexVector n × ℝ => F (chartInv a p.1) p.2)
    (s := Metric.closedBall (0 : ComplexVector n) R ×ˢ I) k (chartPt a a, (0 : ℝ)) (z,t)
  rw [original_chart_joint_translation_domain] at hshift
  have hp : (chartPt a a, (0 : ℝ)) + (z,t) = (chartPt a a + z,t) :=
    Prod.ext rfl (zero_add t)
  rw [hp] at hshift
  simpa only [centeredOriginalChart_apply, Prod.fst_add, Prod.snd_add, zero_add] using hshift

end Yau.NodeProofs.F01Aux
