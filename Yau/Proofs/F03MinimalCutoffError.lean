import Yau.Proofs.F03MinimalBoundedEvolution

/-! Genuine bounded-data localization error from the proved sub-Markov mass. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

theorem dirichletMinimalKernelCandidate_cutoff_error
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f η : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ) (hη : AEStronglyMeasurable η μ)
    (hηrange : ∀ y, η y ∈ Icc (0 : ℝ) 1) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y, |f y| ≤ B) {t : ℝ} (ht : 0 < t) (x : M.Carrier) :
    |(∫ y, dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*f y ∂μ)-
      (∫ y, dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*(η y*f y) ∂μ)| ≤
      B*(1-∫ y, dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*η y ∂μ) := by
  let H := dirichletMinimalKernelCandidate g hK μ hμ O hO t x
  have hH : ∀ y, 0 ≤ H y := dirichletMinimalKernelCandidate_nonneg g hK μ hμ O hO ht x
  have hm := dirichletMinimalKernelCandidate_mass g hK μ hμ O hO ht x
  have hηabs : ∀ y, |η y| ≤ 1 := fun y => by rw [abs_of_nonneg (hηrange y).1];exact (hηrange y).2
  have hηf : ∀ y, |η y*f y| ≤ B := by
    intro y
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right (hηabs y) (abs_nonneg (f y))).trans
      (by simpa only [one_mul] using hbound y))
  have hif := dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO f hf ⟨B,hbound⟩ ht x
  have hiηf := dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO
    (fun y => η y*f y) (hη.mul hf) ⟨B,hηf⟩ ht x
  have hiη := dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO η hη ⟨1,hηabs⟩ ht x
  change |(∫ y, H y*f y ∂μ)-(∫ y, H y*(η y*f y) ∂μ)| ≤ B*(1-∫ y, H y*η y ∂μ)
  calc
    _ = |∫ y, H y*f y-H y*(η y*f y) ∂μ| := by rw [integral_sub hif hiηf]
    _ ≤ ∫ y, |H y*f y-H y*(η y*f y)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ y, B*(H y-H y*η y) ∂μ := by
      apply integral_mono (hif.sub hiηf).abs ((hm.1.sub hiη).const_mul B)
      intro y
      change |H y*f y-H y*(η y*f y)| ≤ B*(H y-H y*η y)
      have hd : 0 ≤ H y-H y*η y := sub_nonneg.mpr
        (mul_le_of_le_one_right (hH y) (hηrange y).2)
      have heq : H y*f y-H y*(η y*f y)=(H y-H y*η y)*f y := by ring
      rw [heq,abs_mul,abs_of_nonneg hd,mul_comm B]
      exact mul_le_mul_of_nonneg_left (hbound y) hd
    _ = B*((∫ y, H y ∂μ)-(∫ y, H y*η y ∂μ)) := by
      rw [integral_const_mul,integral_sub hm.1 hiη]
    _ ≤ B*(1-∫ y, H y*η y ∂μ) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hm.2.2 _) hB

end Yau.Proofs.F03Aux
