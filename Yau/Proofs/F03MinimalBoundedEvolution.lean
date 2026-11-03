import Yau.Proofs.F03MinimalKernelMass

/-! Integrable action and the actual sharp sup bound for every bounded datum. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletMinimalKernelCandidate_bounded_source_integrable
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (hbound : ∃ B : ℝ, ∀ y, |f y| ≤ B) {t : ℝ} (ht : 0 < t) (x : M.Carrier) :
    Integrable (fun y => dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*f y) μ := by
  obtain ⟨B,hB⟩ := hbound
  exact (dirichletMinimalKernelCandidate_mass g hK μ hμ O hO ht x).1.mul_bdd hf
    (ae_of_all μ (fun y => by simpa only [Real.norm_eq_abs] using hB y))

theorem dirichletMinimalKernelCandidate_bounded_evolution_le
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ y, |f y| ≤ B)
    {t : ℝ} (ht : 0 < t) (x : M.Carrier) :
    (∫ y, |dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*f y| ∂μ) ≤ B ∧
      |boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t x| ≤ B := by
  have hm := dirichletMinimalKernelCandidate_mass g hK μ hμ O hO ht x
  have hi := dirichletMinimalKernelCandidate_bounded_source_integrable g hK μ hμ O hO f hf
    ⟨B,hbound⟩ ht x
  have hle : (∫ y, |dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*f y| ∂μ) ≤ B := by
    calc
      _ ≤ ∫ y, dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*B ∂μ := by
        apply integral_mono hi.abs (hm.1.mul_const B)
        intro y
        change |dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*f y| ≤
          dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*B
        rw [abs_mul,abs_of_nonneg (dirichletMinimalKernelCandidate_nonneg g hK μ hμ O hO ht x y)]
        exact mul_le_mul_of_nonneg_left (hbound y)
          (dirichletMinimalKernelCandidate_nonneg g hK μ hμ O hO ht x y)
      _ = (∫ y, dirichletMinimalKernelCandidate g hK μ hμ O hO t x y ∂μ)*B := integral_mul_const B _
      _ ≤ 1*B := mul_le_mul_of_nonneg_right hm.2.2 hB
      _ = B := one_mul B
  refine ⟨hle,?_⟩
  rw [boundedKernelEvolution,if_neg ht.ne']
  exact abs_integral_le_integral_abs.trans hle

end Yau.Proofs.F03Aux
