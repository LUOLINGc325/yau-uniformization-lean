import Yau.Proofs.F03DirichletRieszKernel
import Yau.Proofs.F03DirichletClassicalPairing

/-! A whole-volume representative of each true kernel row is its actual Riesz vector. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletKernelCandidate_row_ambient_ae (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t)
    (x : M.Carrier) (hx : x ∈ Ω) :
    dirichletKernelCandidate g hK μ hμ Ω hΩ t x =ᵐ[μ]
      (l2ZeroExtension μ Ω hΩ.measurableSet
        (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht) : M.Carrier → ℝ) := by
  rw [dirichletKernelCandidate_row_classical g hK μ hμ Ω hΩ ht x hx]
  have hsem := dirichletHeatEvaluationVector_semigroup g hK μ hμ Ω hΩ x hx
    (half_pos ht) (half_pos ht).le
  have hvec : dirichletHeat g μ hμ Ω (t/2)
      (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx (t/2) (half_pos ht))=
      dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht := by
    simpa only [add_halves] using hsem.symm
  simpa only [hvec] using dirichletClassicalHeat_ambient_ae g hK μ hμ Ω hΩ
    (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx (t/2) (half_pos ht)) (half_pos ht)

end Yau.Proofs.F03Aux
