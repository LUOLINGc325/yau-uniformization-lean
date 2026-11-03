import Yau.Proofs.F03DirichletKernelEvolution
import Yau.Proofs.F03DirichletKernelSplit

/-! The exact convolution law of the single actual supported kernel. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletKernelCandidate_convolution_integrable (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : M.Carrier) :
    Integrable (fun z => dirichletKernelCandidate g hK μ hμ Ω hΩ a x z *
      dirichletKernelCandidate g hK μ hμ Ω hΩ b z y) μ := by
  by_cases hx : x ∈ Ω
  · by_cases hy : y ∈ Ω
    · have hi := dirichletKernelCandidate_source_integrable g hK μ hμ Ω hΩ ha x hx
        (dirichletKernelCandidate g hK μ hμ Ω hΩ b y)
        (dirichletKernelCandidate_row_scalarL2 g hK μ hμ Ω hΩ hb y hy)
      convert hi using 1
      funext z
      rw [dirichletKernelCandidate_symm g hK μ hμ Ω hΩ hb z y]
    · have hz : (fun z => dirichletKernelCandidate g hK μ hμ Ω hΩ a x z *
          dirichletKernelCandidate g hK μ hμ Ω hΩ b z y) = fun _ => (0 : ℝ) := by
        funext z
        rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ hb z y (Or.inr hy),mul_zero]
      rw [hz]
      simp
  · have hz : (fun z => dirichletKernelCandidate g hK μ hμ Ω hΩ a x z *
        dirichletKernelCandidate g hK μ hμ Ω hΩ b z y) = fun _ => (0 : ℝ) := by
      funext z
      rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ ha x z (Or.inl hx),zero_mul]
    rw [hz]
    simp

/-- The original convolution integral equals the same kernel at the sum
time, for every pair of spatial points including all exterior points. -/
theorem dirichletKernelCandidate_semigroup (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : M.Carrier) :
    dirichletKernelCandidate g hK μ hμ Ω hΩ (a+b) x y =
      ∫ z, dirichletKernelCandidate g hK μ hμ Ω hΩ a x z *
        dirichletKernelCandidate g hK μ hμ Ω hΩ b z y ∂μ := by
  by_cases hx : x ∈ Ω
  · by_cases hy : y ∈ Ω
    · rw [dirichletKernelCandidate_split g hK μ hμ Ω hΩ ha hb x y hx hy,L2.inner_def]
      have hr : (∫ z in Ω, dirichletKernelCandidate g hK μ hμ Ω hΩ a x z *
          dirichletKernelCandidate g hK μ hμ Ω hΩ b z y ∂μ) =
          ∫ z, dirichletKernelCandidate g hK μ hμ Ω hΩ a x z *
            dirichletKernelCandidate g hK μ hμ Ω hΩ b z y ∂μ := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ ha x z (Or.inr hz),zero_mul]
      rw [← hr]
      apply integral_congr_ae
      filter_upwards [dirichletKernelCandidate_row_ae g hK μ hμ Ω hΩ ha x hx,
        dirichletKernelCandidate_row_ae g hK μ hμ Ω hΩ hb y hy] with z hza hzb
      rw [dirichletKernelCandidate_symm g hK μ hμ Ω hΩ hb z y]
      simp only [hza,hzb,RCLike.inner_apply,conj_trivial,mul_comm]
    · have hz : (fun z => dirichletKernelCandidate g hK μ hμ Ω hΩ a x z *
          dirichletKernelCandidate g hK μ hμ Ω hΩ b z y) = fun _ => (0 : ℝ) := by
        funext z
        rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ hb z y (Or.inr hy),mul_zero]
      rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ (add_pos ha hb) x y (Or.inr hy),hz,integral_zero]
  · have hz : (fun z => dirichletKernelCandidate g hK μ hμ Ω hΩ a x z *
        dirichletKernelCandidate g hK μ hμ Ω hΩ b z y) = fun _ => (0 : ℝ) := by
      funext z
      rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ ha x z (Or.inl hx),zero_mul]
    rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ (add_pos ha hb) x y (Or.inl hx),hz,integral_zero]

end Yau.Proofs.F03Aux
