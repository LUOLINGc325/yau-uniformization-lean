import Yau.Proofs.F03KernelTerminalDomination

/-! Actual constants plus the terminal density dominate every admissible unbounded profile. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_terminal_profile_integrable
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    (f : Pt X → ℝ) (hfμ : AEStronglyMeasurable f μ) {A : ℝ} (hA : 0 ≤ A)
    (hBound : ∀ y,|f y| ≤ A*(1+ρ y T)) {b : ℝ} (hb : 0 < b) (x : Pt X) :
    Integrable (fun y => dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*f y) μ := by
  have hMass := (dirichletMinimalKernelCandidate_mass X.metric X.kahler_metric μ hμ O hO hb x).1
  have hDensity := dirichletMinimalKernel_terminal_density_integrable X o h U P ρ hf hT μ hμ O hO hb x
  apply ((hMass.add hDensity).const_mul A).mono'
    ((kernelSmooth_univ_continuous_right _
      (dirichletMinimalKernelCandidate_joint_smooth X.metric X.kahler_metric μ hμ O hO) hb x).aestronglyMeasurable.mul hfμ)
  apply ae_of_all μ
  intro y
  have hK0 := dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb x y
  change |dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*f y| ≤
    A*(dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y+
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*ρ y T)
  rw [abs_mul,abs_of_nonneg hK0]
  convert mul_le_mul_of_nonneg_left (hBound y) hK0 using 1 <;> ring

end Yau.Proofs.F03Aux
