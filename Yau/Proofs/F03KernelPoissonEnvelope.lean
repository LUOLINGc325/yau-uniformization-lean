import Yau.Proofs.F03KernelBandDomination
import Yau.Proofs.F03CenteredFlowEnvelope

/-! The actual centered flow potential discharges every weighted hypothesis of the compact Green error estimate. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_centered_poisson_envelope
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    {ε B : ℝ} (hε : 0 < ε) (hεB : ε ≤ B) (x : Pt X) :
    ∃ E : Pt X → ℝ,Integrable E μ ∧ (∀ y,0 ≤ E y) ∧
      ∀ b ∈ Icc ε B,∀ s ∈ Icc 0 T,∀ y,
      |centeredFlowPotential X U T y s*
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y| ≤ E y ∧
      |centeredFlowPotential X U T y s| * Real.sqrt (gradNormSq X.metric.form (fun z =>
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x z) y) ≤ E y ∧
      |dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*
        laplacian X.metric.form (fun z => centeredFlowPotential X U T z s) y| ≤ E y := by
  obtain ⟨D,hD,hD0,hBound⟩ := dirichletMinimalKernel_positive_band_domination
    X o h U P ρ hf hT.le μ hμ O hO hε hεB x
  let A : ℝ := 2*T+(n:ℝ)+1
  have hA0 : 0 ≤ A := by dsimp [A];positivity
  have hTA : 2*T ≤ A := by dsimp [A];linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnA : (n:ℝ) ≤ A := by dsimp [A];linarith
  refine ⟨fun y => A*D y,hD.const_mul A,fun y => mul_nonneg hA0 (hD0 y),?_⟩
  intro b hb s hs y
  have hb0 : 0 < b := hε.trans_le hb.1
  have hk0 := dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb0 x y
  have hW := (centeredFlowPotential_terminal_envelope X o h U P ρ hf hT hs y).1
  have hLap := centeredFlowPotential_laplacian_bound X o h U P ρ hf hT hs y
  have hEn := hBound b hb y
  constructor
  · rw [abs_mul,abs_of_nonneg hk0]
    calc
      _ ≤ (2*T*ρ y T)*dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y :=
        mul_le_mul_of_nonneg_right hW hk0
      _ = (2*T)*(dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*ρ y T) := by ring
      _ ≤ (2*T)*D y := mul_le_mul_of_nonneg_left hEn.2.2.1 (by positivity)
      _ ≤ A*D y := mul_le_mul_of_nonneg_right hTA (hD0 y)
  constructor
  · calc
      _ ≤ (2*T*ρ y T)*Real.sqrt (gradNormSq X.metric.form (fun z =>
          dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x z) y) :=
        mul_le_mul_of_nonneg_right hW (Real.sqrt_nonneg _)
      _ = (2*T)*(Real.sqrt (gradNormSq X.metric.form (fun z =>
          dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x z) y)*ρ y T) := by ring
      _ ≤ (2*T)*D y := mul_le_mul_of_nonneg_left hEn.2.2.2 (by positivity)
      _ ≤ A*D y := mul_le_mul_of_nonneg_right hTA (hD0 y)
  · rw [abs_mul,abs_of_nonneg hk0]
    calc
      _ ≤ dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*(n:ℝ) :=
        mul_le_mul_of_nonneg_left hLap hk0
      _ ≤ D y*(n:ℝ) := mul_le_mul_of_nonneg_right hEn.1 (Nat.cast_nonneg n)
      _ ≤ A*D y := by nlinarith [mul_le_mul_of_nonneg_right hnA (hD0 y)]

end Yau.Proofs.F03Aux
