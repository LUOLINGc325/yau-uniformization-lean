import Yau.Proofs.V03SignedTensorCoefficients
import Yau.Proofs.V03CurrentFactors
import Yau.Proofs.V03QuadraticBoundaryCurrentEstimate
import Yau.Proofs.V03ActualEuclideanEnergyDerivative

/-! Every term of the actual finite signed current expansion has one
uniform bound before all original discs, frames, columns, and realizations. -/

open scoped Topology ContDiff Matrix
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def realizedCurrentAtom (d : VariationData X q)
    (B : CotangentPoint X.manifold → Matrix (Fin q) (Fin q) ℂ)
    (F : VariationDisc X) (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (i₁ i₂ : Option (Fin q)) (k : TensorFirstCoefficientIndex q)
    (s : Fin 4) (w : Fin q ⊕ Fin q) (θ : ℝ) : ℝ :=
  (star (currentVelocityFactor (ambientVelocity d F E l h α) i₁ (circlePoint θ)) *
    tensorCurrentCoefficient d.G B k s (F.f (circlePoint θ)) *
    currentVelocityFactor (ambientVelocity d F E l h α) i₂ (circlePoint θ) *
    holomorphicAngularTrace (currentDerivativeFunction d.G F.f (ambientVelocity d F E l h α) w) θ).re

theorem realizedCurrentAtom_uniform_bound {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ)
    {B : CotangentPoint X.manifold → Matrix (Fin q) (Fin q) ℂ}
    (hB : ∀ x b c, ContDiffOn ℝ ∞ (fun z => B (cotangentChartInv x z) b c) (cotangentTarget x))
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
      (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      RealizesFirstField d j a F E l h α fz R →
      ∀ (i₁ i₂ : Option (Fin q)) (k : TensorFirstCoefficientIndex q) (s : Fin 4) (w : Fin q ⊕ Fin q),
      |∫ θ in (-Real.pi)..Real.pi, realizedCurrentAtom d B F E l h α i₁ i₂ k s w θ| ≤
        C * (1 + (variationEnergy d j F).toReal +
          (boundaryDSq (fun θ => l (circlePoint θ))).toReal) := by
  obtain ⟨Cv, hCv, hVel⟩ := ambientVelocity_uniform_boundaryDSq hd j a L hL
  obtain ⟨CB, M, hCB, hM, hCoeff⟩ := tensorCurrentCoefficients_uniform_boundary_control hd j hB
  let Cg : ℝ := (2 * Real.pi)⁻¹
  have hCg : 0 ≤ Cg := by dsimp only [Cg]; positivity
  let CW : ℝ := Cv + Cg
  have hCW : 0 ≤ CW := add_nonneg hCv hCg
  obtain ⟨C, hC, hAtom⟩ := quadraticDerivativeCurrent_uniform_bound (L + 1) M Cv CB Cv CW
    (by linarith) hM hCW
  refine ⟨C, hC, fun F E l h α fz R hF hE hl hlL hR i₁ i₂ k s w => ?_⟩
  let V := ambientVelocity d F E l h α
  let T : ENNReal := 1 + variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ))
  have hEn : variationEnergy d j F ≠ ⊤ := hF.2.2.2.2.2.2.2.2
  have hDl := holomorphicColumn_boundaryDSq_ne_top hl
  have hT : T ≠ ⊤ := by dsimp only [T]; finiteness
  have hEnT : variationEnergy d j F ≤ T := (le_add_left le_rfl).trans (le_add_right le_rfl)
  have hTr : T.toReal = 1 + (variationEnergy d j F).toReal +
      (boundaryDSq (fun θ => l (circlePoint θ))).toReal := by
    dsimp only [T]
    rw [ENNReal.toReal_add (by finiteness : 1 + variationEnergy d j F ≠ ⊤) hDl,
      ENNReal.toReal_add ENNReal.one_ne_top hEn, ENNReal.toReal_one]
  have hV : ContDiffOn ℂ ∞ V (Metric.closedBall (0 : ℂ) 1) :=
    realized_ambientVelocity_contDiffOn hd j a F E l h α fz R hR
  have hVn (θ : ℝ) : ‖V (circlePoint θ)‖ ≤ L :=
    ambientVelocity_boundary_norm_le d hd j a hL F hF E hE l hlL h α fz R hR θ
  have hVD : boundaryDSq (fun θ b => V (circlePoint θ) b) ≤ ENNReal.ofReal Cv * T :=
    hVel F E l h α fz R hF hE hl hlL hR
  let u : ℝ → ℂ := fun θ => currentVelocityFactor V i₁ (circlePoint θ)
  let v : ℝ → ℂ := fun θ => currentVelocityFactor V i₂ (circlePoint θ)
  let b : ℝ → ℂ := fun θ => tensorCurrentCoefficient d.G B k s (F.f (circlePoint θ))
  let f := currentDerivativeFunction d.G F.f V w
  have hu : Continuous u := (currentVelocityFactor_contDiffOn hV i₁).continuousOn.comp_continuous
    circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hv : Continuous v := (currentVelocityFactor_contDiffOn hV i₂).continuousOn.comp_continuous
    circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hb : Continuous b := cotangentCoefficient_trace_continuous hd
    (fun x => tensorCurrentCoefficient_chart_contDiffOn hd.2.2.2.2.1 hB k s x) hF
  have hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1) :=
    currentDerivativeFunction_contDiffOn hd.2.2.2.2.1.1 hF.1 hV w
  have hDu : boundaryDSq (fun θ (_ : Unit) => u θ) ≤ ENNReal.ofReal Cv * T :=
    (currentVelocityFactor_boundaryDSq_le V i₁).trans hVD
  have hDv : boundaryDSq (fun θ (_ : Unit) => v θ) ≤ ENNReal.ofReal Cv * T :=
    (currentVelocityFactor_boundaryDSq_le V i₂).trans hVD
  have hDb : boundaryDSq (fun θ (_ : Unit) => b θ) ≤ ENNReal.ofReal CB * T :=
    ((hCoeff F hF k s).2).trans (mul_le_mul' le_rfl hEnT)
  have hDW : boundaryDSq (fun θ (_ : Unit) => f (circlePoint θ)) ≤ ENNReal.ofReal CW * T := by
    have hCG : ENNReal.ofReal Cg ≤ ENNReal.ofReal CW := ENNReal.ofReal_le_ofReal (by dsimp only [CW]; linarith)
    have hCV : ENNReal.ofReal Cv ≤ ENNReal.ofReal CW := ENNReal.ofReal_le_ofReal (by dsimp only [CW]; linarith)
    cases w with
    | inl c =>
      exact (boundaryDSq_component_le (fun θ b => d.G (F.f (circlePoint θ)) b) c).trans
        ((admissible_ambientTrace_boundaryDSq_le_energy hd j hF).trans (mul_le_mul' hCG hEnT))
    | inr c =>
      exact (boundaryDSq_component_le (fun θ b => V (circlePoint θ) b) c).trans
        (hVD.trans (mul_le_mul' hCV le_rfl))
  have hh := hAtom T hT u b v (fun θ => f (circlePoint θ)) (holomorphicAngularTrace f)
    hu hb hv (holomorphicAngularTrace_continuous hf)
    (circleTrace_periodic (currentVelocityFactor V i₁))
    (circleTrace_periodic (fun ζ => tensorCurrentCoefficient d.G B k s (F.f ζ)))
    (circleTrace_periodic (currentVelocityFactor V i₂)) (circleTrace_periodic f)
    (holomorphicAngularTrace_periodic f) (hasDerivAt_holomorphic_boundary hf)
    (currentVelocityFactor_boundary_norm_le hL hVn i₁)
    (hCoeff F hF k s).1 (currentVelocityFactor_boundary_norm_le hL hVn i₂)
    hDu hDb hDv hDW
  simpa only [realizedCurrentAtom, u, v, b, f, V, hTr] using hh

end Yau.Blueprint.V03Proof
