import Yau.Proofs.V03AmbientScalarDifferential
import Yau.Proofs.V03FiniteCoefficientBoundaryControl

/-! One finite family consists of the actual ambient tensor entries and
the ambient differentials of their real and imaginary parts. All coefficients
are defined by native derivatives and have one uniform boundary constant. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

def tensorRealCoefficient (B : CotangentPoint M → Matrix (Fin q) (Fin q) ℂ)
    (a b : Fin q) (k : Fin 2) (y : CotangentPoint M) : ℝ :=
  if k = 0 then (B y a b).re else (B y a b).im

abbrev TensorFirstCoefficientIndex (q : ℕ) :=
  (Fin q × Fin q) ⊕ ((Fin q × Fin q) × (Fin q × Fin 2))

def tensorFirstCoefficient (G : CotangentPoint M → ComplexVector q)
    (B : CotangentPoint M → Matrix (Fin q) (Fin q) ℂ) :
    TensorFirstCoefficientIndex q → CotangentPoint M → ℂ
  | .inl ab, y => B y ab.1 ab.2
  | .inr i, y => ambientScalarCovector G (tensorRealCoefficient B i.1.1 i.1.2 i.2.2) y i.2.1

theorem tensorRealCoefficient_chart_contDiffOn
    {B : CotangentPoint M → Matrix (Fin q) (Fin q) ℂ}
    (hB : ∀ x a b, ContDiffOn ℝ ∞ (fun z => B (cotangentChartInv x z) a b) (cotangentTarget x))
    (a b : Fin q) (k : Fin 2) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => tensorRealCoefficient B a b k (cotangentChartInv x z))
      (cotangentTarget x) := by
  by_cases hk : k = 0
  · simp only [tensorRealCoefficient, hk, ↓reduceIte]
    exact Complex.reCLM.contDiff.comp_contDiffOn (hB x a b)
  · simp only [tensorRealCoefficient, hk, ↓reduceIte]
    exact Complex.imCLM.contDiff.comp_contDiffOn (hB x a b)

theorem tensorFirstCoefficient_chart_contDiffOn
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {B : CotangentPoint M → Matrix (Fin q) (Fin q) ℂ}
    (hB : ∀ x a b, ContDiffOn ℝ ∞ (fun z => B (cotangentChartInv x z) a b) (cotangentTarget x))
    (i : TensorFirstCoefficientIndex q) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => tensorFirstCoefficient G B i (cotangentChartInv x z))
      (cotangentTarget x) := by
  cases i with
  | inl ab => exact hB x ab.1 ab.2
  | inr i =>
    exact ambientScalarCovector_chart_entry_contDiffOn hG
      (tensorRealCoefficient_chart_contDiffOn hB i.1.1 i.1.2 i.2.2) x i.2.1

theorem tensorFirstCoefficients_uniform_boundary_control {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j : ℕ)
    {B : CotangentPoint X.manifold → Matrix (Fin q) (Fin q) ℂ}
    (hB : ∀ x a b, ContDiffOn ℝ ∞ (fun z => B (cotangentChartInv x z) a b) (cotangentTarget x)) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ F : VariationDisc X,
      AdmissibleVariationDisc d j F → ∀ i : TensorFirstCoefficientIndex q,
      (∀ θ, ‖tensorFirstCoefficient d.G B i (F.f (circlePoint θ))‖ ≤ M) ∧
      boundaryDSq (fun θ (_ : Unit) => tensorFirstCoefficient d.G B i (F.f (circlePoint θ))) ≤
        ENNReal.ofReal C * variationEnergy d j F :=
  finiteCoefficients_uniform_boundary_control hd j
    (tensorFirstCoefficient_chart_contDiffOn hd.2.2.2.2.1 hB)

end Yau.Blueprint.V03Proof
