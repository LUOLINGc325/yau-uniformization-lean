import Yau.Proofs.V03TensorFirstCoefficients

/-! The finitely many actual coefficients of the signed current expansion
have one native boundary bound before every original admissible disc. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def signedCurrentCoefficient (c : ℂ) (k : Fin 4) : ℂ :=
  if k = 0 then c else if k = 1 then -Complex.I * c else if k = 2 then star c else -Complex.I * star c

def tensorCurrentCoefficient {n q : ℕ} {M : ComplexManifold n}
    (G : CotangentPoint M → ComplexVector q) (B : CotangentPoint M → Matrix (Fin q) (Fin q) ℂ)
    (i : TensorFirstCoefficientIndex q) (k : Fin 4) (y : CotangentPoint M) : ℂ :=
  signedCurrentCoefficient (tensorFirstCoefficient G B i y) k

theorem tensorCurrentCoefficient_chart_contDiffOn {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {B : CotangentPoint M → Matrix (Fin q) (Fin q) ℂ}
    (hB : ∀ x a b, ContDiffOn ℝ ∞ (fun z => B (cotangentChartInv x z) a b) (cotangentTarget x))
    (i : TensorFirstCoefficientIndex q) (k : Fin 4) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => tensorCurrentCoefficient G B i k (cotangentChartInv x z))
      (cotangentTarget x) := by
  have hc := tensorFirstCoefficient_chart_contDiffOn hG hB i x
  have hs : ContDiffOn ℝ ∞ (fun z => star (tensorFirstCoefficient G B i (cotangentChartInv x z)))
      (cotangentTarget x) := by
    apply (Complex.conjCLE.contDiff.comp_contDiffOn hc).congr
    intro z _
    rfl
  by_cases h0 : k = 0
  · simpa only [tensorCurrentCoefficient, signedCurrentCoefficient, h0, Fin.reduceEq, ↓reduceIte] using hc
  by_cases h1 : k = 1
  · simpa only [tensorCurrentCoefficient, signedCurrentCoefficient, h0, h1, Fin.reduceEq, ↓reduceIte] using
      (contDiffOn_const.mul hc : ContDiffOn ℝ ∞ (fun z => -Complex.I * tensorFirstCoefficient G B i
        (cotangentChartInv x z)) (cotangentTarget x))
  by_cases h2 : k = 2
  · simpa only [tensorCurrentCoefficient, signedCurrentCoefficient, h0, h1, h2, Fin.reduceEq, ↓reduceIte,
      Complex.star_def, Function.comp_def] using hs
  · simpa only [tensorCurrentCoefficient, signedCurrentCoefficient, h0, h1, h2, Fin.reduceEq, ↓reduceIte,
      Complex.star_def, Function.comp_def] using
      (contDiffOn_const.mul hs : ContDiffOn ℝ ∞ (fun z => -Complex.I *
        star (tensorFirstCoefficient G B i (cotangentChartInv x z))) (cotangentTarget x))

theorem tensorCurrentCoefficients_uniform_boundary_control {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j : ℕ)
    {B : CotangentPoint X.manifold → Matrix (Fin q) (Fin q) ℂ}
    (hB : ∀ x a b, ContDiffOn ℝ ∞ (fun z => B (cotangentChartInv x z) a b) (cotangentTarget x)) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ F : VariationDisc X,
      AdmissibleVariationDisc d j F → ∀ i : TensorFirstCoefficientIndex q, ∀ k : Fin 4,
      (∀ θ, ‖tensorCurrentCoefficient d.G B i k (F.f (circlePoint θ))‖ ≤ M) ∧
      boundaryDSq (fun θ (_ : Unit) => tensorCurrentCoefficient d.G B i k (F.f (circlePoint θ))) ≤
        ENNReal.ofReal C * variationEnergy d j F := by
  obtain ⟨C, M, hC, hM, hb⟩ := finiteCoefficients_uniform_boundary_control hd j
    (b := fun ik : TensorFirstCoefficientIndex q × Fin 4 => tensorCurrentCoefficient d.G B ik.1 ik.2)
    (fun ik x => tensorCurrentCoefficient_chart_contDiffOn hd.2.2.2.2.1 hB ik.1 ik.2 x)
  exact ⟨C, M, hC, hM, fun F hF i k => hb F hF (i, k)⟩

end Yau.Blueprint.V03Proof
