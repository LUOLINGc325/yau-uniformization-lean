import Yau.Proofs.G01ChernFlat
import Yau.Proofs.G01ConnectionCandidate
import Yau.Proofs.G01RealDirection

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
set_option backward.isDefEq.respectTransparency false
open Yau Yau.LeafProofs
variable {n r : ℕ}

theorem matrixRealDerivative_smul (A : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (c : ℂ) (a : RIdx n) :
    matrixRealDerivative (fun w => c • A w) z a = c • matrixRealDerivative A z a := by
  ext i j
  simp only [matrixRealDerivative, Matrix.smul_apply, smul_eq_mul]
  rw [fderiv_const_mul (hA i j) c]
  simp

variable {M : ComplexManifold n}

def complexCurvatureRealDirections (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (a b : RIdx n) : Matrix (Fin n) (Fin n) ℂ :=
  matrixRealDerivative (fun w => chernRealA h x w b) z a -
    matrixRealDerivative (fun w => chernRealA h x w a) z b +
    chernRealA h x z a * chernRealA h x z b - chernRealA h x z b * chernRealA h x z a

/-- The computed Chern curvature in real coordinate directions has only mixed type. -/
theorem complexCurvatureRealDirections_eq (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    complexCurvatureRealDirections h x z a b =
      (realDirectionFactor a * star (realDirectionFactor b)) • chernF h x z a.1 b.1 -
        (realDirectionFactor b * star (realDirectionFactor a)) • chernF h x z b.1 a.1 := by
  have hA (k i j : Fin n) : DifferentiableAt ℝ (fun w => chernA h x w k i j) z :=
    ((chernA_contDiffOn h hs x k i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  rcases a with ⟨k, a⟩
  rcases b with ⟨l, b⟩
  have hp := chernA_holomorphic_flat h hs x z hz k l
  fin_cases a <;> fin_cases b <;>
    simp [complexCurvatureRealDirections, chernRealA, realDirectionFactor,
      matrixRealDerivative_smul _ z (hA _) Complex.I,
      matrixRealDerivative_zero, matrixRealDerivative_one, smul_smul, chernF]
  all_goals
    ext i j
    have hc := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) hp
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.zero_apply, Matrix.smul_apply,
      smul_eq_mul] at hc ⊢
  · linear_combination hc
  · linear_combination Complex.I * hc
  · linear_combination Complex.I * hc
  · linear_combination -hc

end Yau.NodeProofs.G01Aux
