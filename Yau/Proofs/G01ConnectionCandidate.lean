import Yau.Proofs.G01ComplexMetricDerivative
import Yau.Proofs.G01Koszul

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
set_option backward.isDefEq.respectTransparency false
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The complex Chern matrix in an actual real coordinate direction. -/
def chernRealA (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (a : RIdx n) : Matrix (Fin n) (Fin n) ℂ :=
  if a.2 = 0 then chernA h x z a.1 else Complex.I • chernA h x z a.1

def connectionCandidate (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (a : RIdx n) : Matrix (RIdx n) (RIdx n) ℝ :=
  rawReal (chernRealA h x z a)

/-- The locally defined Chern matrices satisfy the actual complex metric derivative identity. -/
theorem matrixRealDerivative_eq_chernRealA (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    matrixRealDerivative (hMat h x) z a =
      (chernRealA h x z a)ᴴ * hMat h x z + hMat h x z * chernRealA h x z a := by
  have hH : (hMat h x z)ᴴ = hMat h x z := L12Aux.hMat_isHermitian h x z
  rcases a with ⟨k, a⟩
  fin_cases a
  · change matrixRealDerivative (hMat h x) z (k, 0) =
      (chernA h x z k)ᴴ * hMat h x z + hMat h x z * chernA h x z k
    rw [matrixRealDerivative_zero (hMat h x) z k,
      matrixWirtBar_hMat, ← chernA_lower h x z hz k]
    simp only [Matrix.conjTranspose_mul, hH]
    exact add_comm _ _
  · change matrixRealDerivative (hMat h x) z (k, 1) =
      (Complex.I • chernA h x z k)ᴴ * hMat h x z +
        hMat h x z * (Complex.I • chernA h x z k)
    rw [matrixRealDerivative_one (hMat h x) z k,
      matrixWirtBar_hMat, ← chernA_lower h x z hz k]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hH,
      Complex.star_def, Complex.conj_I, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    module

/-- Raw realification transports this derivative identity to the genuine G = 2 Re h. -/
theorem connectionCandidate_compatible (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    L12Aux.matrixDirectionalDerivative (fun w => realMetricFn h x w) z (realVec a) =
      (connectionCandidate h x z a)ᵀ * realMetricFn h x z +
        realMetricFn h x z * connectionCandidate h x z a := by
  rw [realMetricFn_derivative_eq h hs x z hz,
    matrixRealDerivative_eq_chernRealA h x z hz, realMetricFn_eq_rawReal]
  simp only [connectionCandidate, rawReal_add, rawReal_mul, rawReal_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, smul_add]

/-- Kähler symmetry makes the real coefficient candidate torsion free. -/
theorem connectionCandidate_symm (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (a b d : RIdx n) :
    connectionCandidate h x z a d b = connectionCandidate h x z b d a := by
  have ht := chernA_torsion_symm h hs hk x z hz a.1 b.1 d.1
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rcases d with ⟨p, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases d <;>
    simp [connectionCandidate, chernRealA, rawReal, Matrix.smul_apply,
      smul_eq_mul, Complex.mul_re, Complex.mul_im, ht]

/-- The computed Levi-Civita connection is the real representation of the computed Chern connection. -/
theorem connectionMatrix_eq_chernRealA (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) (a : RIdx n) :
    L12Aux.connectionMatrix h x z a = rawReal (chernRealA h x z a) :=
  connectionMatrix_eq_of_compatible h hs x z hz (connectionCandidate h x z)
    (connectionCandidate_symm h hs hk x z hz)
    (connectionCandidate_compatible h hs x z hz) a

end Yau.NodeProofs.G01Aux
