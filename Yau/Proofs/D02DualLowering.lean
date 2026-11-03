import Yau.Proofs.D02WirtingerVectors
import Yau.Proofs.D02DifferentialNorm

/-! The raised covector is computed using the actual inverse transpose.
Its lowering identity and regularity are proved from the same metric. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n N : ℕ} {M : ComplexManifold n}

def raisedCovector (H : Matrix (Fin n) (Fin n) ℂ) (η : Fin n → ℂ) : Fin n → ℂ :=
  H⁻¹ᵀ *ᵥ η

theorem raisedCovector_lowering {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef)
    (η : Fin n → ℂ) : Hᵀ *ᵥ raisedCovector H η = η := by
  unfold raisedCovector
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul H (hH.isUnit.map Matrix.detMonoidHom),
    Matrix.transpose_one, Matrix.one_mulVec]

theorem dualNormMat_eq_raisedPairing (H : Matrix (Fin n) (Fin n) ℂ) (η : Fin n → ℂ) :
    dualNormMat H (WithLp.toLp 2 η) = (star η ⬝ᵥ raisedCovector H η).re := rfl

def raisedImmersionComponent (g : HermitianField M) (F : M.Carrier → ComplexVector N)
    (x : M.Carrier) (a : Fin N) (z : ComplexVector n) : Fin n → ℂ :=
  raisedCovector (hMat g x z) (fun b => immersionDerivativeMatrix F x z a b)

theorem raisedImmersionComponent_lowering (g : HermitianField M)
    (F : M.Carrier → ComplexVector N) (x : M.Carrier) (a : Fin N)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    (hMat g x z)ᵀ *ᵥ raisedImmersionComponent g F x a z =
      (fun b => immersionDerivativeMatrix F x z a b) :=
  raisedCovector_lowering (hMat_posDef g x z hz) _

theorem raisedImmersionComponent_contDiffOn (g : HermitianField M) (hg : MetricSmooth g)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (x : M.Carrier)
    (a : Fin N) (b : Fin n) :
    ContDiffOn ℝ ∞ (fun z => raisedImmersionComponent g F x a z b) (chartTarget x) := by
  have hJ (c : Fin n) : ContDiffOn ℝ ∞
      (fun z => immersionDerivativeMatrix F x z a c) (chartTarget x) :=
    (complex_holomorphic_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x)
      (immersionDerivativeMatrix_differentiableOn hF x a c)).restrict_scalars ℝ
  have hI (c : Fin n) : ContDiffOn ℝ ∞ (fun z => (hMat g x z)⁻¹ c b) (chartTarget x) :=
    entrywise_matrix_inv_contDiffOn
      (Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth g hg x)
      (fun z hz => ne_of_gt (hMat_posDef g x z hz).det_pos) c b
  change ContDiffOn ℝ ∞ (fun z => ∑ c, (hMat g x z)⁻¹ c b *
    immersionDerivativeMatrix F x z a c) (chartTarget x)
  exact ContDiffOn.sum fun c _ => (hI c).mul (hJ c)

theorem immersionDifferentialNormSq_eq_raisedPairing (g : HermitianField M)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    immersionDifferentialNormSq g F (chartInv x z) =
      ∑ a, (star (fun b => immersionDerivativeMatrix F x z a b) ⬝ᵥ
        raisedImmersionComponent g F x a z).re := by
  rw [immersionDifferentialNormSq_in_fixed_chart g hF x hz]
  rfl

end Yau.NodeProofs.D02Aux
