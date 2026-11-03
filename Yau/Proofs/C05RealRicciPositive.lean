import Yau.Proofs.C05RicciDualEnergy
import Yau.Proofs.G01RawPairing

/-! Positivity of the actual real Ricci form follows from the original
positive Hermitian Ricci form, with the physical factor two. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C05Aux
open Yau Yau.NodeProofs.G01Aux Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem rawReal_quadratic_coords (A : Matrix (Fin n) (Fin n) ℂ) (W : ComplexVector n) :
    realCoord W ⬝ᵥ (rawReal A *ᵥ realCoord W) =
      (star (WithLp.ofLp W) ⬝ᵥ (A *ᵥ WithLp.ofLp W)).re := by
  calc
    _ = ∑ d, ∑ c, rawReal A d c * realCoord W c * realCoord W d := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = (complexMatrixPairing A W W).re := rawReal_pairing A W W
    _ = _ := by
      congr 1
      simp only [complexMatrixPairing, dotProduct, Matrix.mulVec, Finset.mul_sum,
        Pi.star_apply]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro c _
      ring

theorem rawReal_posDef (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    (rawReal A).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change (rawReal A)ᵀ = rawReal A
    exact rawReal_isSymm A hA.isHermitian
  · intro r hr
    let W : ComplexVector n := ∑ a, r a • realVec a
    have hcoords : realCoord W = r := funext (realCoord_sum_realVec r)
    have hW : WithLp.ofLp W ≠ 0 := by
      intro hzero
      have hWzero : W = 0 := by
        ext i
        exact congrFun hzero i
      apply hr
      rw [← hcoords, hWzero]
      funext a
      simp [realCoord]
    have hquad := rawReal_quadratic_coords A W
    rw [hcoords] at hquad
    simp only [star_trivial]
    rw [hquad]
    exact (Complex.pos_iff.mp (hA.dotProduct_mulVec_pos hW)).1

theorem realRicciMatrix_posDef (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (x : M.Carrier) (hA : (ricci k x).PosDef) :
    (Matrix.of (realRicciCoeff k x (chartPt x x))).PosDef := by
  have heq : Matrix.of (realRicciCoeff k x (chartPt x x)) =
      (2 : ℝ) • rawReal (ricci k x) := by
    ext a b
    exact Yau.NodeProofs.G04Aux.realRicciCoeff_center_raw k hk hK x a b
  rw [heq]
  exact (rawReal_posDef _ hA).smul (by norm_num : (0 : ℝ) < 2)

end Yau.Proofs.C05Aux
