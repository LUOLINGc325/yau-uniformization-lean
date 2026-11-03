import Yau.Proofs.G01RicciNormalization
import Yau.Proofs.G01RawPairing

noncomputable section
open scoped Matrix Manifold
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}

def centralRicciQuadratic (h : HermitianField M) (x : M.Carrier) (v : TangentVector M x) : ℝ :=
  (complexMatrixPairing (ricci h x) (tangentCoords x x v) (tangentCoords x x v)).re

theorem centralRicciQuadratic_abs_le (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (v : TangentVector M x) :
    |centralRicciQuadratic h x v| ≤
      (2 * n : ℕ) * curvatureJetNorm h 0 x * hermitianNormSq (h x) v := by
  have hRic (a b : RIdx n) : realRicciCoeff h x (chartPt x x) a b =
      2 * rawReal (ricci h x) a b := by
    rw [L23Aux.realRicciCoeff_eq_realRicciMatrix h x (chartPt x x) (mem_extChartAt_target x),
      realRicciMatrix_eq_realification h hs hk x (chartPt x x) (mem_extChartAt_target x),
      hermitianRealification_eq]
    rfl
  have hQuad : (∑ a, ∑ b, realRicciCoeff h x (chartPt x x) a b *
      realCoord (tangentCoords x x v) a * realCoord (tangentCoords x x v) b) =
      2 * centralRicciQuadratic h x v := by
    simp_rw [hRic]
    rw [centralRicciQuadratic, ← rawReal_pairing]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hh := L23Aux.realRicciQuadratic_abs_le h x v
  rw [hQuad, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  nlinarith

end Yau.Blueprint.C02Proof
