import Yau.Proofs.G01RicciLocal
import Yau.Proofs.C01RicciPositive
import Yau.Proofs.C01RicciTraceBound
import Yau.Proofs.C01CompactQuadraticCoercivity

/-! The actual Levi-Civita Ricci trace agrees with twice the original
complex Ricci quadratic. The local identity requires only the genuine
field smoothness and Kähler equations, not a complete SmoothMetric. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem realRicciMatrix_quadratic_eq_complex
    (g : HermitianField M) (hg : MetricSmooth g) (hK : KahlerClosed g)
    (x : M.Carrier) (v : ComplexVector n) :
    (∑ i, ∑ j, realRicciMatrix g x (chartPt x x) i j * realCoord v i * realCoord v j) =
      2 * matrixQuadraticReal (ricci g x) v := by
  let r := realCoord v
  have hq : star r ⬝ᵥ (realRicciMatrix g x (chartPt x x) *ᵥ r) =
      ∑ i, ∑ j, realRicciMatrix g x (chartPt x x) i j * realCoord v i * realCoord v j := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum, r]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← hq, Yau.NodeProofs.G01Aux.realRicciMatrix_eq_realification g hg hK x
    (chartPt x x) (mem_extChartAt_target x), hermitianRealification_quadratic]
  rw [show complexCoordsOfReal r = WithLp.ofLp v from complexCoordsOfReal_realCoord v]
  rfl

variable {X : KahlerManifold n} {o : Pt X} {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_realRicciMatrix_quadratic_bounds
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (a : ℝ) (ha : 0 ≤ a) (x : Pt X) (v : ComplexVector n) :
    let R := ∑ i, ∑ j, realRicciMatrix (h a) x (chartPt x x) i j * realCoord v i * realCoord v j
    0 ≤ R ∧ R ≤ 2 * scalarCurvature (h a) x * matrixQuadraticReal (gMat (h a) x) v := by
  dsimp only
  rw [realRicciMatrix_quadratic_eq_complex (h a) (localizedFlow_metricSmooth_nonneg hflow a ha)
    (hflow.1.2.2.1 a ha) x v]
  have hA := (localizedFlow_ricci_posDef hflow hjoint a ha x).posSemidef
  have hqnonneg : 0 ≤ matrixQuadraticReal (ricci (h a) x) v :=
    (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg (WithLp.ofLp v))).1
  have hH := Yau.Blueprint.Alignment.Y03Proof.hMat_posDef (h a) x (chartPt x x) (mem_extChartAt_target x)
  have htrace := quadratic_le_traceWith_mul_metric (gMat (h a) x) (ricci (h a) x) hH hA (WithLp.ofLp v)
  change matrixQuadraticReal (ricci (h a) x) v ≤
    scalarCurvature (h a) x * matrixQuadraticReal (gMat (h a) x) v at htrace
  constructor
  · exact mul_nonneg (by norm_num) hqnonneg
  · nlinarith

end Yau.NodeProofs.C01Aux
