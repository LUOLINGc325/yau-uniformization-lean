import Yau.Proofs.D05CotangentSymplectic
import Yau.Proofs.D05GeneratorsAlgebra
import Yau.Proofs.V03AmbientSmooth

/-! A single globally defined ambient bivector for the original immersion.
Its fixed-chart identity proves holomorphicity of its actual columns. -/

open scoped Manifold Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau V03Proof

variable {n q : ℕ} {M : ComplexManifold n}

def ambientBivector (G : CotangentPoint M → ComplexVector q) (y : CotangentPoint M) :
    Matrix (Fin q) (Fin q) ℂ :=
  cotangentDG G y.1 y * (canonicalBivector : CotangentMatrix n) * (cotangentDG G y.1 y)ᵀ

def ambientBivectorColumn (G : CotangentPoint M → ComplexVector q) (a : Fin q)
    (y : CotangentPoint M) : ComplexVector q :=
  WithLp.toLp 2 (fun b => ambientBivector G y b a)

theorem ambientBivector_in_fixed_chart {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) (x : M.Carrier) (y : CotangentPoint M)
    (hy : y ∈ cotangentSource x) :
    ambientBivector G y = cotangentDG G x y * (canonicalBivector : CotangentMatrix n) * (cotangentDG G x y)ᵀ := by
  unfold ambientBivector
  rw [cotangentDG_transition hG y.1 x y (mem_extChartAt_source _) hy,
    Matrix.transpose_mul]
  calc
    _ = cotangentDG G x y *
        (cotangentTransition y.1 x y * (canonicalBivector : CotangentMatrix n) * (cotangentTransition y.1 x y)ᵀ) *
          (cotangentDG G x y)ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [cotangentTransition_symplectic y.1 x y (mem_extChartAt_source _) hy]

theorem cotangentDG_chart_entry_contDiffOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) (x : M.Carrier) (a : Fin q) (b : CotangentIndex n) :
    ContDiffOn ℂ ∞ (fun z => cotangentDG G x (cotangentChartInv x z) a b)
      (cotangentTarget x) := by
  have hD : ContDiffOn ℂ ∞ (fun z =>
      (fderiv ℂ (fun w => G (cotangentChartInv x w)) z (cotangentDir b)) a)
      (cotangentTarget x) := by
    intro z hz
    have hc := (cotangentHolomorphic_chart_contDiffOn hG x).contDiffAt
      (((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ).mem_nhds hz)
    exact ((contDiffAt_piLp_apply (p := 2) (i := a)).comp z
      ((hc.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)).contDiffWithinAt
  exact hD.congr fun z hz => by
    dsimp only [cotangentDG]
    rw [cotangentChart_right_inv x hz]

theorem ambientBivector_chart_contDiffOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) (x : M.Carrier) (a b : Fin q) :
    ContDiffOn ℂ ∞ (fun z => ambientBivector G (cotangentChartInv x z) a b)
      (cotangentTarget x) := by
  have hA := cotangentDG_chart_entry_contDiffOn hG x
  have hAJ (i : Fin q) (j : CotangentIndex n) : ContDiffOn ℂ ∞
      (fun z => (cotangentDG G x (cotangentChartInv x z) * (canonicalBivector : CotangentMatrix n)) i j)
      (cotangentTarget x) := by
    simp only [Matrix.mul_apply]
    exact ContDiffOn.sum fun k _ => (hA i k).mul contDiffOn_const
  have hlocal : ContDiffOn ℂ ∞ (fun z =>
      (cotangentDG G x (cotangentChartInv x z) * (canonicalBivector : CotangentMatrix n) *
        (cotangentDG G x (cotangentChartInv x z))ᵀ) a b) (cotangentTarget x) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact ContDiffOn.sum fun j _ =>
      (ContDiffOn.sum fun k _ => (hA a k).mul contDiffOn_const).mul (hA b j)
  exact hlocal.congr fun z hz => congrFun (congrFun
    (ambientBivector_in_fixed_chart hG x (cotangentChartInv x z)
      (cotangentChartInv_mapsTo x hz)) a) b

theorem ambientBivectorColumn_holomorphic {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) (a : Fin q) :
    CotangentHolomorphic (ambientBivectorColumn G a) := by
  intro x
  have hv : ContDiffOn ℂ ∞ (fun z => ambientBivectorColumn G a (cotangentChartInv x z))
      (cotangentTarget x) := by
    apply (contDiffOn_piLp 2).mpr
    intro b
    exact ambientBivector_chart_contDiffOn hG x b a
  exact hv.differentiableOn (by simp)

theorem ambientBivector_columns_span {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (y : CotangentPoint M) :
    Submodule.span ℂ (Set.range fun a => ambientBivectorColumn G a y) =
      LinearMap.range (Matrix.toEuclideanLin (cotangentDG G y.1 y)) := by
  exact (span_matrix_columns_eq_range (ambientBivector G y)).trans
    (range_canonical_pushforward _ (cotangentDG_mulVec_injective hG y))

end Yau.Blueprint.D05Proof
