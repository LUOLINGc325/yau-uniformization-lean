import Yau.Proofs.V01SpanningAlgebra
import Yau.Proofs.D05CotangentSymplectic
import Yau.Proofs.V03DifferentialTransport

/-! V01 scratch source: global Hamiltonian fields from the same immersion.
Their actual fixed-chart representatives are holomorphic derivatives of G. -/

noncomputable section
open Set Matrix
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Blueprint.V01Proof

variable {n q : ℕ} {M : ComplexManifold n}

def hamiltonianColumns (G : CotangentPoint M → ComplexVector q)
    (i : Fin q) (y : CotangentPoint M) : CotangentIndex n → ℂ :=
  fun a => ((canonicalBivector : CotangentMatrix n) * (cotangentDG G y.1 y)ᵀ) a i

theorem hamiltonianColumns_fixed_chart
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (x : M.Carrier) (y : CotangentPoint M) (hy : y ∈ cotangentSource x)
    (i : Fin q) (a : CotangentIndex n) :
    (cotangentTransition y.1 x y *ᵥ hamiltonianColumns G i y) a =
      ((canonicalBivector : CotangentMatrix n) * (cotangentDG G x y)ᵀ) a i := by
  let T := cotangentTransition y.1 x y
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source y.1
  have hDG := Yau.Blueprint.V03Proof.cotangentDG_transition hG.1 y.1 x y hself hy
  have hT := Yau.Blueprint.D05Proof.cotangentTransition_symplectic y.1 x y hself hy
  have hmatrix : T * ((canonicalBivector : CotangentMatrix n) *
      (cotangentDG G y.1 y)ᵀ) =
      (canonicalBivector : CotangentMatrix n) * (cotangentDG G x y)ᵀ := by
    calc
      _ = T * ((canonicalBivector : CotangentMatrix n) *
          (cotangentDG G x y * T)ᵀ) := by rw [hDG]
      _ = (T * (canonicalBivector : CotangentMatrix n) * Tᵀ) *
          (cotangentDG G x y)ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hT]
  have hentry := congrArg
    (fun B : Matrix (CotangentIndex n) (Fin q) ℂ => B a i) hmatrix
  simpa only [T, hamiltonianColumns, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hentry

theorem hamiltonianColumns_fixed_chart_holomorphic
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (x : M.Carrier) (i : Fin q) (a : CotangentIndex n) :
    DifferentiableOn ℂ (fun z =>
      (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        hamiltonianColumns G i (cotangentChartInv x z)) a) (cotangentTarget x) := by
  have hopen : IsOpen (cotangentTarget x) := (isOpen_extChartAt_target x).prod isOpen_univ
  have hsum : DifferentiableOn ℂ (fun z : CotangentCoord n =>
      ∑ b, (canonicalBivector : CotangentMatrix n) a b *
        (fderiv ℂ (fun w => G (cotangentChartInv x w)) z (cotangentDir b)) i)
        (cotangentTarget x) := by
    apply DifferentiableOn.fun_sum
    intro b _
    have hd := Yau.Blueprint.V03Proof.complex_holomorphic_fderiv_apply_differentiableOn
      hopen (hG.1 x) (cotangentDir b)
    convert (differentiableOn_const ((canonicalBivector : CotangentMatrix n) a b)).mul
      ((EuclideanSpace.proj i).differentiable.comp_differentiableOn hd) using 1
    funext z
    rfl
  apply hsum.congr
  intro z hz
  calc
    _ = ((canonicalBivector : CotangentMatrix n) *
        (cotangentDG G x (cotangentChartInv x z))ᵀ) a i :=
      hamiltonianColumns_fixed_chart hG x (cotangentChartInv x z)
        (Yau.Blueprint.V03Proof.cotangentChartInv_mapsTo x hz) i a
    _ = _ := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, cotangentDG]
      rw [Yau.Blueprint.V03Proof.cotangentChart_right_inv x hz]

theorem cotangentSpanningFields_of_immersion
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G) :
    CotangentSpanningFields M := by
  refine ⟨q, hamiltonianColumns G, ?_, ?_⟩
  · intro i x a
    exact hamiltonianColumns_fixed_chart_holomorphic hG x i a
  · intro y
    exact canonical_columns_span_of_injective (cotangentDG G y.1 y)
      (Yau.Blueprint.V03Proof.cotangentDG_mulVec_injective hG y)

end Yau.Blueprint.V01Proof
