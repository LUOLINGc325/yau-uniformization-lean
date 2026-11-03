import Yau.Proofs.V03ClearedAmbientLogCovector

/-! The actual first differential of every smooth intrinsic real scalar
descends through the immersion Gram inverse to a smooth ambient covector. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

def fixedAmbientScalarCovector (G : CotangentPoint M → ComplexVector q)
    (b : CotangentPoint M → ℝ) (x : M.Carrier) (z : CotangentCoord n) : Fin q → ℂ :=
  ambientCovector (cotangentDG G x (cotangentChartInv x z))
    (fun i => wirt (fun w => (b (cotangentChartInv x w) : ℂ)) z (cotangentDir i))

def ambientScalarCovector (G : CotangentPoint M → ComplexVector q)
    (b : CotangentPoint M → ℝ) (y : CotangentPoint M) : Fin q → ℂ :=
  fixedAmbientScalarCovector G b y.1 (cotangentChart y.1 y)

theorem fixedAmbientScalarCovector_entry_contDiffOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {b : CotangentPoint M → ℝ}
    (hb : ∀ x, ContDiffOn ℝ ∞ (fun z => b (cotangentChartInv x z)) (cotangentTarget x))
    (x : M.Carrier) (a : Fin q) :
    ContDiffOn ℝ ∞ (fun z => fixedAmbientScalarCovector G b x z a) (cotangentTarget x) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hJ := gramLeftInverse_entry_contDiffOn
    (fun k i => (cotangentDG_chart_entry_contDiffOn hG.1 x k i).restrict_scalars ℝ)
    (fun z hz => ne_of_gt (cotangentDG_gram_posDef_in_chart hG x _
      (cotangentChartInv_mapsTo x hz)).det_pos)
  change ContDiffOn ℝ ∞ (fun z => ∑ i,
    wirt (fun w => (b (cotangentChartInv x w) : ℂ)) z (cotangentDir i) *
      gramLeftInverse (cotangentDG G x (cotangentChartInv x z)) i a) (cotangentTarget x)
  exact ContDiffOn.sum (fun i _ =>
    (wirt_contDiffOn hopen (Complex.ofRealCLM.contDiff.comp_contDiffOn (hb x)) (cotangentDir i)).mul
      (hJ i a))

theorem fixedAmbientScalarCovector_eq_ambient {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) {b : CotangentPoint M → ℝ} (x : M.Carrier)
    {y : CotangentPoint M} (hy : y ∈ cotangentSource x)
    (hb : DifferentiableAt ℝ (fun z => b (cotangentChartInv x z)) (cotangentChart x y)) :
    fixedAmbientScalarCovector G b x (cotangentChart x y) = ambientScalarCovector G b y := by
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hW := scalarWirt_in_fixed_chart b x hy hb
  have hT : IsUnit (cotangentTransition y.1 x y) :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (cotangentTransition_mulVec_injective y.1 x y hself hy)
  unfold ambientScalarCovector fixedAmbientScalarCovector
  rw [cotangentChart_left_inv x hy, cotangentChart_left_inv y.1 hself, hW,
    cotangentDG_transition hG y.1 x y hself hy]
  exact (ambientCovector_covariant (cotangentDG G x y)
    (fun i => wirt (fun z => (b (cotangentChartInv x z) : ℂ)) (cotangentChart x y)
      (cotangentDir i)) (cotangentTransition y.1 x y) hT).symm

theorem ambientScalarCovector_chart_entry_contDiffOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {b : CotangentPoint M → ℝ}
    (hb : ∀ x, ContDiffOn ℝ ∞ (fun z => b (cotangentChartInv x z)) (cotangentTarget x))
    (x : M.Carrier) (a : Fin q) :
    ContDiffOn ℝ ∞ (fun z => ambientScalarCovector G b (cotangentChartInv x z) a)
      (cotangentTarget x) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  apply (fixedAmbientScalarCovector_entry_contDiffOn hG hb x a).congr
  intro z hz
  have hbd : DifferentiableAt ℝ (fun w => b (cotangentChartInv x w))
      (cotangentChart x (cotangentChartInv x z)) := by
    rw [cotangentChart_right_inv x hz]
    exact ((hb x).contDiffAt (hopen.mem_nhds hz)).differentiableAt (by simp)
  have hh := congrFun (fixedAmbientScalarCovector_eq_ambient hG.1 x (cotangentChartInv_mapsTo x hz)
    hbd) a
  rw [cotangentChart_right_inv x hz] at hh
  exact hh.symm

end Yau.Blueprint.V03Proof
