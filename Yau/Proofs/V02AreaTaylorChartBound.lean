import Yau.Proofs.V02AreaTaylorImmersion
import Yau.Proofs.V03ImmersionChartBound

/-! One uniform genuine chart differential estimate on each compact
coordinate piece, derived from the original cotangent immersion. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {M : ComplexManifold n}

theorem immersion_chart_fderiv_injective
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (x : M.Carrier) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x) :
    Function.Injective (fderiv ℂ (fun w => G (cotangentChartInv x w)) z) := by
  have hzc := cotangentChart_right_inv x hz
  have hcoords : Function.Injective (cotangentCoordsVector : CotangentCoord n → CotangentIndex n → ℂ) :=
    (show Function.LeftInverse cotangentVectorOfCoords cotangentCoordsVector from
      cotangentVectorOfCoords_coordsVector).injective
  intro u v huv
  apply hcoords
  apply cotangentDG_mulVec_injective_in_chart hG x (cotangentChartInv x z)
    (cotangentChartInv_mapsTo x hz)
  ext b
  simpa only [cotangentDG_mulVec, cotangentVectorOfCoords_coordsVector, hzc] using
    congrArg (fun w : ComplexVector q => w b) huv

theorem compact_immersion_chart_differential_bound
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (x : M.Carrier) {K : Set (CotangentCoord n)} (hK : IsCompact K)
    (hKtarget : K ⊆ cotangentTarget x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ v : CotangentCoord n,
      ‖v‖ ≤ C * ‖fderiv ℂ (fun w => G (cotangentChartInv x w)) z v‖ := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hD := (cotangentHolomorphic_chart_contDiffOn hG.1 x).fderiv_of_isOpen hopen
    (m := ∞) (by simp)
  have hDR : ContDiffOn ℝ ∞ (fun z =>
      (fderiv ℂ (fun w => G (cotangentChartInv x w)) z).restrictScalars ℝ) (cotangentTarget x) := by
    apply contDiffOn_clm_apply.mpr
    intro v
    exact (hD.clm_apply (contDiffOn_const (c := v))).restrict_scalars ℝ
  exact compact_injective_linear_family_bound hK (hDR.continuousOn.mono hKtarget)
    (fun z hz => immersion_chart_fderiv_injective hG x (hKtarget hz))

end Yau.Blueprint.V02AreaTaylorProof
