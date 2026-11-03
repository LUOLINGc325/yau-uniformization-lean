import Yau.Proofs.V03DifferentialTransport

/-! The actual cotangent chart differential is invertible on an overlap.
Consequently the original immersion has full rank in every valid chart. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

theorem cotangentTransition_mulVec (x x' : M.Carrier) (y : CotangentPoint M)
    (v : CotangentIndex n → ℂ) :
    cotangentVectorOfCoords (cotangentTransition x x' y *ᵥ v) =
      fderiv ℂ (fun z => cotangentChart x' (cotangentChartInv x z))
        (cotangentChart x y) (cotangentVectorOfCoords v) := by
  classical
  conv_rhs => rw [cotangentVectorOfCoords_eq_sum]
  ext i <;>
    simp [cotangentVectorOfCoords, Matrix.mulVec, dotProduct, cotangentTransition,
      cotangentCoordsVector, map_sum, map_smul, Prod.fst_sum, Prod.snd_sum,
      WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, mul_comm]

theorem cotangentChartTransition_fderiv_injective (x x' : M.Carrier)
    {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    (hz' : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source) :
    Function.Injective (fderiv ℂ (fun w => cotangentChart x' (cotangentChartInv x w)) z) := by
  let T : CotangentCoord n → CotangentCoord n := fun w => cotangentChart x' (cotangentChartInv x w)
  let S : CotangentCoord n → CotangentCoord n := fun w => cotangentChart x (cotangentChartInv x' w)
  have hT := cotangentChartTransition_contDiffAt x x' hz hz'
  have hsource : cotangentChartInv x z ∈ cotangentSource x := cotangentChartInv_mapsTo x hz
  have hTz : T z ∈ cotangentTarget x' := cotangentChart_mapsTo x' hz'
  have hround : chartInv x' (T z).1 = chartInv x z.1 :=
    (extChartAt (ComplexModel n) x').left_inv hz'
  have hS : ContDiffAt ℂ ∞ S (T z) := cotangentChartTransition_contDiffAt x' x hTz
    (by rw [hround]; exact hsource)
  have heq : (fun w => S (T w)) =ᶠ[𝓝 z] id := by
    filter_upwards [(isOpen_cotangentChartOverlap x x').mem_nhds ⟨hz, hz'⟩] with w hw
    exact (congrArg (cotangentChart x) (cotangentChart_left_inv x' hw.2)).trans
      (cotangentChart_right_inv x hw.1)
  have hc := fderiv_comp z (hS.differentiableAt (by simp)) (hT.differentiableAt (by simp))
  have he := heq.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_id] at he
  have hderiv : (fderiv ℂ S (T z)).comp (fderiv ℂ T z) = ContinuousLinearMap.id ℂ _ := by
    exact hc.symm.trans he
  intro u v huv
  change fderiv ℂ T z u = fderiv ℂ T z v at huv
  have hh := congrArg (fderiv ℂ S (T z)) huv
  simpa only [← ContinuousLinearMap.comp_apply, hderiv, ContinuousLinearMap.id_apply] using hh

theorem cotangentTransition_mulVec_injective (x x' : M.Carrier) (y : CotangentPoint M)
    (hy : y ∈ cotangentSource x) (hy' : y ∈ cotangentSource x') :
    Function.Injective (cotangentTransition x x' y).mulVec := by
  have hbase : chartInv x (cotangentChart x y).1 = y.1 :=
    (extChartAt (ComplexModel n) x).left_inv hy
  have hD := cotangentChartTransition_fderiv_injective x x'
    (cotangentChart_mapsTo x hy) (by rw [hbase]; exact hy')
  intro u v huv
  apply cotangentVectorOfCoords_injective
  apply hD
  rw [← cotangentTransition_mulVec, ← cotangentTransition_mulVec, huv]

theorem cotangentDG_mulVec_injective_in_chart
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (x : M.Carrier) (y : CotangentPoint M) (hy : y ∈ cotangentSource x) :
    Function.Injective (cotangentDG G x y).mulVec := by
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hT := cotangentTransition_mulVec_injective x y.1 y hy hself
  have hJ := cotangentDG_mulVec_injective hG y
  rw [cotangentDG_transition hG.1 x y.1 y hy hself]
  intro u v huv
  apply hT
  apply hJ
  simpa only [Matrix.mulVec_mulVec] using huv

theorem cotangentDG_gram_posDef_in_chart
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (x : M.Carrier) (y : CotangentPoint M) (hy : y ∈ cotangentSource x) :
    ((cotangentDG G x y)ᴴ * cotangentDG G x y).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self _ (cotangentDG_mulVec_injective_in_chart hG x y hy)

theorem cotangentDG_gram_det_re_pos_in_chart
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (x : M.Carrier) (y : CotangentPoint M) (hy : y ∈ cotangentSource x) :
    0 < ((cotangentDG G x y)ᴴ * cotangentDG G x y).det.re :=
  (Complex.pos_iff.mp (cotangentDG_gram_posDef_in_chart hG x y hy).det_pos).1

end Yau.Blueprint.V03Proof
