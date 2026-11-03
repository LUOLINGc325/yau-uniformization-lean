import Yau.Proofs.V03Transitions

/-! Holomorphic smoothness of induced cotangent coordinate changes, obtained
from the dual base derivative rather than a product trivialization. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem cotangentChartTransition_contDiffAt (x x' : M.Carrier) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x)
    (hy' : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source) :
    ContDiffAt ℂ ∞ (fun w => cotangentChart x' (cotangentChartInv x w)) z := by
  let A : CotangentCoord n → ComplexVector n := fun w => chartPt x' (chartInv x w.1)
  let B : ComplexVector n → ComplexVector n := fun w => chartPt x (chartInv x' w)
  let K : CotangentCoord n → CotangentCoord n := fun w =>
    (A w, WithLp.toLp 2 (fun i =>
      ∑ k, (fderiv ℂ B (A w) (stdVec i)) k * w.2 k))
  have hy : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x).source :=
    (extChartAt (ComplexModel n) x).map_target hz.1
  have hA : ContDiffAt ℂ ∞ A z :=
    (chartTransition_contDiffAt x x' hz.1 hy').comp z contDiffAt_fst
  have hround : chartInv x' (A z) = chartInv x z.1 :=
    (extChartAt (ComplexModel n) x').left_inv hy'
  have hB : ContDiffAt ℂ ∞ B (A z) := by
    apply chartTransition_contDiffAt x' x
      ((extChartAt (ComplexModel n) x').map_source hy')
    change chartInv x' (A z) ∈ (extChartAt (ComplexModel n) x).source
    rw [hround]
    exact hy
  have hD : ContDiffAt ℂ ∞ (fun w => fderiv ℂ B (A w)) z :=
    (hB.fderiv_right (m := ∞) (by simp)).comp z hA
  have hK : ContDiffAt ℂ ∞ K z := by
    refine hA.prodMk ?_
    apply (contDiffAt_piLp 2).mpr
    intro i
    change ContDiffAt ℂ ∞ (fun w : CotangentCoord n =>
      ∑ k, (fderiv ℂ B (A w) (stdVec i)) k * w.2 k) z
    apply ContDiffAt.sum
    intro k _
    exact ((contDiffAt_piLp_apply (p := 2) (i := k)).comp z
      (hD.clm_apply contDiffAt_const)).mul
      ((contDiffAt_piLp_apply (p := 2) (i := k)).comp z contDiffAt_snd)
  have hInvSmooth : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞
      (chartInv x) z.1 :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) x).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz.1)
  have hInv : ContinuousAt (fun w : CotangentCoord n => chartInv x w.1) z :=
    hInvSmooth.continuousAt.comp continuousAt_fst
  have htarget : ∀ᶠ w in 𝓝 z, w ∈ cotangentTarget x :=
    ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ).mem_nhds hz
  have hsource : ∀ᶠ w in 𝓝 z,
      chartInv x w.1 ∈ (extChartAt (ComplexModel n) x').source :=
    hInv.eventually ((isOpen_extChartAt_source (I := ComplexModel n) x').mem_nhds hy')
  apply hK.congr_of_eventuallyEq
  filter_upwards [htarget, hsource] with w hw hw'
  apply Prod.ext
  · rfl
  ext i
  have hDw : fderiv ℂ B (A w) =
      tangentCoordChange (ComplexModel n) x' x (chartInv x w.1) := by
    have hroundw : chartInv x' (A w) = chartInv x w.1 :=
      (extChartAt (ComplexModel n) x').left_inv hw'
    calc
      _ = tangentCoordChange (ComplexModel n) x' x (chartInv x' (A w)) :=
        chartTransition_fderiv_eq_coordChange x' x
          ((extChartAt (ComplexModel n) x').map_source hw')
      _ = _ := by rw [hroundw]
  change (cotangentChart x' (cotangentChartInv x w)).2 i =
    ∑ k, (fderiv ℂ B (A w) (stdVec i)) k * w.2 k
  rw [cotangentChart_transition_fiber x x' hw hw', hDw]

end Yau.Blueprint.V03Proof
