import Yau.Proofs.F01LogDetTangent
import Yau.Proofs.F01FieldHeatPenalty
import Yau.Proofs.F01NativeLogDetEvolution

/-! The difference of two actual potential solutions is subcaloric
for the second actual flow metric, by the logarithmic determinant tangent
inequality and the original native potential identities. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem potential_difference_subcaloric
    (α : HermitianField M) (h k : ℝ → HermitianField M)
    (U V : M.Carrier → ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    (hU : SmoothSpaceTime U (Icc 0 T)) (hV : SmoothSpaceTime V (Icc 0 T))
    (hpotU : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpotV : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (k s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => V y s) x)
    (hpdeU : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (flowLogDetRatio α h x s) (Icc 0 T) s)
    (hpdeV : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (V x)
      (flowLogDetRatio α k x s) (Icc 0 T) s) :
    ∀ x t, t ∈ Icc 0 T →
      fieldHeatWithin k (Icc 0 T) (fun s y => U y s - V y s) x t ≤ 0 := by
  intro x t ht
  have hα := Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x)
  have hh := Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)
  have hk := Yau.LeafProofs.L12Aux.hMat_posDef (k t) x (chartPt x x) (mem_extChartAt_target x)
  have ha0 := (Complex.pos_iff.mp hα.det_pos).1
  have hh0 := (Complex.pos_iff.mp hh.det_pos).1
  have hk0 := (Complex.pos_iff.mp hk.det_pos).1
  have hlog : flowLogDetRatio α h x t - flowLogDetRatio α k x t =
      Real.log ((gMat (h t) x).det.re / (gMat (k t) x).det.re) := by
    change Real.log ((gMat (h t) x).det.re / (gMat α x).det.re) -
      Real.log ((gMat (k t) x).det.re / (gMat α x).det.re) = _
    erw [Real.log_div hh0.ne' ha0.ne', Real.log_div hk0.ne' ha0.ne',
      Real.log_div hh0.ne' hk0.ne']
    ring
  have hdiff : gMat (h t) x - gMat (k t) x = levi (fun y => U y t - V y t) x := by
    rw [hpotU t ht x, hpotV t ht x,
      levi_sub_native (smoothSpaceTime_slice hU ht) (smoothSpaceTime_slice hV ht)]
    abel
  have htime := ((hpdeU x t ht).sub (hpdeV x t ht)).derivWithin
    ((uniqueDiffOn_Icc hT) t ht)
  change derivWithin (fun s => U x s - V x s) (Icc 0 T) t =
    flowLogDetRatio α h x t - flowLogDetRatio α k x t at htime
  unfold fieldHeatWithin
  change derivWithin (fun s => U x s - V x s) (Icc 0 T) t -
    laplacian (k t) (fun y => U y t - V y t) x ≤ 0
  rw [htime, hlog]
  change Real.log ((gMat (h t) x).det.re / (gMat (k t) x).det.re) -
    traceWith (gMat (k t) x) (levi (fun y => U y t - V y t) x) ≤ 0
  rw [← hdiff]
  exact sub_nonpos.mpr (matrix_logdet_le_tangent_trace hk hh)

end Yau.NodeProofs.F01Aux
