import Yau.Proofs.F01ComparisonTime
import Yau.Proofs.F01LaplacianLinearity
import Yau.Proofs.F01HeatChartNaturality
import Yau.Proofs.F01TraceOrder

/-! The explicit paper comparison function has its actual native heat
operator. A genuine lower Levi order of the weight gives its positive trace. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem comparisonFunction_heat_identity
    (α : HermitianField M) (h : ℝ → HermitianField M)
    (U P : M.Carrier → ℝ → ℝ) (φ : M.Carrier → ℝ) (D : ℝ)
    {I : Set ℝ} {t pdot : ℝ} (x : M.Carrier) (hUnique : UniqueDiffWithinAt ℝ I t)
    (hPtime : HasDerivWithinAt (P x) pdot I t) (hUtime : HasDerivWithinAt (U x) (P x t) I t)
    (hUspace : SmoothFn (fun y => U y t)) (hPspace : SmoothFn (fun y => P y t)) (hφ : SmoothFn φ)
    (hpot : ∀ y, gMat (h t) y = gMat α y - (t : ℂ) • ricci α y + levi (fun z => U z t) y)
    (hPheat : fieldHeatWithin h I (fun s y => P y s) x t =
      -traceWith (gMat (h t) x) (ricci α x)) :
    fieldHeatWithin h I (fun s y => comparisonFunction D n U P φ y s) x t =
      traceWith (gMat (h t) x) (gMat α x - (D : ℂ) • ricci α x + (D : ℂ) • levi φ x) := by
  have hDP : SmoothFn (fun y => (D - t) * P y t) := fun a => contDiffOn_const.mul (hPspace a)
  have hsum : SmoothFn (fun y => (D - t) * P y t + U y t) := fun a => (hDP a).add (hUspace a)
  have hDφ : SmoothFn (fun y => D * φ y) := fun a => contDiffOn_const.mul (hφ a)
  have hsub : SmoothFn (fun y => (D - t) * P y t + U y t - D * φ y) := fun a => (hsum a).sub (hDφ a)
  have hconst : SmoothFn (fun _ : M.Carrier => (n : ℝ) * t) := fun _ => contDiffOn_const
  have hlap : laplacian (h t) (fun y => comparisonFunction D n U P φ y t) x =
      (D - t) * laplacian (h t) (fun y => P y t) x + laplacian (h t) (fun y => U y t) x -
        D * laplacian (h t) φ x := by
    unfold comparisonFunction
    rw [laplacian_add_native (h t) hsub hconst, laplacian_const_native,
      laplacian_sub_native (h t) hsum hDφ, laplacian_add_native (h t) hDP hUspace,
      laplacian_const_mul_native (h t) hPspace (D - t), laplacian_const_mul_native (h t) hφ D]
    ring
  have htQ := (comparisonFunction_hasDerivWithinAt (D := D) (n := n) (φ := φ) x hPtime hUtime).derivWithin hUnique
  change derivWithin (P x) I t - laplacian (h t) (fun y => P y t) x = _ at hPheat
  rw [hPtime.derivWithin hUnique] at hPheat
  have hpdot : pdot = laplacian (h t) (fun y => P y t) x -
      traceWith (gMat (h t) x) (ricci α x) := by linarith
  unfold fieldHeatWithin
  rw [htQ, hlap, potential_laplacian_identity α (h t) (fun y => U y t) t hpot x,
    hpdot, traceWith_add, traceWith_sub, traceWith_real_smul, traceWith_real_smul]
  unfold laplacian
  ring

theorem comparisonFunction_heat_lower
    (α : HermitianField M) (h : ℝ → HermitianField M)
    (U P : M.Carrier → ℝ → ℝ) (φ : M.Carrier → ℝ) (D : ℝ)
    {I : Set ℝ} {t pdot c : ℝ} (x : M.Carrier) (hUnique : UniqueDiffWithinAt ℝ I t)
    (hPtime : HasDerivWithinAt (P x) pdot I t) (hUtime : HasDerivWithinAt (U x) (P x t) I t)
    (hUspace : SmoothFn (fun y => U y t)) (hPspace : SmoothFn (fun y => P y t)) (hφ : SmoothFn φ)
    (hpot : ∀ y, gMat (h t) y = gMat α y - (t : ℂ) • ricci α y + levi (fun z => U z t) y)
    (hPheat : fieldHeatWithin h I (fun s y => P y s) x t =
      -traceWith (gMat (h t) x) (ricci α x))
    (hweight : (gMat α x - (D : ℂ) • ricci α x + (D : ℂ) • levi φ x - (c : ℂ) • gMat α x).PosSemidef) :
    c * traceWith (gMat (h t) x) (gMat α x) ≤
      fieldHeatWithin h I (fun s y => comparisonFunction D n U P φ y s) x t := by
  rw [comparisonFunction_heat_identity α h U P φ D x hUnique hPtime hUtime hUspace hPspace hφ hpot hPheat]
  exact traceWith_lower_scalar
    (Yau.LeafProofs.L12Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)) hweight

end Yau.NodeProofs.F01Aux
