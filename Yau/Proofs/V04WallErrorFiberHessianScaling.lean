import Yau.Proofs.V04WallErrorFiberBaseSmooth

/-! Exact normalized Hessian identity for the radius update. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem leviMatrix_real_const_mul {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (c : ℝ) (dir : ι → E) :
    leviMatrix (fun w => c * f w) z dir = c • leviMatrix f z dir := by
  rw [leviMatrix_const_mul hf c dir]
  ext a b
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

theorem leviMatrix_four_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N S B F : E → ℝ} {z : E}
    (hN : ContDiffAt ℝ 2 N z) (hS : ContDiffAt ℝ 2 S z)
    (hB : ContDiffAt ℝ 2 B z) (hF : ContDiffAt ℝ 2 F z) (c a : ℝ) (dir : ι → E) :
    leviMatrix (fun w => c * N w + S w + a * B w + a * F w) z dir =
      c • leviMatrix N z dir + leviMatrix S z dir +
        a • leviMatrix B z dir + a • leviMatrix F z dir := by
  have hNc : ContDiffAt ℝ 2 (fun w => c * N w) z := hN.const_smul c
  have hBa : ContDiffAt ℝ 2 (fun w => a * B w) z := hB.const_smul a
  have hFa : ContDiffAt ℝ 2 (fun w => a * F w) z := hF.const_smul a
  rw [leviMatrix_add ((hNc.add hS).add hBa) hFa,
    leviMatrix_add (hNc.add hS) hBa,
    leviMatrix_add hNc hS,
    leviMatrix_real_const_mul hN, leviMatrix_real_const_mul hB, leviMatrix_real_const_mul hF]

theorem leviMatrix_three_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N S B : E → ℝ} {z : E}
    (hN : ContDiffAt ℝ 2 N z) (hS : ContDiffAt ℝ 2 S z)
    (hB : ContDiffAt ℝ 2 B z) (c a : ℝ) (dir : ι → E) :
    leviMatrix (fun w => c * N w + S w + a * B w) z dir =
      c • leviMatrix N z dir + leviMatrix S z dir + a • leviMatrix B z dir := by
  have hNc : ContDiffAt ℝ 2 (fun w => c * N w) z := hN.const_smul c
  have hBa : ContDiffAt ℝ 2 (fun w => a * B w) z := hB.const_smul a
  rw [leviMatrix_add (hNc.add hS) hBa,
    leviMatrix_add hNc hS,
    leviMatrix_real_const_mul hN, leviMatrix_real_const_mul hB]

theorem fiber_rescaled_hessian_difference {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) {b : ℝ} (hb : b ≠ 0) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x) {t : ℝ} (ht : t ∈ Set.Icc 0 d.T) (s : ℝ)
    (hδ : deltaBase d j (cotangentChartInv x z).1 ≠ 0)
    (hε : normalizedFiberProfile d x z ≠ 0) :
    symplecticP (leviMatrix (fun w => dualNorm (d.h t) (cotangentChartInv x w).1
        (cotangentChartInv x w).2 +
        wallCost {d with B := Function.update d.B j b} j (cotangentChartInv x w) t s)
      (fiberDilation b z) cotangentDir) -
      symplecticP (leviMatrix (fun w => dualNorm (d.h t) (cotangentChartInv x w).1
        (cotangentChartInv x w).2 + (baseCost d j (cotangentChartInv x w).1 t +
          (1 + s) * wallBase d j (cotangentChartInv x w).1)) (fiberDilation b z) cotangentDir) =
    symplecticCross (leviMatrix (fiberNormModel d x t) z cotangentDir)
      ((1 + s) • leviMatrix (normalizedFiberWall d x) z cotangentDir) +
      b⁻¹ ^ 2 * symplecticCross
        (leviMatrix (fiberBaseModel d j x t) z cotangentDir +
          (1 + s) • leviMatrix (fiberBaseWallModel d j x) z cotangentDir)
        ((1 + s) • leviMatrix (normalizedFiberWall d x) z cotangentDir) +
      b⁻¹ ^ 2 * symplecticP ((1 + s) • leviMatrix (normalizedFiberWall d x) z cotangentDir) := by
  have hzB : fiberDilation b z ∈ cotangentTarget x := ⟨hz.1, Set.mem_univ _⟩
  have hδB : deltaBase d j (cotangentChartInv x (fiberDilation b z)).1 ≠ 0 := hδ
  have hεB : deltaFiber {d with B := Function.update d.B j b} j
      (cotangentChartInv x (fiberDilation b z)) ≠ 0 := by
    rwa [deltaFiber_update_dilation d j x hb z]
  have hG := symplecticP_leviMatrix_fiberDilation b
    (updated_boundary_cost_contDiffAt hd j x b hzB ht s hδB hεB)
  have hG₀ := symplecticP_leviMatrix_fiberDilation b
    (norm_base_cost_contDiffAt hd j x hzB ht s hδB)
  rw [boundaryCost_update_dilation d j x hb t s] at hG
  rw [normBaseCost_dilation d j x b t s] at hG₀
  have ht' : t ∈ Set.Icc 0 d.extendedT := ⟨ht.1, ht.2.trans hd.2.1.le⟩
  have hN := (fiberNormModel_contDiffAt hd x hz ht').of_le (by simp : (2 : ℕ∞) ≤ ∞)
  have hS := (fiberBaseModel_contDiffAt hd j x hz ht').of_le (by simp : (2 : ℕ∞) ≤ ∞)
  have hB := (fiberBaseWallModel_contDiffAt hd j x hz hδ).of_le (by simp : (2 : ℕ∞) ≤ ∞)
  have hF := (normalizedFiberWall_contDiffAt hd x hz hε).of_le (by simp : (2 : ℕ∞) ≤ ∞)
  rw [leviMatrix_four_sum hN hS hB hF (b ^ 2) (1 + s) cotangentDir] at hG
  rw [leviMatrix_three_sum hN hS hB (b ^ 2) (1 + s) cotangentDir] at hG₀
  have hdiff := congrArg₂ (fun u v : ℝ => b⁻¹ ^ 2 * (u - v)) hG hG₀
  rw [symplecticP_rescaled_difference _ _ _ _ hb] at hdiff
  have hbCancel : b⁻¹ ^ 2 * b ^ 2 = 1 := by field_simp
  rw [mul_sub, ← mul_assoc, ← mul_assoc, hbCancel, one_mul, one_mul] at hdiff
  exact hdiff.symm

end Yau.Blueprint.V04Proof.WallErrorAux
