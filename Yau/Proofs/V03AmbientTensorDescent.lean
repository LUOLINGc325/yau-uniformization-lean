import Yau.Proofs.V03BoundaryTensorTransport

/-! The actual polynomially cleared boundary tensor descends to a single
ambient tensor on cotangent points, including every cutoff zero. -/

open scoped Topology ContDiff Matrix Manifold ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem clearedWallHessian_zero_left {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℝ} {z : E}
    (hz : f z = 0) (dir : ι → E) {m : ℕ} (hm : 4 ≤ m) :
    clearedWallHessian f g m dir z = 0 := by
  simp only [clearedWallHessian, clearedReciprocalMatrix_zero hz dir hm, smul_zero,
    hz, Complex.ofReal_zero, zero_pow (by omega : m ≠ 0), zero_smul, add_zero]

theorem clearedWallHessian_zero_right {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℝ} {z : E}
    (hz : g z = 0) (dir : ι → E) {m : ℕ} (hm : 4 ≤ m) :
    clearedWallHessian f g m dir z = 0 := by
  simp only [clearedWallHessian, clearedReciprocalMatrix_zero hz dir hm, smul_zero,
    hz, Complex.ofReal_zero, zero_pow (by omega : m ≠ 0), zero_smul, zero_add]

variable {n q : ℕ} {X : KahlerManifold n}

theorem clearedBoundaryTensor_zero (d : VariationData X q) (j a : ℕ) (ha : 4 ≤ a)
    (x : Pt X) (z : CotangentCoord n) (t s : ℝ)
    (hz : deltaBase d j (cotangentChartInv x z).1 = 0 ∨
      deltaFiber d j (cotangentChartInv x z) = 0) :
    clearedBoundaryTensor d j a x ((z, t), s) = 0 := by
  have hW : clearedWallTensor d j a x z = 0 := by
    rcases hz with hb | hf
    · exact clearedWallHessian_zero_left
        (f := fun w => deltaBase d j (cotangentChartInv x w).1)
        (g := fun w => deltaFiber d j (cotangentChartInv x w)) hb cotangentDir
        (by omega : 4 ≤ 2 * a)
    · exact clearedWallHessian_zero_right
        (f := fun w => deltaBase d j (cotangentChartInv x w).1)
        (g := fun w => deltaFiber d j (cotangentChartInv x w)) hf cotangentDir
        (by omega : 4 ≤ 2 * a)
  have hp : wallPower d j a (cotangentChartInv x z) = 0 := by
    rcases hz with hb | hf
    · simp [wallPower, wallProduct, hb, zero_pow (by omega : a ≠ 0)]
    · simp [wallPower, wallProduct, hf, zero_pow (by omega : a ≠ 0)]
  simp [clearedBoundaryTensor, hW, hp]

def ambientBoundaryTensor (d : VariationData X q) (j a : ℕ)
    (y : CotangentPoint X.manifold) (t s : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  fixedAmbientBoundaryTensor d j a y.1 ((cotangentChart y.1 y, t), s)

theorem fixedAmbientBoundaryTensor_eq_ambient {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) (x : Pt X)
    {y : CotangentPoint X.manifold} (hy : y ∈ cotangentSource x)
    {t : ℝ} (ht : t ∈ Set.Icc 0 d.extendedT) (s : ℝ) :
    fixedAmbientBoundaryTensor d j a x ((cotangentChart x y, t), s) =
      ambientBoundaryTensor d j a y t s := by
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hround := cotangentChart_left_inv x hy
  have hround0 := cotangentChart_left_inv y.1 hself
  have hz := cotangentChart_mapsTo x hy
  have hz0 := cotangentChart_mapsTo y.1 hself
  by_cases hb : deltaBase d j y.1 = 0
  · have h1 := clearedBoundaryTensor_zero d j a ha x (cotangentChart x y) t s
      (Or.inl (by simpa only [hround] using hb))
    have h2 := clearedBoundaryTensor_zero d j a ha y.1 (cotangentChart y.1 y) t s
      (Or.inl (by simpa only [hround0] using hb))
    unfold ambientBoundaryTensor fixedAmbientBoundaryTensor
    dsimp only
    rw [h1, h2]
    simp only [ambientLeviTensor, Matrix.mul_zero, Matrix.zero_mul]
  by_cases hf : deltaFiber d j y = 0
  · have h1 := clearedBoundaryTensor_zero d j a ha x (cotangentChart x y) t s
      (Or.inr (by simpa only [hround] using hf))
    have h2 := clearedBoundaryTensor_zero d j a ha y.1 (cotangentChart y.1 y) t s
      (Or.inr (by simpa only [hround0] using hf))
    unfold ambientBoundaryTensor fixedAmbientBoundaryTensor
    dsimp only
    rw [h1, h2]
    simp only [ambientLeviTensor, Matrix.mul_zero, Matrix.zero_mul]
  let b : CotangentPoint X.manifold → ℝ := fun y =>
    dualNorm (d.h t) y.1 y.2 + wallCost d j y t s
  have hcost := boundaryCost_fixed_chart_contDiffAt hd j x hz ht s
    (by simpa only [hround] using hb) (by simpa only [hround] using hf)
  have hH := spatialHessian_in_fixed_chart b x hy hcost
  have h1 := clearedBoundaryTensor_eq hd j a ha x hz ht s
    (by simpa only [hround] using hb) (by simpa only [hround] using hf)
  have h2 := clearedBoundaryTensor_eq hd j a ha y.1 hz0 ht s
    (by simpa only [hround0] using hb) (by simpa only [hround0] using hf)
  rw [hround] at h1
  rw [hround0] at h2
  have hT : IsUnit (cotangentTransition y.1 x y) :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (cotangentTransition_mulVec_injective y.1 x y hself hy)
  unfold ambientBoundaryTensor fixedAmbientBoundaryTensor
  dsimp only
  rw [hround, hround0]
  rw [h1, h2]
  simp only [Complex.ofReal_pow]
  change _ = ambientLeviTensor (cotangentDG d.G y.1 y)
    (((wallPower d j a y) ^ 2 : ℂ) • spatialHessian b y)
  rw [hH, cotangentDG_transition hd.2.2.2.2.1.1 y.1 x y hself hy]
  have hcov := ambientLeviTensor_covariant (cotangentDG d.G x y)
    (((wallPower d j a y : ℂ) ^ 2) •
      leviMatrix (fun z => b (cotangentChartInv x z)) (cotangentChart x y) cotangentDir)
    (cotangentTransition y.1 x y) hT
  simpa only [Matrix.smul_mul, Matrix.mul_smul] using hcov.symm

end Yau.Blueprint.V03Proof
