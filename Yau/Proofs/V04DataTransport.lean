import Yau.Blueprint.VariationContracts
import Yau.Proofs.V03Charts

/-! Fibre dilation is performed in the actual cotangent atlas. In particular,
compactness is transported through valid charts rather than a product topology. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {M : ComplexManifold n} {X : KahlerManifold n}

def fiberScale (c : ℂ) (y : CotangentPoint M) : CotangentPoint M :=
  (y.1, c • y.2)

theorem fiberScale_chartInv (c : ℂ) (x : M.Carrier) (z : CotangentCoord n) :
    fiberScale c (cotangentChartInv x z) =
      cotangentChartInv x (z.1, c • z.2) := by
  apply Prod.ext
  · rfl
  · ext v
    simp [fiberScale, cotangentChartInv, covectorOfCoords, Finset.mul_sum, mul_assoc]

theorem cotangentCompact_fiberScale {K : Set (CotangentPoint M)}
    (hK : CotangentCompact K) (c : ℂ) : CotangentCompact (fiberScale c '' K) := by
  obtain ⟨r, x, C, hC, hK⟩ := hK
  let S : CotangentCoord n → CotangentCoord n := fun z => (z.1, c • z.2)
  have hS : Continuous S := continuous_fst.prodMk (continuous_snd.const_smul c)
  refine ⟨r, x, fun i => S '' C i, fun i => ⟨(hC i).1.image hS, ?_⟩, ?_⟩
  · rintro z ⟨w, hw, rfl⟩
    exact ⟨((hC i).2 hw).1, Set.mem_univ _⟩
  · rw [hK, Set.image_iUnion]
    congr 1
    funext i
    rw [Set.image_image, Set.image_image]
    congr 1
    funext z
    exact fiberScale_chartInv c (x i) z

theorem dualNorm_fiber_smul (g : HermitianField M) (x : M.Carrier)
    (c : ℂ) (ξ : Covector n) :
    dualNorm g x (c • ξ) = ‖c‖ ^ 2 * dualNorm g x ξ := by
  have hc : covectorCoords x x (c • ξ) = c • covectorCoords x x ξ := by
    ext i
    rfl
  change dualNormMat (gMat g x) (covectorCoords x x (c • ξ)) = _
  rw [hc]
  have hlp : WithLp.ofLp (c • covectorCoords x x ξ) =
      c • WithLp.ofLp (covectorCoords x x ξ) := rfl
  unfold dualNormMat
  rw [hlp, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

theorem dualNorm_fiberScale_real (g : HermitianField M) (c : ℝ)
    (y : CotangentPoint M) :
    dualNorm g (fiberScale (c : ℂ) y).1 (fiberScale (c : ℂ) y).2 =
      c ^ 2 * dualNorm g y.1 y.2 := by
  rw [fiberScale, dualNorm_fiber_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The exact old and new compact boxes are related by one fibre dilation. -/
theorem boundaryCompact_eq_fiberScale (d : VariationData X q) (B : ℕ → ℝ)
    (j : ℕ) (hd : 0 < d.B j) (hB : 0 < B j) :
    boundaryCompact {d with B := B} j =
      fiberScale ((B j / d.B j : ℝ) : ℂ) '' boundaryCompact d j := by
  ext y
  constructor
  · intro hy
    let z := fiberScale ((d.B j / B j : ℝ) : ℂ) y
    have hnorm := dualNorm_fiberScale_real (d.h 0) (d.B j / B j) y
    have hz : z ∈ boundaryCompact d j := by
      refine ⟨hy.1, ?_⟩
      dsimp [z]
      rw [hnorm]
      have hmul := mul_le_mul_of_nonneg_left hy.2 (sq_nonneg (d.B j / B j))
      have heq : (d.B j / B j) ^ 2 * B j ^ 2 = d.B j ^ 2 := by
        field_simp
      exact hmul.trans_eq heq
    refine ⟨z, hz, ?_⟩
    apply Prod.ext
    · rfl
    · change (((B j / d.B j : ℝ) : ℂ) •
        (((d.B j / B j : ℝ) : ℂ) • y.2)) = y.2
      rw [smul_smul, ← Complex.ofReal_mul]
      have heq : B j / d.B j * (d.B j / B j) = 1 := by field_simp
      rw [heq, Complex.ofReal_one, one_smul]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨hz.1, ?_⟩
    change dualNorm (d.h 0) (fiberScale _ z).1 (fiberScale _ z).2 ≤ B j ^ 2
    rw [dualNorm_fiberScale_real]
    have hm := mul_le_mul_of_nonneg_left hz.2 (sq_nonneg (B j / d.B j))
    have heq : (B j / d.B j) ^ 2 * d.B j ^ 2 = B j ^ 2 := by field_simp
    exact hm.trans_eq heq

/-- Enlargement preserves the original setup, including intrinsic compactness. -/
theorem variationSetup_enlarge_B {d : VariationData X q} (hd : VariationSetup d)
    (B : ℕ → ℝ) (hB : ∀ j, d.B j ≤ B j) : VariationSetup {d with B := B} := by
  rcases hd with ⟨hT, hTe, hflow, hu, hG, hspan, hp, hc, hQ, htail, htail0,
    hA, hA0, hb⟩
  refine ⟨hT, hTe, hflow, hu, hG, hspan, hp, hc, hQ, htail, htail0,
    hA, hA0, fun j => ?_⟩
  obtain ⟨hAj, hBj, hcompact, hcost⟩ := hb j
  have hold : 0 < d.B j := lt_of_lt_of_le (by positivity : (0 : ℝ) < j + 1) hBj
  refine ⟨hAj, hBj.trans (hB j), ?_, hcost⟩
  rw [boundaryCompact_eq_fiberScale d B j hold (hold.trans_le (hB j))]
  exact cotangentCompact_fiberScale hcompact _

/-- Only the radius at the index being tested occurs in a fibre wall error. -/
theorem fiberWallError_enlarge_B {d : VariationData X q} {k : ClockData X}
    (h : FiberWallError d k) (B : ℕ → ℝ) : FiberWallError {d with B := B} k := by
  simpa only [FiberWallError, boundaryRegion, spatialBoundaryHessianAt,
    wallCost, baseCost, wallBase, deltaBase, wallFiber, deltaFiber,
    wallProduct, clockFiberCutoff, Function.update_self] using h

theorem baseWallError_enlarge_B {d : VariationData X q} {k : ClockData X}
    (h : BaseWallError d k) (B : ℕ → ℝ) : BaseWallError {d with B := B} k := h

end Yau.Blueprint.V04Proof
