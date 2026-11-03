import Yau.Proofs.F03LeviScalarCalculus
import Yau.Proofs.F03CovectorCrossBound
import Yau.Proofs.F03HermitianBounds

/-! Physical gradient bounds control the actual rank-one and mixed Levi matrices. -/
noncomputable section
open scoped ComplexOrder Matrix ContDiff
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smooth_gradNormSq_nonneg (g : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (x : M.Carrier) : 0 ≤ gradNormSq g f x := by
  have hh := scalarGradientPair_self_nonneg g f x
  rw [scalarGradientPair_eq_twice_gradNormSq g hf] at hh
  linarith

theorem scalarFirstCovector_bound (g : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (x : M.Carrier) {a : ℝ}
    (hBound : Real.sqrt (gradNormSq g f x) ≤ a) :
    HermLE (Matrix.vecMulVec (star (scalarFirstCovector f x)) (scalarFirstCovector f x))
      (Complex.ofReal (a^2) • gMat g x) := by
  apply covector_rankOne_bound_of_dual_bound _
    (hMat_posDef g x (chartPt x x) (mem_extChartAt_target x))
  change dualNormMat (gMat g x) (WithLp.toLp 2 (scalarFirstCovector f x)) ≤ a^2
  rw [scalarFirstCovector_dualNorm g hf x]
  calc
    _ = (Real.sqrt (gradNormSq g f x))^2 := (Real.sq_sqrt (smooth_gradNormSq_nonneg g hf x)).symm
    _ ≤ a^2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hBound 2

theorem hermAbsLE_of_nonneg_upper {A G : Herm n} {C : ℝ} (hA : A.PosSemidef)
    (hG : G.PosSemidef) (hC : 0 ≤ C) (hUpper : HermLE A (Complex.ofReal C • G)) :
    HermAbsLE A G C := by
  refine ⟨?_,hUpper⟩
  unfold HermLE
  convert hA.add (hG.smul (Complex.zero_le_real.mpr hC)) using 1
  simp only [Complex.ofReal_neg,neg_smul,sub_neg_eq_add]

theorem scalarFirstCovector_abs_bound (g : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (x : M.Carrier) {a : ℝ}
    (hBound : Real.sqrt (gradNormSq g f x) ≤ a) :
    HermAbsLE (Matrix.vecMulVec (star (scalarFirstCovector f x)) (scalarFirstCovector f x))
      (gMat g x) (a^2) :=
  hermAbsLE_of_nonneg_upper (Matrix.posSemidef_vecMulVec_star_self _)
    (hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)).posSemidef (sq_nonneg a)
    (scalarFirstCovector_bound g hf x hBound)

theorem covector_cross_abs_bound_of_rankOne_bounds
    (G : Herm n) (c d : Fin n → ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : HermLE (Matrix.vecMulVec (star c) c) (Complex.ofReal (a^2) • G))
    (hd : HermLE (Matrix.vecMulVec (star d) d) (Complex.ofReal (b^2) • G)) :
    HermAbsLE (Matrix.vecMulVec (star c) d+Matrix.vecMulVec (star d) c) G (2*a*b) := by
  have hNegC : HermLE (Matrix.vecMulVec (star (-c)) (-c)) (Complex.ofReal (a^2) • G) := by
    convert hc using 1
    ext i j
    simp only [Matrix.vecMulVec_apply,Pi.star_apply,Pi.neg_apply,star_neg,neg_mul,mul_neg,neg_neg]
  have hNeg := covector_cross_bound_of_rankOne_bounds G (-c) d ha hb hNegC hd
  refine ⟨?_,covector_cross_bound_of_rankOne_bounds G c d ha hb hc hd⟩
  convert hermLE_neg hNeg using 1 <;>
    ext i j <;> simp only [Matrix.add_apply,Matrix.neg_apply,Matrix.smul_apply,
      Matrix.vecMulVec_apply,Pi.star_apply,Pi.neg_apply,star_neg,Complex.ofReal_neg,
      smul_eq_mul] <;> ring

theorem scalarFirstCovector_cross_abs_bound (g : HermitianField M)
    {f q : M.Carrier → ℝ} (hf : SmoothFn f) (hq : SmoothFn q) (x : M.Carrier)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hF : Real.sqrt (gradNormSq g f x) ≤ a) (hQ : Real.sqrt (gradNormSq g q x) ≤ b) :
    HermAbsLE (Matrix.vecMulVec (star (scalarFirstCovector f x)) (scalarFirstCovector q x)+
      Matrix.vecMulVec (star (scalarFirstCovector q x)) (scalarFirstCovector f x)) (gMat g x) (2*a*b) :=
  covector_cross_abs_bound_of_rankOne_bounds (gMat g x) _ _ ha hb
    (scalarFirstCovector_bound g hf x hF) (scalarFirstCovector_bound g hq x hQ)

theorem levi_scalar_comp_abs_bound (g : HermitianField M)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (x : M.Carrier) {C a : ℝ} (hU : HermAbsLE (levi u x) (gMat g x) C)
    (hGrad : Real.sqrt (gradNormSq g u x) ≤ a) :
    HermAbsLE (levi (fun y => F (u y)) x) (gMat g x)
      (|deriv F (u x)| *C+|deriv (deriv F) (u x)| *a^2) := by
  rw [levi_real_scalar_comp hu F hF x]
  exact hermAbsLE_add (hermAbsLE_real_smul hU (deriv F (u x)))
    (hermAbsLE_real_smul (scalarFirstCovector_abs_bound g hu x hGrad) (deriv (deriv F) (u x)))

end Yau.Proofs.F03Aux
