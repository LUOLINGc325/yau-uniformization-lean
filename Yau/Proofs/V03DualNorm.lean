import Yau.Proofs.V03Charts

/-! Positivity of the metric and dual norm used in the raw disc envelope. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem hermitian_sum_left {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (s : Finset ι) (u : ι → V) (v : V) :
    h.toFun (∑ i ∈ s, u i) v = ∑ i ∈ s, h.toFun (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.map_smul_left (0 : ℂ) (0 : V) v
  | @insert a s ha ih => simp [Finset.sum_insert ha, h.map_add_left, ih]

theorem hermitian_sum_right {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (s : Finset ι) (u : V) (v : ι → V) :
    h.toFun u (∑ i ∈ s, v i) = ∑ i ∈ s, h.toFun u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.map_smul_right (0 : ℂ) u (0 : V)
  | @insert a s ha ih => simp [Finset.sum_insert ha, h.map_add_right, ih]

theorem hMat_isHermitian (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) : (hMat h x z).IsHermitian := by
  ext i j
  exact ((h (chartInv x z)).conjugate_symmetric _ _).symm

theorem hMat_quadratic (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (u : Fin n → ℂ) :
    star u ⬝ᵥ ((hMat h x z) *ᵥ u) =
      (h (chartInv x z)).toFun
        (∑ i, u i • chartVec x (chartInv x z) (stdVec i))
        (∑ i, u i • chartVec x (chartInv x z) (stdVec i)) := by
  rw [hermitian_sum_left]
  simp only [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
    HermitianInnerProduct.map_smul_right, dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.mul_sum, hMat]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hMat_posDef (h : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (hz : z ∈ chartTarget x) : (hMat h x z).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hMat_isHermitian h x z)
  intro u hu
  rw [hMat_quadratic]
  apply Complex.pos_iff.mpr
  refine ⟨hermitianNormSq_pos (h (chartInv x z)) ?_,
    ((h (chartInv x z)).self_adjoint _).symm⟩
  intro hzero
  have hsum : ∑ i, u i • stdVec i = (WithLp.toLp 2 u : ComplexVector n) := by
    ext i
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  have heq : ∑ i, u i • chartVec x (chartInv x z) (stdVec i) =
      chartVec x (chartInv x z) (WithLp.toLp 2 u) := by
    rw [← hsum, chartVec_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (chartVec_smul _ _ _ _).symm
  rw [heq] at hzero
  have hc := congrArg (tangentCoords x (chartInv x z)) hzero
  rw [tangentCoords_chartVec x (chartInv x z)
    ((extChartAt (ComplexModel n) x).map_target hz)] at hc
  have hc0 : (WithLp.toLp 2 u : ComplexVector n) = 0 := by
    exact hc.trans (map_zero (mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) x) (chartInv x z)))
  apply hu
  ext i
  exact congrArg (fun v : ComplexVector n => v i) hc0

theorem gMat_posDef (h : HermitianField M) (x : M.Carrier) : (gMat h x).PosDef :=
  hMat_posDef h x (chartPt x x)
    ((extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x))

theorem dualNormMat_nonneg {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef)
    (ξ : ComplexVector n) : 0 ≤ dualNormMat H ξ := by
  exact Complex.nonneg_iff.mp
    ((hH.inv.transpose).posSemidef.dotProduct_mulVec_nonneg (WithLp.ofLp ξ)) |>.1

theorem dualNorm_nonneg (h : HermitianField M) (x : M.Carrier) (ξ : Covector n) :
    0 ≤ dualNorm h x ξ :=
  dualNormMat_nonneg (gMat_posDef h x) (covectorCoords x x ξ)

end Yau.Blueprint.V03Proof
