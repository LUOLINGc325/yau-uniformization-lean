import Yau.Proofs.D02FieldHolomorphic
import Yau.Proofs.D02FiberLimitLinear

open scoped Manifold Topology ContDiff Matrix
open Set

noncomputable section
namespace Yau.NodeProofs.D02FiberLimitAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.NodeProofs.D02Aux
set_option backward.isDefEq.respectTransparency false

variable {n m : ℕ} {M : ComplexManifold n}

/-- The original spanning tuple separates actual covectors in each fibre. -/
theorem field_evaluation_injective (V : Fin m → VectorField M)
    (hspan : ∀ x, Submodule.span ℂ (Set.range fun i ↦ V i x) = ⊤)
    (x : M.Carrier) {ξ η : Covector n}
    (h : ∀ i, fieldEvaluation (V i) (x, ξ) = fieldEvaluation (V i) (x, η)) : ξ = η := by
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨i, hi⟩ := exists_fieldEvaluation_ne_zero hspan hne
  apply hi
  change ξ (V i x) - η (V i x) = 0
  exact sub_eq_zero.mpr (h i)

/-- Constant linear combinations of the SAME finite fields form a square
coordinate matrix. No global cotangent trivialization is introduced. -/
def frameMatrix (V : Fin m → VectorField M) (C : Fin n → Fin m → ℂ)
    (x : M.Carrier) (z : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ ∑ a, C i a * fieldCoords (V a) x z j

/-- At each center the coefficients can be fixed so the actual matrix is the
identity. This is the empty identity matrix when n=0. -/
theorem exists_frame_coefficients (V : Fin m → VectorField M)
    (hspan : ∀ x, Submodule.span ℂ (Set.range fun i ↦ V i x) = ⊤) (x : M.Carrier) :
    ∃ C : Fin n → Fin m → ℂ, frameMatrix V C x (chartPt x x) = 1 := by
  classical
  obtain ⟨C, hC⟩ := exists_spanning_coefficients (fun a ↦ V a x) (hspan x)
    (fun i : Fin n ↦ chartVec x x (stdVec i))
  refine ⟨C, ?_⟩
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have he (a : Fin m) : fieldCoords (V a) x (chartPt x x) = tangentCoords x x (V a x) := by
    change tangentCoords x (chartInv x (chartPt x x)) (V a (chartInv x (chartPt x x))) = _
    rw [hx]
  ext i j
  change (∑ a, C i a * fieldCoords (V a) x (chartPt x x) j) = _
  simp_rw [he]
  have hh := congrArg (fun w ↦ tangentCoords x x w) (hC i)
  rw [tangentCoords_chartVec x x (mem_extChartAt_source x)] at hh
  have hhj := congrArg (EuclideanSpace.proj j) hh
  simp only [tangentCoords, map_sum, map_smul, smul_eq_mul] at hhj
  have hhj' : (∑ a, C i a * tangentCoords x x (V a x) j) = stdVec i j := hhj
  rw [hhj']
  simp [stdVec, EuclideanSpace.single, PiLp.single_apply, Matrix.one_apply, eq_comm]

/-- The actual intrinsic evaluation equals the unconjugated coordinate pairing. -/
theorem field_evaluation_coordinates (V : VectorField M) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (ξ : Covector n) :
    fieldEvaluation V (y, ξ) = ∑ j, fieldCoords V x (chartPt x y) j * covectorCoords x y ξ j := by
  have hp : cotangentChart x (y, ξ) ∈ cotangentTarget x := cotangentChart_mapsTo x hy
  have hh := fieldEvaluation_chart V x hp
  rw [cotangentChart_left_inv x hy] at hh
  exact hh

/-- The square reconstruction uses linear combinations of the original
scalar evaluations, with transpose convention already included in the rows. -/
theorem frameMatrix_evaluation (V : Fin m → VectorField M) (C : Fin n → Fin m → ℂ)
    (x y : M.Carrier) (hy : y ∈ (extChartAt (ComplexModel n) x).source) (ξ : Covector n) :
    (frameMatrix V C x (chartPt x y)).mulVec (covectorCoords x y ξ) =
      fun i ↦ ∑ a, C i a * fieldEvaluation (V a) (y, ξ) := by
  classical
  ext i
  simp only [Matrix.mulVec, dotProduct, frameMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [field_evaluation_coordinates (V a) x y hy ξ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- All matrix entries are continuous on the original valid chart target. -/
theorem frameMatrix_continuousOn (V : Fin m → VectorField M)
    (hV : ∀ a, IsHolomorphicField (V a)) (C : Fin n → Fin m → ℂ) (x : M.Carrier) :
    ContinuousOn (frameMatrix V C x) (chartTarget x) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact continuousOn_finsetSum Finset.univ fun a _ ↦ continuousOn_const.mul
    (((EuclideanSpace.proj j).continuous.comp_continuousOn (fieldCoords_continuousOn (hV a) x)))

end Yau.NodeProofs.D02FiberLimitAux
