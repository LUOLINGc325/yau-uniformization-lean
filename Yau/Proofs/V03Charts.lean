import Yau.Proofs.V03Coordinates

/-! Inverse identities in the induced cotangent atlas. All identities retain
the actual chart-source or chart-target hypotheses. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem tangentCoords_chartVec (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (v : ComplexVector n) :
    tangentCoords x y (chartVec x y v) = v := by
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
    (I := ComplexModel n) hy
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
  exact congrArg (fun L => L v) hcomp

theorem chartVec_tangentCoords (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (v : TangentVector M y) :
    chartVec x y (tangentCoords x y v) = v := by
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := ComplexModel n) hy
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
  exact congrArg (fun L => L v) hcomp

set_option backward.isDefEq.respectTransparency false in
theorem tangentCoords_eq_coordChange (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (v : TangentVector M y) :
    tangentCoords x y v = tangentCoordChange (ComplexModel n) y x y v := by
  have h := mfderiv_chartAt_eq_tangentCoordChange (I := ComplexModel n)
    (by simpa only [extChartAt_source] using hy)
  have he : (extChartAt (ComplexModel n) x : M.Carrier → ComplexVector n) =
      chartAt (ComplexVector n) x := rfl
  simpa only [tangentCoords, he] using! congrArg (fun L => L v) h

set_option backward.isDefEq.respectTransparency false in
theorem chartVec_eq_coordChange (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (v : ComplexVector n) :
    chartVec x y v = tangentCoordChange (ComplexModel n) x y y v := by
  have hinj : Function.Injective (tangentCoords x y) :=
    (show Function.LeftInverse (chartVec x y) (tangentCoords x y) from
      chartVec_tangentCoords x y hy).injective
  apply hinj
  rw [tangentCoords_chartVec x y hy, tangentCoords_eq_coordChange x y hy,
    tangentCoordChange_comp ⟨⟨hy, mem_extChartAt_source y⟩, hy⟩,
    tangentCoordChange_self hy]

theorem covectorCoords_ofCoords (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (η : ComplexVector n) :
    covectorCoords x y (covectorOfCoords x y η) = η := by
  classical
  ext i
  change ((∑ k, η k • (EuclideanSpace.proj k : ComplexVector n →L[ℂ] ℂ))
    (tangentCoordChange (ComplexModel n) y x y (chartVec x y (stdVec i)))) = η i
  rw [← tangentCoords_eq_coordChange x y hy, tangentCoords_chartVec x y hy]
  simp [stdVec, EuclideanSpace.single, Pi.single_apply]

theorem chartVec_sum {ι : Type*} (x y : M.Carrier) (s : Finset ι)
    (v : ι → ComplexVector n) :
    chartVec x y (∑ i ∈ s, v i) = ∑ i ∈ s, chartVec x y (v i) := by
  exact map_sum (mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) x).symm (chartPt x y)) v s

theorem chartVec_smul (x y : M.Carrier) (c : ℂ) (v : ComplexVector n) :
    chartVec x y (c • v) = c • chartVec x y v := by
  exact (mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) x).symm (chartPt x y)).map_smul c v

set_option backward.isDefEq.respectTransparency false in
theorem covector_apply_chartVec (x y : M.Carrier) (ξ : Covector n)
    (v : ComplexVector n) :
    ξ (chartVec x y v) = ∑ i, v i * (covectorCoords x y ξ) i := by
  classical
  have hv : v = ∑ i, v i • stdVec i := by
    ext j
    simp [stdVec, EuclideanSpace.single, Pi.single_apply]
  conv_lhs => rw [hv, chartVec_sum]
  simp [covectorCoords, chartVec_smul, map_sum, map_smul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem covectorOfCoords_coords (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (ξ : Covector n) :
    covectorOfCoords x y (covectorCoords x y ξ) = ξ := by
  classical
  ext v
  change (∑ i, (covectorCoords x y ξ) i •
    (EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ))
      (tangentCoordChange (ComplexModel n) y x y v) = ξ v
  rw [← tangentCoords_eq_coordChange x y hy]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [← chartVec_tangentCoords x y hy v, covector_apply_chartVec]
  simp only [tangentCoords_chartVec x y hy, mul_comm]
  rfl

theorem cotangentChart_left_inv (x : M.Carrier) {y : CotangentPoint M}
    (hy : y ∈ cotangentSource x) :
    cotangentChartInv x (cotangentChart x y) = y := by
  have hx : chartInv x (chartPt x y.1) = y.1 :=
    (extChartAt (ComplexModel n) x).left_inv hy
  simp only [cotangentChartInv, cotangentChart, hx,
    covectorOfCoords_coords x y.1 hy, Prod.mk.eta]

theorem cotangentChart_right_inv (x : M.Carrier) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x) :
    cotangentChart x (cotangentChartInv x z) = z := by
  have hx : chartPt x (chartInv x z.1) = z.1 :=
    (extChartAt (ComplexModel n) x).right_inv hz.1
  have hy := (extChartAt (ComplexModel n) x).map_target hz.1
  simp only [cotangentChartInv, cotangentChart, hx,
    covectorCoords_ofCoords x (chartInv x z.1) hy, Prod.mk.eta]

theorem cotangentChart_mapsTo (x : M.Carrier) :
    Set.MapsTo (cotangentChart x) (cotangentSource x) (cotangentTarget x) := by
  intro y hy
  exact ⟨(extChartAt (ComplexModel n) x).map_source hy, Set.mem_univ _⟩

theorem cotangentChartInv_mapsTo (x : M.Carrier) :
    Set.MapsTo (cotangentChartInv x) (cotangentTarget x) (cotangentSource x) := by
  intro z hz
  exact (extChartAt (ComplexModel n) x).map_target hz.1

end Yau.Blueprint.V03Proof
