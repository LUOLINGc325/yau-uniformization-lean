import spec.CHAIN.CONTRACTS

/-! The coordinate frame sums are the actual derivative of the inverse chart,
in arbitrary complex dimension, including the empty finite index set. -/

noncomputable section
open scoped Manifold
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

theorem complexVector_basis_sum (u : ComplexVector n) :
    (∑ i, u i • stdVec i) = u := by
  ext j
  simp [stdVec, Pi.single_apply]

theorem chartVectorInFrame_eq_chartVec (a x : M.Carrier) (u : ComplexVector n) :
    chartVectorInFrame a x u = chartVec a x u := by
  let d : ComplexVector n →ₗ[ℂ] TangentVector M x :=
    ((mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) a).symm
      (chartPt a x)).comp
      (tangentSpaceCastModel (ComplexModel n) (chartPt a x)).symm.toContinuousLinearMap).toLinearMap
  change (∑ i, u i • d (stdVec i)) = d u
  calc
    (∑ i, u i • d (stdVec i)) = ∑ i, d (u i • stdVec i) :=
      Finset.sum_congr rfl (fun i _ => (d.map_smul (u i) (stdVec i)).symm)
    _ = d (∑ i, u i • stdVec i) := (map_sum d _ _).symm
    _ = d u := congrArg d (complexVector_basis_sum u)

end Yau.Blueprint.C02Proof
