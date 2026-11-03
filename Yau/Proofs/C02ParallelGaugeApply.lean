import Yau.Proofs.C02ParallelGaugeFrame

/-! The radial isometry agrees on every vector with actual Levi--Civita
parallel transport. Pairing with the transported basis identifies the vector;
no linearity of a chosen ODE solution is assumed. -/

noncomputable section
open scoped Manifold InnerProductSpace
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalParallelIsometry_apply (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x z : ComplexVector n) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    normalParallelIsometry g p U hU x z =
      realParallelField g ⟨p, normalInitialLinearMap p U x⟩ (normalInitialLinearMap p U z) 1 := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let b := normalTransportedFrame g p U hU x
  let e := stdOrthonormalBasis ℝ (ComplexVector n)
  let P := normalParallelIsometry g p U hU x
  let w : TangentSpace 𝓘(ℝ, ComplexVector n) (normalRealMap g p U x) :=
    realParallelField g ⟨p, normalInitialLinearMap p U x⟩ (normalInitialLinearMap p U z) 1
  change P z = w
  apply b.repr.injective
  ext i
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  have hbi : b i = P (e i) := by
    change (normalTransportedFrame g p U hU x) i =
      (normalTransportedFrame g p U hU x).repr.symm (e.repr (e i))
    rw [OrthonormalBasis.repr_self, OrthonormalBasis.repr_symm_single]
  let wi : TangentSpace 𝓘(ℝ, ComplexVector n) (normalRealMap g p U x) :=
    realParallelField g ⟨p, normalInitialLinearMap p U x⟩ (normalInitialLinearMap p U (e i)) 1
  have he : P (e i) = wi := normalParallelIsometry_basis g p U hU x i
  have hp : ⟪wi, w⟫_ℝ =
      ⟪normalInitialLinearMap p U (e i), normalInitialLinearMap p U z⟫_ℝ := by
    exact realParallelField_pairing g ⟨p, normalInitialLinearMap p U x⟩
      (normalInitialLinearMap p U (e i)) (normalInitialLinearMap p U z) 1
  calc
    ⟪b i, P z⟫_ℝ = ⟪P (e i), P z⟫_ℝ := congrArg (fun v => ⟪v, P z⟫_ℝ) hbi
    _ = ⟪e i, z⟫_ℝ := P.inner_map_map _ _
    _ = ⟪normalInitialLinearMap p U (e i), normalInitialLinearMap p U z⟫_ℝ :=
      ((normalInitialIsometryEquiv g.form p U hU).inner_map_map (e i) z).symm
    _ = ⟪wi, w⟫_ℝ := hp.symm
    _ = ⟪b i, w⟫_ℝ := congrArg (fun v => ⟪v, w⟫_ℝ) (hbi.trans he).symm

end Yau.Blueprint.C02Proof
