import Yau.Proofs.C02InitialLinearEquiv
import Yau.Proofs.C02NormalMap
import Yau.Proofs.C02ParallelSmooth

/-! The radial frame is an actual physical linear isometry, constructed by
transporting the unitary initial frame along the actual complete geodesic. -/

noncomputable section
open scoped Manifold InnerProductSpace
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalInitialPhysicalFrame (h : HermitianField M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (h p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup h y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace h y
    OrthonormalBasis (Fin (Module.finrank ℝ (ComplexVector n))) ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) p) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  exact (stdOrthonormalBasis ℝ (ComplexVector n)).map (normalInitialIsometryEquiv h p U hU)

def normalTransportedFrame (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    OrthonormalBasis (Fin (Module.finrank ℝ (ComplexVector n))) ℝ
      (TangentSpace 𝓘(ℝ, ComplexVector n) (normalRealMap g p U x)) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact realParallelFrame g ⟨p, normalInitialLinearMap p U x⟩
    (normalInitialPhysicalFrame g.form p U hU) 1

def normalParallelIsometry (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    ComplexVector n ≃ₗᵢ[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (normalRealMap g p U x) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  exact (stdOrthonormalBasis ℝ (ComplexVector n)).repr.trans
    (normalTransportedFrame g p U hU x).repr.symm

theorem normalParallelIsometry_basis (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n)
    (i : Fin (Module.finrank ℝ (ComplexVector n))) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    normalParallelIsometry g p U hU x (stdOrthonormalBasis ℝ (ComplexVector n) i) =
      realParallelField g ⟨p, normalInitialLinearMap p U x⟩
        (normalInitialLinearMap p U (stdOrthonormalBasis ℝ (ComplexVector n) i)) 1 := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  change (normalTransportedFrame g p U hU x).repr.symm
    ((stdOrthonormalBasis ℝ (ComplexVector n)).repr (stdOrthonormalBasis ℝ (ComplexVector n) i)) = _
  rw [OrthonormalBasis.repr_self, OrthonormalBasis.repr_symm_single]
  exact realParallelFrame_apply g ⟨p, normalInitialLinearMap p U x⟩
    (normalInitialPhysicalFrame g.form p U hU) 1 i

end Yau.Blueprint.C02Proof
