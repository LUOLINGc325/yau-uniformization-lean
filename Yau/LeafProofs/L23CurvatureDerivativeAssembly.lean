import Yau.LeafProofs.L23JetBernsteinInduction
import spec.CHAIN.ParabolicCandidates

/-! Exact frozen-target assembly from the remaining genuine distance support construction. -/

noncomputable section
open scoped Topology
namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem curvatureJetNorm_core_bound_of_cutoffSupports
    (h : ℝ → HermitianField M) (p : M.Carrier) (a K r τ σ : ℝ)
    (hK : 0<K) (hr : 0<r) (hτ : 0<τ) (hσ : 0<σ)
    (hO : IsOpen (distBall (h a) p (2*r)))
    (hcO : IsCompact (closure (distBall (h a) p (2*r))))
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x∈distBall (h a) p (2*r), ∀ t∈Set.Icc a (a+2*τ), curvatureJetNorm (h t) 0 x≤K)
    (hSupports : DerivativeCutoffSupports h p a K r τ σ) (k : ℕ)
    (q : M.Carrier) (hq : q∈distBall (h a) p r) (T : ℝ) (hT : T∈Set.Icc (a+τ) (a+2*τ)) :
    curvatureJetNorm (h T) k q≤Real.sqrt (localJetBound n K r τ σ k) :=
  Real.sqrt_le_sqrt (jetSq_core_closed_bound_of_cutoffSupports h p a K r τ σ
    hK hr hτ hσ hO hcO hflow hcurv hSupports k q hq T hT)

theorem localCurvatureDerivatives_of_supportConstruction
    (hSupports : ∀ (n : ℕ) (M : ComplexManifold n) (h : ℝ → HermitianField M)
      (p : M.Carrier) (a K r τ σ : ℝ),
      0<K → 0<r → 0<τ → 0<σ →
      IsOpen (distBall (h a) p (2*r)) → IsCompact (closure (distBall (h a) p (2*r))) →
      LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ →
      (∀ x∈distBall (h a) p (2*r), ∀ t∈Set.Icc a (a+2*τ), curvatureJetNorm (h t) 0 x≤K) →
      DerivativeCutoffSupports h p a K r τ σ) :
    ParabolicCandidates.LocalCurvatureDerivatives := by
  intro n hn k K r τ σ hK hr hτ hσ
  refine ⟨Real.sqrt (localJetBound n K r τ σ k),
    Real.sqrt_pos.mpr (localJetBound_pos n K r τ σ hK hr hτ hσ k),?_⟩
  intro M h p a
  dsimp only
  intro hO hcO hflow hcurv q hq T hT
  exact curvatureJetNorm_core_bound_of_cutoffSupports h p a K r τ σ hK hr hτ hσ
    hO hcO hflow hcurv (hSupports n M h p a K r τ σ hK hr hτ hσ hO hcO hflow hcurv) k q hq T hT

end Yau.LeafProofs.L23Aux
