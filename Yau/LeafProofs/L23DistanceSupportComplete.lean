import Yau.LeafProofs.L23DistanceSupportAssembly
import Yau.LeafProofs.L23DistanceSupportCutoffAssembly

/-! Every distance support parameter in the curvature induction is now constructed from the original flow. -/

noncomputable section
open scoped Topology
namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem derivativeCutoffSupports
    (h : ℝ → HermitianField M) (p : M.Carrier) (a K r τ σ : ℝ)
    (hK : 0<K) (hr : 0<r) (hτ : 0<τ) (hσ : 0<σ)
    (hO : IsOpen (distBall (h a) p (2*r)))
    (hcO : IsCompact (closure (distBall (h a) p (2*r))))
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x∈distBall (h a) p (2*r), ∀ t∈Set.Icc a (a+2*τ), curvatureJetNorm (h t) 0 x≤K) :
    DerivativeCutoffSupports h p a K r τ σ := by
  apply derivativeCutoffSupports_of_upperSupports h p a K r τ σ hK hr hτ hσ hflow
  intro rIn rOut hIn hInOut hOut q hq y t ht hy
  exact exists_timeDistanceSq_upperSupport h p q y a K r τ σ rIn rOut t hK hr hτ hσ
    hO hcO hflow hcurv hIn hInOut hOut hq ht hy

end Yau.LeafProofs.L23Aux
