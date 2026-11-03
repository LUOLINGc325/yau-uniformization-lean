import Yau.LeafProofs.L23LocalDistanceSupportMinimizingGeodesic

noncomputable section
open scoped Topology Manifold
namespace Yau.LeafProofs.L23Aux
open L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_buffered_minimizing_geodesic
    (h : ℝ → HermitianField M) (p q y : M.Carrier)
    (a K r τ σ rIn rOut t : ℝ)
    (hK : 0 < K) (hr : 0 < r) (hτ : 0 < τ) (hσ : 0 < σ)
    (hO : IsOpen (distBall (h a) p (2*r)))
    (hcO : IsCompact (closure (distBall (h a) p (2*r))))
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x ∈ distBall (h a) p (2*r), ∀ s ∈ Set.Icc a (a+2*τ),
      curvatureJetNorm (h s) 0 x ≤ K)
    (hIn : 0 < rIn) (hInOut : rIn < rOut) (hOut : rOut ≤ 2*r)
    (hq : q ∈ distBall (h a) p rIn) (ht : t ∈ Set.Icc a (a+2*τ))
    (hy : inducedDistance (h t) q y < Real.exp (-σ*(2*n : ℕ)*K*τ)*(rOut-rIn)/4) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ → M.Carrier,
      γ 0 = q ∧ γ 1 = y ∧ FieldGeodesicOn (h t) γ (Set.Ioo (-δ) (1+δ)) ∧
      Set.MapsTo γ (Set.Icc (0 : ℝ) 1) (distBall (h a) p (2*r)) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        actualSpeedSq (h t) γ u = inducedDistance (h t) q y ^ 2 := by
  exact exists_buffered_minimizing_geodesic_of_gap (compactMinimizingGeodesic n)
    h p q y a K r τ σ rIn rOut t hK hr hτ hσ hO hcO hflow hcurv hIn hInOut hOut hq ht hy

end Yau.LeafProofs.L23Aux
