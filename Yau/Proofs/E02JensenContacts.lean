import Yau.Proofs.E02InfCommonJets
import Yau.Proofs.E02InfProductSemiconcavity
import Yau.LeafProofs.L04

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux

/-- The native Jensen positive outer-measure contact set and native
Aleksandrov give one product minimum with every factor jet. -/
theorem jensen_simultaneous_compactInf_jets (n m : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin (4*n+1))))
    (v : EuclideanSpace ℝ (Fin (4*n+1)) → ℝ)
    (hK : IsCompact K) (hNE : K.Nonempty) (hv : LowerSemicontinuousOn v K)
    (hv0 : ∀ a ∈ K, 0 ≤ v a) (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    {κ : ℝ} (hκ : 0 < κ)
    (g : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)) → ℝ) (C : ℝ)
    (hg : ConvexOn ℝ univ (fun Q => g Q+C*(‖Q‖^2/2)))
    (O : Set (EuclideanSpace ℝ (Fin (2*n+1+2*n*m))))
    (xh : EuclideanSpace ℝ (Fin (2*n+1+2*n*m))) (r : ℝ)
    (hr : 0 < r) (hO : IsOpen O) (hxh : xh ∈ O) (hOC : IsCompact (closure O))
    (hBall : closure O ⊆ Metric.ball xh r)
    (hGap : ∀ Q ∈ closure O \ O,
      (∑ i, α i*compactInfConvolution K v κ (factorProjection n m i xh))-g xh <
      (∑ i, α i*compactInfConvolution K v κ (factorProjection n m i Q))-g Q) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ (Q : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)))
        (slope : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)))
        (p : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
        (A : Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ),
        Q ∈ O ∧ ‖slope‖ ≤ δ ∧
        IsLocalMin (fun R => (∑ i, α i*compactInfConvolution K v κ (factorProjection n m i R))-
          g R-⟪slope,R⟫_ℝ) Q ∧
        ∀ i, RealSecondJet (compactInfConvolution K v κ) (factorProjection n m i Q) (p i) (A i) := by
  let F : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)) → ℝ :=
    fun Q => (∑ i, α i*compactInfConvolution K v κ (factorProjection n m i Q))-g Q
  let Λ : ℝ := (∑ i, α i)/κ+C
  have hConv := product_compactInfConvolution_jensen_convex K v hK hNE hv hv0
    (factorProjection n m) (factorProjection_norm_le n m) α hα hκ g C hg
  have hSemi : ConvexOn ℝ (Metric.ball xh (2*r)) (fun Q => -F Q+Λ/2*‖Q‖^2) := by
    have hOn : ConvexOn ℝ (Metric.ball xh (2*r)) (fun Q => -F Q+Λ*(‖Q‖^2/2)) :=
      hConv.subset (subset_univ _) (convex_ball xh (2*r))
    convert hOn using 1
    funext Q
    dsimp [Λ,F]
    ring
  obtain ⟨δ₀,hδ₀,hJensen⟩ := Yau.LeafProofs.L04.1 (2*n+1+2*n*m) F Λ xh r O
    hr hO hxh hOC hBall hSemi hGap
  refine ⟨δ₀,hδ₀,?_⟩
  intro δ hδ hδle
  obtain ⟨Q,hQ,p,A,hJets⟩ := compactInfConvolution_simultaneous_jets n m K v hK hNE hv hv0 hκ
    _ (hJensen δ hδ hδle)
  obtain ⟨hQO,slope,hNorm,hMinimum⟩ := hQ
  refine ⟨Q,slope,p,A,hQO,hNorm,?_,hJets⟩
  filter_upwards [hO.mem_nhds hQO] with R hRO
  exact hMinimum R (subset_closure hRO)

end Yau.NodeProofs.E02Aux
