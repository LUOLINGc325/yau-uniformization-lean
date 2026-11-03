import Yau.Proofs.E02PackedContactSequence
import Yau.Proofs.E02InfContactCluster

open Matrix Set Filter
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- An ACTUAL converging global affine-minimum contact sequence has
zero original physical product gap. All sources and the bound M stay fixed. -/
theorem actual_packed_global_minimizer_cluster {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (f : ComplexVector n × ℝ → ℝ) (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (P₀ : Herm m) (θ : ℝ) (V : Set (ComplexVector n × ℝ)) (hV : IsOpen V)
    (hf : ContDiffOn ℝ 2 f V) (O : Set (ProductPoint n m))
    (hOU : closure O ⊆ productOpenDomain α V)
    (K : Set (EuclideanSpace ℝ (Fin (4*n+1)))) (hK : IsCompact K) (hNE : K.Nonempty)
    (hv : LowerSemicontinuousOn (packedEnvelopeReal X h T x) K)
    (hv0 : ∀ q ∈ K, 0 ≤ packedEnvelopeReal X h T x q)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ q ∈ K, packedEnvelopeReal X h T x q ≤ M)
    (hProj : ∀ Q ∈ closure O, ∀ i, factorProjection n m i (productRealCoordinates n m Q) ∈ K)
    (hNonneg : ∀ Q ∈ closure O, 0 ≤ actualProductGap X h T x f α P₀ θ Q)
    (Qstar : ProductPoint n m) (hStar : Qstar ∈ closure O)
    (hCenter : actualProductGap X h T x f α P₀ θ Qstar ≤ 0)
    (κ : ℕ → ℝ) (hκ : ∀ j, 0 < κ j) (hκLim : Tendsto κ atTop (𝓝 0))
    (Q slope : ℕ → EuclideanSpace ℝ (Fin (2*n+1+2*n*m)))
    (Q₀ : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)))
    (hQ : ∀ j, Q j ∈ (productRealCoordinates n m) '' closure O)
    (hQ₀ : Q₀ ∈ (productRealCoordinates n m) '' closure O)
    (hQLim : Tendsto Q atTop (𝓝 Q₀)) (hSlopeLim : Tendsto slope atTop (𝓝 0))
    (hMin : ∀ j, ∀ R ∈ (productRealCoordinates n m) '' closure O,
      ((∑ i, α i*compactInfConvolution K (packedEnvelopeReal X h T x) (κ j) (factorProjection n m i (Q j)))-
        productCostPacked f α P₀ θ (Q j))-⟪slope j,Q j⟫_ℝ ≤
      ((∑ i, α i*compactInfConvolution K (packedEnvelopeReal X h T x) (κ j) (factorProjection n m i R))-
        productCostPacked f α P₀ θ R)-⟪slope j,R⟫_ℝ) :
    actualProductGap X h T x f α P₀ θ ((productRealCoordinates n m).symm Q₀) = 0 := by
  let e := productRealCoordinates n m
  let S := e '' closure O
  have hPJ : ∀ R ∈ S, ∀ i, factorProjection n m i R ∈ K := by
    rintro R ⟨q,hq,rfl⟩ i
    simpa only [e] using hProj q hq i
  have hg : ContinuousOn (productCostPacked f α P₀ θ) S := by
    rintro R ⟨q,hq,rfl⟩
    simpa only [e] using (productCostPacked_contDiffAt f α P₀ θ q
      (hf.contDiffAt (hV.mem_nhds (hOU hq).1))
      ((fullRankRect_iff_posDef _).mp (hOU hq).2)).continuousAt.continuousWithinAt
  have hF0 : ∀ R ∈ S, 0 ≤ (∑ i, α i*packedEnvelopeReal X h T x (factorProjection n m i R))-
      productCostPacked f α P₀ θ R := by
    rintro R ⟨q,hq,rfl⟩
    simpa only [e,packed_actualProductGap_eq] using hNonneg q hq
  have hCenterκ (j : ℕ) :
      (∑ i, α i*compactInfConvolution K (packedEnvelopeReal X h T x) (κ j) (factorProjection n m i (e Qstar)))-
        productCostPacked f α P₀ θ (e Qstar) ≤ 0 := by
    have hPoint : (∑ i, α i*packedEnvelopeReal X h T x (factorProjection n m i (e Qstar)))-
        productCostPacked f α P₀ θ (e Qstar) ≤ 0 := by
      simpa only [e,packed_actualProductGap_eq] using hCenter
    apply le_trans (b := (∑ i, α i*packedEnvelopeReal X h T x (factorProjection n m i (e Qstar)))-
      productCostPacked f α P₀ θ (e Qstar)) ?_ hPoint
    have hEach (i : Fin m) :
        compactInfConvolution K (packedEnvelopeReal X h T x) (κ j) (factorProjection n m i (e Qstar)) ≤
          packedEnvelopeReal X h T x (factorProjection n m i (e Qstar)) := by
      simpa only [e] using compactInfConvolution_le K (packedEnvelopeReal X h T x) hv0 (hκ j)
        (factorProjection n m i (productRealCoordinates n m Qstar)) (hProj Qstar hStar i)
    exact sub_le_sub_right (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hEach i) (hα i))) _
  have hCluster := compactInfConvolution_affine_minimizer_cluster_zero
    K (packedEnvelopeReal X h T x) hK hNE hv hv0 S
    (fun i R => factorProjection n m i R) (fun i => (factorProjection n m i).continuous)
    hPJ hM (fun R hR i => hBound _ (hPJ R hR i)) α hα
    (productCostPacked f α P₀ θ) hg hF0 κ hκ hκLim Q Q₀ (e Qstar) hQ hQ₀
    (mem_image_of_mem e hStar) hQLim slope hSlopeLim hCenterκ hMin
  have hEq := packed_actualProductGap_eq X h T x f α P₀ θ (e.symm Q₀)
  rw [show productRealCoordinates n m (e.symm Q₀) = Q₀ from e.apply_symm_apply Q₀] at hEq
  exact hEq.symm.trans hCluster

end Yau.NodeProofs.E02Aux
