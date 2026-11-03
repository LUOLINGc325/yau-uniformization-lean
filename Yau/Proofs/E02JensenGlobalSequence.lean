import Yau.Proofs.E02JensenGlobalContacts
import Yau.Proofs.E02CompactEpiGap

open Set Filter
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux

/-- Actual native Jensen/Aleksandrov contacts for a κ-sequence tending
to zero. K and its bound M precede the sequence; all factor jets use ONE
shared product point for each κ. No uniform Jensen slope radius is assumed. -/
theorem exists_jensen_global_contact_sequence (n m : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin (4*n+1))))
    (v : EuclideanSpace ℝ (Fin (4*n+1)) → ℝ)
    (hK : IsCompact K) (hNE : K.Nonempty) (hv : LowerSemicontinuousOn v K)
    (hv0 : ∀ q ∈ K, 0 ≤ v q) (M : ℝ) (hM : 0 ≤ M)
    (α : Fin m → ℝ) (hα : ∀ i, 0 ≤ α i)
    (g : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)) → ℝ) (hg : Continuous g)
    (C : ℝ) (hConv : ConvexOn ℝ univ (fun Q => g Q+C*(‖Q‖^2/2)))
    (O : Set (EuclideanSpace ℝ (Fin (2*n+1+2*n*m))))
    (hO : IsOpen O) (hOC : IsCompact (closure O))
    (Qstar : EuclideanSpace ℝ (Fin (2*n+1+2*n*m))) (hStar : Qstar ∈ O)
    (hProj : ∀ Q ∈ closure O, ∀ i, factorProjection n m i Q ∈ K)
    (hBound : ∀ Q ∈ closure O, ∀ i, v (factorProjection n m i Q) ≤ M)
    (hCenter : (∑ i, α i*v (factorProjection n m i Qstar))-g Qstar ≤ 0)
    (γ κmax : ℝ) (hγ : 0 < γ) (hκmax : 0 < κmax)
    (hGap : ∀ Q ∈ closure O \ O, γ ≤ (∑ i, α i*v (factorProjection n m i Q))-g Q) :
    ∃ (κ : ℕ → ℝ)
      (Q slope : ℕ → EuclideanSpace ℝ (Fin (2*n+1+2*n*m)))
      (p : ℕ → Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
      (A : ℕ → Fin m → EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ),
      (∀ j, 0 < κ j ∧ κ j < κmax) ∧ Tendsto κ atTop (𝓝 0) ∧
      Tendsto slope atTop (𝓝 0) ∧ ∀ j, Q j ∈ O ∧
        IsLocalMin (fun R => (∑ i, α i*compactInfConvolution K v (κ j) (factorProjection n m i R))-
          g R-⟪slope j,R⟫_ℝ) (Q j) ∧
        (∀ R ∈ closure O,
          ((∑ i, α i*compactInfConvolution K v (κ j) (factorProjection n m i (Q j)))-g (Q j))-⟪slope j,Q j⟫_ℝ ≤
          ((∑ i, α i*compactInfConvolution K v (κ j) (factorProjection n m i R))-g R)-⟪slope j,R⟫_ℝ) ∧
        ∀ i, RealSecondJet (compactInfConvolution K v (κ j)) (factorProjection n m i (Q j))
          (p j i) (A j i) := by
  obtain ⟨κbase,_hAnti,hκbase,hBaseLim⟩ := exists_seq_strictAnti_tendsto' hκmax
  have hBoundaryCompact : IsCompact (closure O \ O) := hOC.diff hO
  have hEvent := compactInfConvolution_uniform_gap K v hK hNE hv hv0
    (closure O \ O) hBoundaryCompact (fun i Q => factorProjection n m i Q)
    (fun i => (factorProjection n m i).continuous)
    (fun Q hQ => hProj Q hQ.1) hM (fun Q hQ => hBound Q hQ.1)
    α hα g (hg.continuousOn) κbase (fun j => (hκbase j).1) hBaseLim
    (show γ/2 < γ by linarith) hGap
  obtain ⟨N,hN⟩ := eventually_atTop.mp hEvent
  let κ : ℕ → ℝ := fun j => κbase (j+N)
  have hκ : ∀ j, 0 < κ j ∧ κ j < κmax := fun j => hκbase (j+N)
  have hκLim : Tendsto κ atTop (𝓝 0) := hBaseLim.comp (tendsto_add_atTop_nat N)
  have hCenterκ (j : ℕ) :
      (∑ i, α i*compactInfConvolution K v (κ j) (factorProjection n m i Qstar))-g Qstar ≤ 0 := by
    apply le_trans (b := (∑ i, α i*v (factorProjection n m i Qstar))-g Qstar) ?_ hCenter
    exact sub_le_sub_right (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (compactInfConvolution_le K v hv0 (hκ j).1 _ (hProj Qstar (subset_closure hStar) i)) (hα i))) _
  have hGapκ (j : ℕ) : ∀ R ∈ closure O \ O,
      (∑ i, α i*compactInfConvolution K v (κ j) (factorProjection n m i Qstar))-g Qstar <
      (∑ i, α i*compactInfConvolution K v (κ j) (factorProjection n m i R))-g R := by
    intro R hR
    have hb := hN (j+N) (Nat.le_add_left N j) R hR
    exact (hCenterκ j).trans_lt ((by linarith : (0:ℝ) < γ/2).trans_le hb)
  obtain ⟨r,hr,hBall⟩ := hOC.isBounded.subset_ball_lt 0 Qstar
  choose δ₀ hδ₀ hContacts using (fun j => jensen_simultaneous_compactInf_global_jets n m K v
    hK hNE hv hv0 α hα (hκ j).1 g C hConv O Qstar r hr hO hStar hOC hBall (hGapκ j))
  let δ : ℕ → ℝ := fun j => min (δ₀ j) (1/((j:ℝ)+1))
  have hδ : ∀ j, 0 < δ j := fun j => lt_min (hδ₀ j) (by positivity)
  choose Q slope p A hQ hSlope hMin hGlobal hJets using
    (fun j => hContacts j (δ j) (hδ j) (min_le_left _ _))
  have hSlopeNorm : ∀ j, ‖slope j‖ ≤ 1/((j:ℝ)+1) :=
    fun j => (hSlope j).trans (min_le_right _ _)
  have hNormLim : Tendsto (fun j => ‖slope j‖) atTop (𝓝 0) :=
    squeeze_zero (fun j => norm_nonneg _) hSlopeNorm tendsto_one_div_add_atTop_nhds_zero_nat
  have hSlopeLim : Tendsto slope atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hNormLim
  exact ⟨κ,Q,slope,p,A,hκ,hκLim,hSlopeLim,fun j => ⟨hQ j,hMin j,hGlobal j,hJets j⟩⟩

end Yau.NodeProofs.E02Aux
