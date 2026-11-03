import Yau.Proofs.C05CompactInvariantFlowDiagonal

/-! Forward completeness on a compact locally forward-invariant set. The
chosen curves include a genuine fixed negative-time interval at time zero. -/
noncomputable section
open scoped Manifold Topology ContDiff
open Set Filter
namespace Yau.Proofs.C05CompactInvariantFlowAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]

 theorem exists_forward_curves_with_uniform_negative_extension
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞ (fun x => (⟨x,v x⟩ : TangentBundle I M)))
    (K : Set M) (hK : IsCompact K)
    (hinv : ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε → γ 0 ∈ K →
      IsMIntegralCurveOn γ v (Ioo (-ε) ε) → ∀ t ∈ Ico (0:ℝ) ε, γ t ∈ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ F : ℝ → M → M,
      (∀ x ∈ K, F 0 x = x) ∧
      (∀ x ∈ K, ∀ t, 0 ≤ t → F t x ∈ K) ∧
      (∀ x ∈ K, IsMIntegralCurveOn (fun t => F t x) v (Ioi (-ε))) ∧
      (∀ x ∈ K, ContinuousOn (fun t => F t x) (Ici (0:ℝ))) := by
  classical
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ,E)) 1 (fun x => (⟨x,v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num)
  obtain ⟨ε,hε,hloc⟩ := exists_uniform_integral_curves_on_compact v hv1 K hK
  have hcurves (x : M) (hx : x ∈ K) := exists_forward_curve_of_horizons v hv1 K hε x
    (exists_forward_horizons_of_uniform_local_invariant v hv1 K hε hloc hinv x hx)
  choose γ hγ0 hγ hγK using hcurves
  let F : ℝ → M → M := fun t x => if hx : x ∈ K then γ x hx t else x
  have hFx (x : M) (hx : x ∈ K) : (fun t => F t x) = γ x hx := by
    funext t
    simp only [F,dite_eq_left hx]
  refine ⟨ε,hε,F,?_,?_,?_,?_⟩
  · intro x hx
    simpa only [F,dite_eq_left hx] using hγ0 x hx
  · intro x hx t ht
    simpa only [F,dite_eq_left hx] using hγK x hx t ht
  · intro x hx
    rw [hFx x hx]
    exact hγ x hx
  · intro x hx
    rw [hFx x hx]
    apply (hγ x hx).continuousOn.mono
    intro t ht
    exact (neg_lt_zero.mpr hε).trans_le ht

 theorem exists_forward_integral_curves_of_compact_local_invariant
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞ (fun x => (⟨x,v x⟩ : TangentBundle I M)))
    (K : Set M) (hK : IsCompact K)
    (hinv : ∀ (γ : ℝ → M) (ε : ℝ), 0 < ε → γ 0 ∈ K →
      IsMIntegralCurveOn γ v (Ioo (-ε) ε) → ∀ t ∈ Ico (0:ℝ) ε, γ t ∈ K) :
    ∃ F : ℝ → M → M,
      (∀ x ∈ K, F 0 x = x) ∧
      (∀ x ∈ K, ∀ t, 0 ≤ t → F t x ∈ K) ∧
      (∀ x ∈ K, ∀ t, 0 ≤ t → IsMIntegralCurveAt (fun s => F s x) v t) ∧
      (∀ x ∈ K, ContinuousOn (fun t => F t x) (Ici (0:ℝ))) := by
  obtain ⟨ε,hε,F,hF0,hFK,hF,hcont⟩ := exists_forward_curves_with_uniform_negative_extension v hv K hK hinv
  refine ⟨F,hF0,hFK,?_,hcont⟩
  intro x hx t ht
  exact (hF x hx).isMIntegralCurveAt (isOpen_Ioi.mem_nhds (show -ε < t by linarith))

end Yau.Proofs.C05CompactInvariantFlowAux
