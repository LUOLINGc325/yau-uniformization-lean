import Yau.LeafProofs.L23FieldMetricParallelCalculus

/-! Finitely many genuine coordinate windows cover a smooth compact path. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem exists_uniform_curve_chart_windows (γ : ℝ → M.Carrier) (J : Set ℝ)
    (hJ : IsOpen J) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ J →
    ∃ (N : ℕ) (ρ : ℝ) (c : Fin (N+1) → M.Carrier), 0 < ρ ∧
      ∀ (i : Fin (N+1)) (t : ℝ),
        t ∈ Set.Ioo ((i.val : ℝ)/(N+1 : ℕ)-ρ) (((i.val : ℝ)+1)/(N+1 : ℕ)+ρ) →
        t ∈ J ∧ γ t ∈ (chartAt (ComplexVector n) (c i)).source := by
  letI := manifold_realSmooth M
  intro hγ
  classical
  let S := Set.Icc (0 : ℝ) 1
  let U : S → Set ℝ := fun s => J ∩ γ ⁻¹' (chartAt (ComplexVector n) (γ s.val)).source
  have hU : ∀ s, IsOpen (U s) := fun s =>
    hγ.continuousOn.isOpen_inter_preimage hJ (chartAt (ComplexVector n) (γ s.val)).open_source
  have hcover : S ⊆ ⋃ s : S, U s := by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨t,ht⟩,hunit ht,mem_chart_source _ _⟩
  obtain ⟨η,hη,hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hU hcover
  obtain ⟨N,hN⟩ := exists_nat_gt (2/η)
  let k : ℝ := (N+1 : ℕ)
  have hk : 0 < k := by dsimp [k]; positivity
  let Δ := 1/k
  have hΔη : Δ < η/2 := by
    have H := (div_lt_iff₀ hη).mp hN
    apply (div_lt_iff₀ hk).mpr
    dsimp only [k]
    push_cast
    nlinarith
  have hcenters (i : Fin (N+1)) : (i.val : ℝ)/k ∈ S := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hk.le,(div_le_one hk).mpr ?_⟩
    dsimp only [k]
    exact_mod_cast i.isLt.le
  have hex : ∀ i : Fin (N+1), ∃ c : M.Carrier,
      Metric.ball ((i.val : ℝ)/k) η ⊆ J ∩ γ ⁻¹' (chartAt (ComplexVector n) c).source := by
    intro i
    obtain ⟨s,hs⟩ := hleb _ (hcenters i)
    exact ⟨γ s.val,hs⟩
  choose c hc using hex
  refine ⟨N,η/4,c,div_pos hη (by norm_num),?_⟩
  intro i t ht
  apply hc i
  have Hupper : t < (i.val : ℝ)/k+Δ+η/4 := by
    have Hratio : ((i.val : ℝ)+1)/k = (i.val : ℝ)/k+Δ := by dsimp only [Δ]; ring
    have Hhi : t < ((i.val : ℝ)+1)/k+η/4 := ht.2
    rwa [Hratio] at Hhi
  have Hlower : (i.val : ℝ)/k-η/4 < t := ht.1
  rw [Metric.mem_ball,Real.dist_eq,abs_lt]
  constructor <;> linarith

end Yau.LeafProofs.L23Aux
