import Yau.LeafProofs.L23FieldMetricParallelSegment
import Yau.LeafProofs.L23FieldMetricCurveCharts

/-! A genuine global parallel frame along a compact path, constructed in finitely many charts. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1000000

theorem exists_parallel_frame_unit
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (J : Set ℝ) (hJ : IsOpen J) (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ J →
    ∀ F : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ 0),
    ∃ δ : ℝ, 0 < δ ∧
      ∃ P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u),
        P 0 = F ∧ Set.Ioo (-δ) (1+δ) ⊆ J ∧
        IsParallelFrameOn h γ P (Set.Ioo (-δ) (1+δ)) := by
  letI := manifold_realSmooth M
  intro hγ F
  obtain ⟨N,ρ,c,hρ,hcover⟩ := exists_uniform_curve_chart_windows γ J hJ hunit
    (hγ.of_le (by norm_num))
  let k : ℝ := (N+1 : ℕ)
  have hk : 0 < k := by dsimp only [k]; positivity
  let T : ℕ → ℝ := fun j => (j : ℝ)/k
  have hT0 : T 0 = 0 := by simp [T]
  have hTmono (j : ℕ) : T j < T (j+1) := by dsimp only [T]; exact (div_lt_div_iff_of_pos_right hk).mpr (by norm_num)
  have hTnonneg (j : ℕ) : 0 ≤ T j := div_nonneg (Nat.cast_nonneg _) hk.le
  have hstep (j : ℕ) (hj : j < N+1)
      (Fj : ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ (T j))) :
      ∃ δ : ℝ, 0 < δ ∧
        ∃ P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u),
          P (T j) = Fj ∧ Set.Ioo (T j-δ) (T (j+1)+δ) ⊆ J ∧
          IsParallelFrameOn h γ P (Set.Ioo (T j-δ) (T (j+1)+δ)) := by
    let i : Fin (N+1) := ⟨j,hj⟩
    let U := Set.Ioo (T j-ρ) (T (j+1)+ρ)
    have HU : ∀ t ∈ U, t ∈ J ∧ γ t ∈ (chartAt (ComplexVector n) (c i)).source := by
      intro t ht
      apply hcover i t
      simpa only [U,T,k,Nat.cast_add,Nat.cast_one] using ht
    obtain ⟨δ,hδ,P,hP,hsub,HP⟩ := exists_parallel_frame_segment h hh γ (c i) U isOpen_Ioo
      (hγ.mono (fun t ht => (HU t ht).1)) (fun t ht => (HU t ht).2)
      (T j) (T (j+1)) (hTmono j)
      (by intro t ht; constructor <;> linarith [ht.1,ht.2]) Fj
    exact ⟨δ,hδ,P,hP,fun t ht => (HU t (hsub ht)).1,HP⟩
  have Hind (j : ℕ) (hj : j ≤ N+1) :
      ∃ δ : ℝ, 0 < δ ∧
        ∃ P : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u),
          P 0 = F ∧ Set.Ioo (-δ) (T j+δ) ⊆ J ∧
          IsParallelFrameOn h γ P (Set.Ioo (-δ) (T j+δ)) := by
    induction j with
    | zero =>
      have HS := hstep 0 (Nat.zero_lt_succ N)
      rw [hT0] at HS
      obtain ⟨δ,hδ,P,hP,hsub,HP⟩ := HS F
      refine ⟨δ,hδ,P,?_,?_,?_⟩
      · exact hP
      · intro t ht
        apply hsub
        constructor
        · simpa only [hT0,zero_sub] using ht.1
        · linarith [ht.2,hTmono 0]
      · apply parallelFrameOn_mono h γ P HP
        intro t ht
        constructor
        · simpa only [hT0,zero_sub] using ht.1
        · linarith [ht.2,hTmono 0]
    | succ j IH =>
      obtain ⟨δ,hδ,P,hP,hsub,HP⟩ := IH (by omega)
      obtain ⟨ε,hε,Q,hQ,hQsub,HQ⟩ := hstep j (by omega) (P (T j))
      let θ := min δ ε
      have hθ : 0 < θ := lt_min hδ hε
      let R : (u : ℝ) → ComplexVector n →L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u) :=
        fun u => if u ≤ T j then P u else Q u
      have HR := parallelFrameOn_splice h γ P Q (-δ) (T j+δ) (T j-ε) (T (j+1)+ε) (T j)
        HP HQ (by constructor <;> linarith [hTnonneg j])
        (by constructor <;> linarith [hTmono j]) hQ.symm
      have hrestrict : Set.Ioo (-θ) (T (j+1)+θ) ⊆ Set.Ioo (-δ) (T (j+1)+ε) := by
        intro t ht
        constructor <;> linarith [ht.1,ht.2,min_le_left δ ε,min_le_right δ ε]
      refine ⟨θ,hθ,R,?_,?_,parallelFrameOn_mono h γ R HR hrestrict⟩
      · change (if (0 : ℝ) ≤ T j then P 0 else Q 0) = F
        rw [if_pos (hTnonneg j),hP]
      · intro t ht
        by_cases htT : t ≤ T j
        · apply hsub
          constructor <;> linarith [ht.1,min_le_left δ ε]
        · apply hQsub
          constructor <;> linarith [ht.2,min_le_right δ ε]
  obtain ⟨δ,hδ,P,hP,hsub,HP⟩ := Hind (N+1) le_rfl
  have hT1 : T (N+1) = 1 := by dsimp only [T]; exact div_self (ne_of_gt hk)
  exact ⟨δ,hδ,P,hP,by simpa only [hT1] using hsub,by simpa only [hT1] using HP⟩

end Yau.LeafProofs.L23Aux
