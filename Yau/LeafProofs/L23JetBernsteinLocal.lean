import Yau.LeafProofs.L23JetNormEvolution
import Yau.LeafProofs.L23JetClosedContinuity
import Yau.LeafProofs.L23BernsteinReaction
import Yau.LeafProofs.L23BernsteinStep

/-! The complete scalar Bernstein step instantiated with the original jets. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem jetSq_flowOp_le_of_lower_bound
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hσ : 0 ≤ σ) (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (x : M.Carrier) (hx : x ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (k : ℕ) (hk : 0 < k) (B : ℝ) (hB : 1 ≤ B)
    (hLower : ∀ j < k, jetSq (h t) j x ≤ B) :
    flowOp h σ (fun y s => jetSq (h s) k y) x t≤
      -σ*jetSq (h t) (k+1) x+
        σ*(jetEvolutionConstant n k*(k+1 : ℕ)*B)*(1+jetSq (h t) k x) := by
  have hr := reaction_sum_le k hk (fun j => jetSq (h t) j x) B hB
    (fun j => jetSq_nonneg (h t) j x) hLower
  have hs : 0 ≤ σ*jetEvolutionConstant n k :=
    mul_nonneg hσ (jetEvolutionConstant_pos n k).le
  have hp := mul_le_mul_of_nonneg_left hr hs
  have he := jetSq_flowOp_le h O a b σ hO hσ hflow x hx t ht k
  dsimp only [jetReactionSum] at he
  nlinarith [hp]

theorem jetSq_flowOp_le_of_all_lower_bound
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ : ℝ) (hO : IsOpen O)
    (hσ : 0 ≤ σ) (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (x : M.Carrier) (hx : x ∈ O) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (k : ℕ) (B : ℝ) (hB : 1 ≤ B) (hLower : ∀ j ≤ k, jetSq (h t) j x ≤ B) :
    flowOp h σ (fun y s => jetSq (h s) k y) x t≤
      -σ*jetSq (h t) (k+1) x+σ*(jetEvolutionConstant n k*(k+1 : ℕ)*B^2) := by
  have hr := lower_reaction_sum_le k (fun j => jetSq (h t) j x) B hB hLower
  have hp := mul_le_mul_of_nonneg_left hr
    (mul_nonneg hσ (jetEvolutionConstant_pos n k).le)
  have he := jetSq_flowOp_le h O a b σ hO hσ hflow x hx t ht k
  dsimp only [jetReactionSum] at he
  nlinarith [hp]

theorem jet_bernstein_local_step
    (h : ℝ → HermitianField M) (O S : Set M.Carrier) (a b σ b₀ T B G L : ℝ)
    (hO : IsOpen O) (hS : IsCompact S) (hSO : S ⊆ O)
    (ha : a < b) (hab₀ : a ≤ b₀) (hb₀T : b₀ < T) (hTb : T < b)
    (hσ : 0 < σ) (hB : 1 ≤ B) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (k : ℕ) (η : M.Carrier → ℝ → ℝ)
    (hη : ContinuousOn (fun p : M.Carrier × ℝ => η p.1 p.2) (S ×ˢ Set.Icc b₀ T))
    (hηRange : ∀ x ∈ S, ∀ t ∈ Set.Icc b₀ T, 0 ≤ η x t ∧ η x t ≤ 1)
    (hηBoundary : ∀ x ∈ S, x ∉ interior S → ∀ t ∈ Set.Icc b₀ T, η x t=0)
    (hSupports : ParabolicCutoffLowerSupports h σ η S b₀ T G L)
    (hLower : ∀ x ∈ interior S, ∀ t ∈ Set.Ioc b₀ T, 0 < η x t →
      ∀ j ≤ k, jetSq (h t) j x ≤ B) :
    ∀ q ∈ S, η q T=1 → jetSq (h T) (k+1) q≤
      bernsteinScalarBound σ B (jetEvolutionConstant n (k+1)*(k+2 : ℕ)*B)
        (jetEvolutionConstant n k*(k+1 : ℕ)*B^2) (T-b₀) G L := by
  have htime {t : ℝ} (ht : t ∈ Set.Ioc b₀ T) : t ∈ Set.Ioo a b :=
    ⟨hab₀.trans_lt ht.1,ht.2.trans_lt hTb⟩
  have hsubset : S ×ˢ Set.Icc b₀ T ⊆ Set.univ ×ˢ Set.Icc a b :=
    fun _ hp => ⟨Set.mem_univ _,⟨hab₀.trans hp.2.1,hp.2.2.trans hTb.le⟩⟩
  have hc₀ := jetEvolutionConstant_pos n k
  have hc₁ := jetEvolutionConstant_pos n (k+1)
  have hB₀ : 0 < B := by linarith
  apply bernstein_local_scalar_step h σ b₀ T B _ _ G L S hS hb₀T hσ hB
    (by positivity) (by positivity) hG hL
    (fun x t => jetSq (h t) k x) (fun x t => jetSq (h t) (k+1) x)
    (fun x t => jetSq (h t) (k+2) x) η
    ((jetSq_continuousOn_closed h a b ha hflow.1 k).mono hsubset)
    ((jetSq_continuousOn_closed h a b ha hflow.1 (k+1)).mono hsubset)
    hη (fun x _ t _ => jetSq_nonneg (h t) k x)
    (fun x _ t _ => jetSq_nonneg (h t) (k+1) x) hηRange hηBoundary
  · intro x hx t ht
    exact (jetSq_joint_contDiffAt h a b hflow.1 x k
      (z := chartPt x x) (mem_extChartAt_target x) t (htime ht)).of_le (by simp)
  · intro x hx t ht
    exact (jetSq_joint_contDiffAt h a b hflow.1 x (k+1)
      (z := chartPt x x) (mem_extChartAt_target x) t (htime ht)).of_le (by simp)
  · exact hSupports
  · intro x hx t ht hηpos
    have hl := hLower x hx t ht hηpos
    have hh := metricFamilySmooth_slice h hflow.1 ⟨(htime ht).1.le,(htime ht).2.le⟩
    refine ⟨hl k le_rfl,jetSq_nonneg (h t) (k+2) x,?_,?_,?_,?_⟩
    · exact jetSq_flowOp_le_of_all_lower_bound h O a b σ hO hσ.le hflow x
        (hSO (interior_subset hx)) t (htime ht) k B hB hl
    · simpa only [Nat.add_assoc] using jetSq_flowOp_le_of_lower_bound h O a b σ hO hσ.le
        hflow x (hSO (interior_subset hx)) t (htime ht) (k+1) (by omega) B hB
          (fun j hj => hl j (by omega))
    · exact realGradPair_jetSq_self_le (h t) hh k x
    · simpa only [Nat.add_assoc] using realGradPair_jetSq_self_le (h t) hh (k+1) x

end Yau.LeafProofs.L23Aux
