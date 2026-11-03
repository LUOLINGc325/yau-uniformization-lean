import Yau.LeafProofs.L03CutoffEnergyBounds

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem cauchySeq_of_two_dist_bound {E F G : Type*}
    [PseudoMetricSpace E] [PseudoMetricSpace F] [PseudoMetricSpace G]
    (u : ℕ → E) (v : ℕ → F) (w : ℕ → G) (hu : CauchySeq u) (hv : CauchySeq v)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ i j, dist (w i) (w j) ≤ C * dist (u i) (u j) + D * dist (v i) (v j)) :
    CauchySeq w := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ := ε / (C + D + 1)
  have hp : 0 < C + D + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hp
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu δ hδ
  obtain ⟨P, hP⟩ := Metric.cauchySeq_iff.mp hv δ hδ
  refine ⟨max N P, ?_⟩
  intro i hi j hj
  have h1 := hN i ((le_max_left N P).trans hi) j ((le_max_left N P).trans hj)
  have h2 := hP i ((le_max_right N P).trans hi) j ((le_max_right N P).trans hj)
  have he : (C + D + 1) * δ = ε := mul_div_cancel₀ ε (ne_of_gt hp)
  calc
    dist (w i) (w j) ≤ C * dist (u i) (u j) + D * dist (v i) (v j) := hb i j
    _ ≤ C * δ + D * δ := add_le_add
      (mul_le_mul_of_nonneg_left h1.le hC) (mul_le_mul_of_nonneg_left h2.le hD)
    _ < ε := by nlinarith

theorem smooth_compact_sub {A B : RealForm M k}
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    SmoothRealForm (A - B) ∧ CompactlySupportedRealForm (A - B) := by
  have hs := (smoothFormSubmodule (M := M) k).sub_mem hA hB
  have hc := compactlySupportedRealForm_add A ((-1 : ℝ) • B) hcA
    (compactlySupportedRealForm_multiply (fun _ => (-1 : ℝ)) B hcB)
  rw [neg_one_smul ℝ B] at hc
  exact ⟨hs, by simpa only [sub_eq_add_neg] using hc⟩

/-- A differential with its actual first-order cutoff estimate sends
an energy Cauchy sequence to a cutoff-output Cauchy sequence. -/
theorem cutoff_differential_cauchy {l : ℕ}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (P : RealForm M k → RealForm M l)
    (hPsub : ∀ A B, SmoothRealForm A → SmoothRealForm B → P (A - B) = P A - P B)
    (hPL2 : ∀ A, SmoothRealForm A → CompactlySupportedRealForm A → L2RealForm g.form μ (P A))
    (η : M.Carrier → ℝ) (hη : SmoothFn η)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ A, ∀ hAs : SmoothRealForm A, ∀ hcA : CompactlySupportedRealForm A,
      ‖realizeActualForm g μ (P (multiplyRealForm η A))
        (hPL2 _ (smoothRealForm_multiply η A hη hAs) (compactlySupportedRealForm_multiply η A hcA))‖ ≤
      C * ‖realizeActualForm g μ (P A) (hPL2 A hAs hcA)‖ +
        D * ‖realizeActualForm g μ A (smooth_compactlySupported_l2RealForm g μ hμ A hAs hcA)‖)
    (As : ℕ → RealForm M k) (hAs : ∀ m, SmoothRealForm (As m))
    (hcAs : ∀ m, CompactlySupportedRealForm (As m))
    (hval : CauchySeq (fun m => realizeActualForm g μ (As m)
      (smooth_compactlySupported_l2RealForm g μ hμ _ (hAs m) (hcAs m))))
    (hout : CauchySeq (fun m => realizeActualForm g μ (P (As m)) (hPL2 _ (hAs m) (hcAs m)))) :
    CauchySeq (fun m => realizeActualForm g μ (P (multiplyRealForm η (As m)))
      (hPL2 _ (smoothRealForm_multiply η _ hη (hAs m)) (compactlySupportedRealForm_multiply η _ (hcAs m)))) := by
  apply cauchySeq_of_two_dist_bound _ _ _ hout hval C D hC hD
  intro i j
  obtain ⟨hs, hc⟩ := smooth_compact_sub (hAs i) (hcAs i) (hAs j) (hcAs j)
  have h := hb (As i - As j) hs hc
  have hm : multiplyRealForm η (As i - As j) = multiplyRealForm η (As i) - multiplyRealForm η (As j) :=
    (multiplyRealFormLinear η).map_sub _ _
  have ho := hPsub (As i) (As j) (hAs i) (hAs j)
  have hcut := hPsub (multiplyRealForm η (As i)) (multiplyRealForm η (As j))
    (smoothRealForm_multiply η _ hη (hAs i)) (smoothRealForm_multiply η _ hη (hAs j))
  simp only [dist_eq_norm]
  rw [← realizeActualForm_sub, ← realizeActualForm_sub, ← realizeActualForm_sub]
  simpa only [hm, hcut, ho] using h

/-- Multiplying an actual d/δ energy-convergent compact smooth sequence
by a compact smooth scalar preserves convergence of both outputs in the
genuine Hilbert completions. No section representation of a general
Hilbert vector is used here. -/
theorem exists_hodge_energy_cutoff_limits
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (As : ℕ → RealForm M k) (hAs : ∀ m, SmoothRealForm (As m))
    (hcAs : ∀ m, CompactlySupportedRealForm (As m))
    (T : RealForm M k) (V : RealForm M (k + 1)) (W : RealForm M (k - 1))
    (hT : L2RealForm g.form μ T) (hV : L2RealForm g.form μ V) (hW : L2RealForm g.form μ W)
    (htT : Tendsto (fun m => formL2DistanceSq g.form μ (As m) T) atTop (𝓝 0))
    (htV : Tendsto (fun m => formL2DistanceSq g.form μ (exteriorRealForm (As m)) V) atTop (𝓝 0))
    (htW : Tendsto (fun m => formL2DistanceSq g.form μ (hodgeLowerRealForm g.form k (As m)) W) atTop (𝓝 0))
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η) :
    ∃ Vη : L2FormHilbert g μ (k + 1), ∃ Wη : L2FormHilbert g μ (k - 1),
      Tendsto (fun m => realizeActualForm g μ (exteriorRealForm (multiplyRealForm η (As m)))
        (smooth_compactlySupported_l2RealForm g μ hμ _
          (exteriorRealForm_smooth _ (smoothRealForm_multiply η _ hη (hAs m)))
          (exteriorRealForm_compactlySupported _ (smoothRealForm_multiply η _ hη (hAs m))
            (compactlySupportedRealForm_multiply η _ (hcAs m))))) atTop (𝓝 Vη) ∧
      Tendsto (fun m => realizeActualForm g μ (hodgeLowerRealForm g.form k (multiplyRealForm η (As m)))
        (smooth_compactlySupported_l2RealForm g μ hμ _
          (hodgeLowerRealForm_smooth_compact g μ hμ _ (smoothRealForm_multiply η _ hη (hAs m))
            (compactlySupportedRealForm_multiply η _ (hcAs m))).1
          (hodgeLowerRealForm_smooth_compact g μ hμ _ (smoothRealForm_multiply η _ hη (hAs m))
            (compactlySupportedRealForm_multiply η _ (hcAs m))).2)) atTop (𝓝 Wη) := by
  obtain ⟨C, D, hC, hD, hηb, hgrad⟩ := exists_compact_cutoff_uniform_bounds g η hη hcη
  have hA2 (m : ℕ) := smooth_compactlySupported_l2RealForm g μ hμ _ (hAs m) (hcAs m)
  let hd : ∀ B : RealForm M k, SmoothRealForm B → CompactlySupportedRealForm B →
      L2RealForm g.form μ (exteriorRealForm B) := fun B hs hc =>
    smooth_compactlySupported_l2RealForm g μ hμ _ (exteriorRealForm_smooth B hs)
      (exteriorRealForm_compactlySupported B hs hc)
  let hl : ∀ B : RealForm M k, SmoothRealForm B → CompactlySupportedRealForm B →
      L2RealForm g.form μ (hodgeLowerRealForm g.form k B) := fun B hs hc =>
    smooth_compactlySupported_l2RealForm g μ hμ _ (hodgeLowerRealForm_smooth_compact g μ hμ B hs hc).1
      (hodgeLowerRealForm_smooth_compact g μ hμ B hs hc).2
  have hv := ((tendsto_realizeL2Form_iff g μ (fun m => L2FormSpace.ofSection (As m) (hA2 m))
    (L2FormSpace.ofSection T hT)).mpr htT).cauchySeq
  have hdv := ((tendsto_realizeL2Form_iff g μ
    (fun m => L2FormSpace.ofSection (exteriorRealForm (As m)) (hd _ (hAs m) (hcAs m)))
      (L2FormSpace.ofSection V hV)).mpr htV).cauchySeq
  have hlv := ((tendsto_realizeL2Form_iff g μ
    (fun m => L2FormSpace.ofSection (hodgeLowerRealForm g.form k (As m)) (hl _ (hAs m) (hcAs m)))
      (L2FormSpace.ofSection W hW)).mpr htW).cauchySeq
  have hdη := cutoff_differential_cauchy g μ hμ exteriorRealForm exteriorRealForm_sub hd η hη C D hC hD
    (fun B hs hc => exterior_cutoff_graph_norm_le g μ η hη C D hC hD hηb hgrad B hs
      (smooth_compactlySupported_l2RealForm g μ hμ B hs hc) (hd B hs hc) _)
    As hAs hcAs hv hdv
  have hlη := cutoff_differential_cauchy g μ hμ (hodgeLowerRealForm g.form k)
    (hodgeLowerRealForm_sub g μ hμ) hl η hη C D hC hD
    (fun B hs hc => hodgeLower_cutoff_graph_norm_le g μ hμ η hη C D hC hD hηb hgrad B hs
      (smooth_compactlySupported_l2RealForm g μ hμ B hs hc) (hl B hs hc) _)
    As hAs hcAs hv hlv
  obtain ⟨Vη, htVη⟩ := cauchySeq_tendsto_of_complete hdη
  obtain ⟨Wη, htWη⟩ := cauchySeq_tendsto_of_complete hlη
  exact ⟨Vη, Wη, htVη, htWη⟩

end Yau.LeafProofs.L03
