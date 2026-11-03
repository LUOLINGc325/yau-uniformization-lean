import Yau.Proofs.U02RealDifferential

/-! A first-exit estimate for the original induced distance. Only the
portion of the actual curve inside the fixed metric ball is controlled. -/

open scoped Manifold Topology ContDiff ENNReal
open Filter MeasureTheory Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint
open Yau.LeafProofs.L12Aux

/-- Finite-dimensional path arguments below use this elementary real
first-level argument, with the first crossing selected from a compact set. -/
theorem exists_first_level {f : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hstart : f a < L) (hend : L ≤ f b) :
    ∃ u ∈ Set.Ioc a b, f u = L ∧ ∀ s ∈ Set.Icc a u, f s ≤ L := by
  let T : Set (Set.Icc a b) := {u | f u = L}
  have hTc : IsCompact T := (isClosed_eq hf.restrict continuous_const).isCompact
  have himage : IsCompact (Subtype.val '' T) := hTc.image continuous_subtype_val
  obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hab hf ⟨hstart.le, hend⟩
  have hne : (Subtype.val '' T).Nonempty := ⟨v, ⟨⟨v,hv⟩,hfv,rfl⟩⟩
  obtain ⟨u, hu⟩ := himage.exists_isLeast hne
  obtain ⟨u', hu', rfl⟩ := hu.1
  have huI := u'.2
  have huval : f u' = L := hu'
  have hau : a < (u' : ℝ) := by
    by_contra h
    have heq : (u' : ℝ) = a := le_antisymm (le_of_not_gt h) huI.1
    rw [heq] at huval
    linarith
  refine ⟨u', ⟨hau, huI.2⟩, huval, ?_⟩
  intro s hs
  by_contra h
  have hfs : L < f s := lt_of_not_ge h
  have hsu : s < (u' : ℝ) := by
    apply lt_of_le_of_ne hs.2
    intro heq
    rw [heq, huval] at hfs
    exact lt_irrefl _ hfs
  have hsub : Set.Icc a s ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl (hs.2.trans huI.2)
  obtain ⟨w, hw, hfw⟩ := intermediate_value_Icc hs.1 (hf.mono hsub) ⟨hstart.le, hfs.le⟩
  have humin : (u' : ℝ) ≤ w := hu.2 ⟨⟨w,hsub hw⟩,hfw,rfl⟩
  linarith [hw.2]

theorem short_path_endpoint_distance {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) (gamma : ℝ → M.Carrier)
    {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (hBR : B < R)
    (hstart : gamma 0 = x) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 gamma (Set.Icc 0 1) →
    (∀ t ∈ Set.Icc (0 : ℝ) 1, inducedDistance g.form x (gamma t) ≤ R →
      ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) gamma t 1‖ ≤ B) →
    inducedDistance g.form x (gamma 1) < R := by
  letI := manifold_realSmooth M
  letI := inducedMetricSpace g
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro hgamma hspeed
  by_contra hfar
  have hf : ContinuousOn (fun t => inducedDistance g.form x (gamma t)) (Set.Icc 0 1) :=
    (continuous_const.dist continuous_id).comp_continuousOn hgamma.continuousOn
  obtain ⟨u, hu, hhit, hbefore⟩ := exists_first_level zero_le_one hf
    (by simpa only [hstart, g.induced_distance_eq_zero.mpr rfl] using hR)
    (le_of_not_gt hfar)
  have hdist : ENNReal.ofReal R ≤ Manifold.pathELength 𝓘(ℝ, ComplexVector n) gamma 0 u := by
    rw [← hhit, inducedDistance_eq_riemannianEDist g]
    exact Manifold.riemannianEDist_le_pathELength
      (hgamma.mono (Set.Icc_subset_Icc le_rfl hu.2)) hstart rfl hu.1.le
  have hlen : Manifold.pathELength 𝓘(ℝ, ComplexVector n) gamma 0 u ≤ ENNReal.ofReal B := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    calc
      _ ≤ ∫⁻ _t in Set.Icc (0 : ℝ) u, ENNReal.ofReal B := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hspeed t ⟨ht.1, ht.2.trans hu.2⟩ (hbefore t ht))
      _ ≤ ∫⁻ _t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal B :=
        lintegral_mono_set (Set.Icc_subset_Icc le_rfl hu.2)
      _ = _ := by simp
  exact (not_le_of_gt hBR) ((ENNReal.ofReal_le_ofReal_iff hB).mp (hdist.trans hlen))

end Yau.NodeProofs.U02Proof
