import Yau.Proofs.C01PathLengthComparison
import Yau.Proofs.C01ExitSphere

/-! A genuine first level hit confines the initial segment of a path
to the original compact ball. The profile is bounded by the exact
extended length of that segment. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

/-- The compact first zero set supplies a first crossing, not merely an
arbitrary point given by the intermediate value theorem. -/
theorem exists_first_exit_level {f : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hstart : f a < L) (hend : L ≤ f b) :
    ∃ u ∈ Set.Ioc a b, f u = L ∧ ∀ s ∈ Set.Icc a u, f s ≤ L := by
  let T : Set (Set.Icc a b) := {u | f u = L}
  have hTc : IsCompact T := (isClosed_eq hf.domRestrict continuous_const).isCompact
  have himage : IsCompact (Subtype.val '' T) := hTc.image continuous_subtype_val
  obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc hab hf ⟨hstart.le, hend⟩
  have hne : (Subtype.val '' T).Nonempty := ⟨v, ⟨⟨v, hv⟩, hfv, rfl⟩⟩
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
  have humin : (u' : ℝ) ≤ w := hu.2 ⟨⟨w, hsub hw⟩, hfw, rfl⟩
  linarith [hw.2]

variable {n : ℕ} {M : ComplexManifold n}

theorem exists_confined_first_exit
    (g : SmoothMetric M) (o : M.Carrier) (L : ℝ) (hL : 0 < L)
    (f : ℝ → M.Carrier) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hf₀ : f 0 = o) (hend : L ≤ inducedDistance g.form o (f 1)) :
    ∃ u ∈ Set.Ioc (0 : ℝ) 1, f u ∈ initialDistanceSphere g o L ∧
      Set.MapsTo f (Set.Icc 0 u) {x | inducedDistance g.form o x ≤ L} := by
  have hco : Continuous (inducedDistance g.form o) :=
    (Yau.LeafProofs.L12Aux.continuous_inducedDistance g).comp
      (continuous_const.prodMk continuous_id)
  have hc : ContinuousOn (fun s => inducedDistance g.form o (f s)) (Set.Icc (0 : ℝ) 1) :=
    hco.comp_continuousOn hf
  obtain ⟨u, hu, hhit, hconfined⟩ := exists_first_exit_level zero_le_one hc
    (by simpa only [hf₀, g.induced_distance_eq_zero.mpr rfl] using hL) hend
  exact ⟨u, hu, hhit, hconfined⟩

theorem exit_profile_le_actualPathELength_at_hit
    (g : SmoothMetric M) (k : HermitianField M) (hk : MetricSmooth k)
    (o : M.Carrier) (L : ℝ) (hL : 0 ≤ L)
    (f : ℝ → M.Carrier) :
    letI := manifold_realSmooth M
    ∀ (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f), f 0 = o →
    ∀ u : ℝ, 0 ≤ u → f u ∈ initialDistanceSphere g o L →
      ENNReal.ofReal (exitDistanceProfile g k o L) ≤ actualPathELength k f 0 u := by
  letI := manifold_realSmooth M
  intro hf hf₀ u hu hhit
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => underlyingRealTangentNormedAddCommGroup k z
  have hd := exitDistanceProfile_le g k hk o L hL (f u) hhit
  have hs := riemannianEDist_le_pathELength_of_contMDiffAt_Ioo k hk hu
    hf.continuous.continuousOn (fun s _ => hf.contMDiffAt)
  rw [hf₀] at hs
  calc
    _ ≤ ENNReal.ofReal (inducedDistance k o (f u)) := ENNReal.ofReal_le_ofReal hd
    _ = Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) o (f u) :=
      inducedDistance_eq_riemannianEDist k hk o (f u)
    _ ≤ _ := hs

end Yau.NodeProofs.C01Aux
