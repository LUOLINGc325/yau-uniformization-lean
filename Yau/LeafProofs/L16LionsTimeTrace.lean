import Yau.LeafProofs.L16LionsApproximation
import Yau.LeafProofs.L16LionsLimit

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16LionsTimeTrace
open Yau.LeafProofs.L16LionsApproximation Yau.LeafProofs.L16HilbertTimeRegularization
  Yau.LeafProofs.L16LionsLimit
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual pivot map from the middle Hilbert space into the energy dual. -/
def hilbertPivot (j : V →L[ℝ] H) : H →L[ℝ] StrongDual ℝ V :=
  ((ContinuousLinearMap.compL ℝ V H ℝ).flip j).comp (innerSL ℝ)

@[simp] theorem hilbertPivot_apply (j : V →L[ℝ] H) (u : H) (w : V) :
    hilbertPivot j u w = inner ℝ u (j w) := rfl

@[simp] theorem hilbertPivot_value (j : V →L[ℝ] H) (v : V) :
    hilbertPivot j (j v) = hilbertEmbedding j v := rfl

/-- The genuine weak time equation alone produces the closed-time Hilbert trace
    and its energy identity. The approximants are constructed by reflection. -/
theorem hilbert_time_trace_chain (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) {U : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv φ t • hilbertEmbedding j (U t)) =
        -(∫ t in Ioo 0 T, φ t • R t)) :
    ∃ u : ℝ → H, ContinuousOn u (Icc 0 T) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 T), j (U t) = u t) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        ‖u t‖^2-‖u s‖^2 = 2*∫ r in s..t, R r (U r)) := by
  obtain ⟨u,hu,hae,-,hChain⟩ := smooth_approximation_trace_chain j hj hT hU hR
    (fun k => (reflectedSmooth_contDiff hT hU k).of_le (by simp))
    (fun k => (reflectedDualSmooth_contDiff hT hR k).continuous.continuousOn)
    (fun k _ ht => reflectedSmooth_derivative (hilbertEmbedding j) hT hU hR hw k ht)
    (reflectedSmooth_L2_tendsto hT hU) (reflectedDualSmooth_L2_tendsto hT hR)
  exact ⟨u,hu,hae,hChain⟩

/-- The canonical continuous trace has every actual dual increment, including
    both endpoints; its pivot is the original Bochner primitive. -/
theorem hilbert_time_trace_pairings (j : V →L[ℝ] H) (hj : ‖j‖ ≤ 1)
    {T : ℝ} (hT : 0 < T) {U : ℝ → V} {R : ℝ → StrongDual ℝ V}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv φ t • hilbertEmbedding j (U t)) =
        -(∫ t in Ioo 0 T, φ t • R t)) :
    ∃ u : ℝ → H, ContinuousOn u (Icc 0 T) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 T), j (U t) = u t) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        ‖u t‖^2-‖u s‖^2 = 2*∫ r in s..t, R r (U r)) ∧
      ∀ w : V, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        inner ℝ (u t-u s) (j w) = ∫ r in s..t, R r w := by
  obtain ⟨u,hu,hae,hChain⟩ := hilbert_time_trace_chain j hj hT hU hR hw
  have hRL1 := hR.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  obtain ⟨c,hc,hPc⟩ := Yau.L16WeakTimePrimitive.exists_weak_time_primitive hT
    ((hilbertEmbedding j).integrable_comp (hU.integrable (by norm_num))) hRL1 hw
  have hPivotAE : (fun t => hilbertPivot j (u t)) =ᵐ[volume.restrict (Ioo 0 T)]
      (fun t => c+∫ r in (0 : ℝ)..t, R r) := by
    filter_upwards [hae,hc] with t ht hct
    rw [← ht,hilbertPivot_value]
    exact hct
  rw [restrict_Ioo_eq_restrict_Icc] at hPivotAE
  have hPivot := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT) hPivotAE
    ((hilbertPivot j).continuous.comp_continuousOn hu) hPc
  refine ⟨u,hu,hae,hChain,?_⟩
  intro w s hs t ht
  have hRi : IntervalIntegrable R volume s t :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le (f := R) (μ := volume) hT.le).mpr hRL1).mono_set
      (by simpa only [uIcc_of_le hT.le] using uIcc_subset_Icc hs ht)
  calc
    inner ℝ (u t-u s) (j w) = (hilbertPivot j (u t)-hilbertPivot j (u s)) w := by
      simp only [sub_apply,hilbertPivot_apply,inner_sub_left]
    _ = ((c+∫ r in (0 : ℝ)..t, R r)-(c+∫ r in (0 : ℝ)..s, R r)) w := by
      have hPt : hilbertPivot j (u t) = c+∫ r in (0 : ℝ)..t, R r := hPivot ht
      have hPs : hilbertPivot j (u s) = c+∫ r in (0 : ℝ)..s, R r := hPivot hs
      rw [hPt,hPs]
    _ = (∫ r in s..t, R r) w :=
      congrArg (fun L : StrongDual ℝ V => L w)
        (Yau.L16WeakTimePrimitive.primitive_increment hT hRL1 c hs ht)
    _ = ∫ r in s..t, R r w :=
      ((ContinuousLinearMap.apply ℝ ℝ w).intervalIntegral_comp_comm hRi).symm

/-- Scalar time tests retain the two genuine Hilbert endpoint traces. -/
theorem hilbert_trace_pairing_ibp (j : V →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    {u : ℝ → H} {R : ℝ → StrongDual ℝ V}
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hInc : ∀ w : V, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      inner ℝ (u t-u s) (j w) = ∫ r in s..t, R r w)
    (w : V) {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) :
    (∫ t in Ioo 0 T, deriv η t*inner ℝ (u t) (j w)) =
      η T*inner ℝ (u T) (j w)-η 0*inner ℝ (u 0) (j w)-
        ∫ t in Ioo 0 T, η t*R t w := by
  have hScalar (t : ℝ) (ht : t ∈ Icc 0 T) :
      inner ℝ (u t) (j w) = inner ℝ (u 0) (j w)+∫ r in (0 : ℝ)..t, R r w := by
    have h := hInc w 0 ⟨le_rfl,hT.le⟩ t ht
    rw [inner_sub_left] at h
    linarith
  have hL1 := (ContinuousLinearMap.apply ℝ ℝ w).integrable_comp
    (hR.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  have hAE : (fun t => inner ℝ (u t) (j w)) =ᵐ[volume.restrict (Ioo 0 T)]
      (fun t => inner ℝ (u 0) (j w)+∫ r in (0 : ℝ)..t, R r w) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hScalar t (Ioo_subset_Icc_self ht)
  have h := Yau.L16WeakTimePrimitive.weak_scalar_test_ibp hT hL1 _ hAE hη
  change (∫ t in Ioo 0 T, deriv η t*inner ℝ (u t) (j w)) =
    η T*(inner ℝ (u 0) (j w)+∫ r in (0 : ℝ)..T, R r w)-
      η 0*inner ℝ (u 0) (j w)-∫ t in Ioo 0 T, η t*R t w at h
  rw [← hScalar T ⟨hT.le,le_rfl⟩] at h
  exact h

end Yau.LeafProofs.L16LionsTimeTrace
