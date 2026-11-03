import Yau.Proofs.F05BootstrapLocalJets
import Yau.Proofs.F05BootstrapCutoffZeroJets

/-! Zero extension across an artificial chart edge preserves relative C2
regularity on the same physical set. The actual plane is retained throughout. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_cutoff_extension {H X V : Set (Space n)} {I : Set ℝ}
    (hH : UniqueDiffOn ℝ H) (hX : UniqueDiffOn ℝ X) (hV : IsOpen V)
    (hVX : H ∩ V ⊆ X) {φ : Space n → ℝ} (hSupport : tsupport φ ⊆ V)
    {u : Point n → ℝ} (hu : F05RelC2 X I (fun z => φ z.1*u z)) :
    F05RelC2 H I (fun z => φ z.1*u z) := by
  let w : Point n → ℝ := fun z => φ z.1*u z
  let Q := H ×ˢ I
  let QV := (H ∩ V) ×ˢ I
  have hSub : QV ⊆ X ×ˢ I := fun z hz => ⟨hVX hz.1,hz.2⟩
  have hLocal (z : Point n) (hz : z ∈ QV) :=
    F05_relative_local_domain_jets hH hX hV hVX hu hz
  have hZeros (z : Point n) (hz : z.1 ∉ tsupport φ) :=
    F05_relative_cutoff_zero_jets H I φ u hz
  have hPatch {E : Type} [NormedAddCommGroup E] (F : Point n → E)
      (hSmall : ContinuousOn F QV) (hZero : ∀ z, z.1 ∉ tsupport φ → F z = 0) :
      ContinuousOn F Q := by
    intro z hz
    by_cases hzSupport : z.1 ∈ tsupport φ
    · have hzV := hSupport hzSupport
      apply (hSmall z ⟨⟨hz.1,hzV⟩,hz.2⟩).mono_of_mem_nhdsWithin
      have hNear : ∀ᶠ q : Point n in 𝓝 z, q.1 ∈ V :=
        (hV.preimage continuous_fst).mem_nhds hzV
      filter_upwards [self_mem_nhdsWithin,hNear.filter_mono nhdsWithin_le_nhds] with q hq hqV
      exact ⟨⟨hq.1,hqV⟩,hq.2⟩
    · have hNear : ∀ᶠ q : Point n in 𝓝 z, q.1 ∉ tsupport φ :=
        ((isClosed_tsupport φ).isOpen_compl.preimage continuous_fst).mem_nhds hzSupport
      apply (continuousWithinAt_const (b := (0 : E))).congr_of_eventuallyEq _ (hZero z hzSupport)
      filter_upwards [hNear.filter_mono nhdsWithin_le_nhds] with q hq
      exact hZero q hq
  have hD : ContinuousOn (F05RelD H w) QV :=
    (hu.2.1.mono hSub).congr (fun z hz => (hLocal z hz).1)
  have hDD : ContinuousOn (F05RelDD H w) QV :=
    (hu.2.2.1.mono hSub).congr (fun z hz => (hLocal z hz).2)
  refine ⟨hPatch w (hu.1.mono hSub) (fun z hz => (hZeros z hz).1),
    hPatch (F05RelD H w) hD (fun z hz => (hZeros z hz).2.1),
    hPatch (F05RelDD H w) hDD (fun z hz => (hZeros z hz).2.2.1),
    hPatch (F05RelT I w) (hu.2.2.2.1.mono hSub) (fun z hz => (hZeros z hz).2.2.2),?_,?_⟩
  · intro t ht x hx
    by_cases hxSupport : x ∈ tsupport φ
    · have hxV := hSupport hxSupport
      apply (hu.2.2.2.2.1 t ht x (hVX ⟨hx,hxV⟩)).mono_of_mem_nhdsWithin
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV)] with y hyH hyV
      exact hVX ⟨hyH,hyV⟩
    · have hSlice : (fun y => w (y,t)) =ᶠ[𝓝 x] (fun _ : Space n => (0 : ℝ)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxSupport] with y hy
        simp only [Pi.zero_apply] at hy
        change φ y*u (y,t) = 0
        rw [hy,zero_mul]
      exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hSlice).contDiffWithinAt
  · intro z hz
    by_cases hzSupport : z.1 ∈ tsupport φ
    · exact hu.2.2.2.2.2 z ⟨hVX ⟨hz.1,hSupport hzSupport⟩,hz.2⟩
    · have hφ : φ z.1 = 0 := image_eq_zero_of_notMem_tsupport hzSupport
      have hSlice : (fun t => w (z.1,t)) = fun _ : ℝ => (0 : ℝ) := by
        funext t
        change φ z.1*u (z.1,t) = 0
        rw [hφ,zero_mul]
      rw [hSlice]
      exact differentiableWithinAt_const 0

end Yau.Proofs.F05Aux
