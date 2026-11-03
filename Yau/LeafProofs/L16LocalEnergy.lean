import Yau.LeafProofs.L16LocalRepresentative
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem compact_subset_relcompact_cylinder {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {K : Set (Point n)} (hK : IsCompact K) (hKQ : K ⊆ O ×ˢ Set.Ioo l r) :
    ∃ (V : Set (Space n)) (c e : ℝ), IsOpen V ∧ IsCompact (closure V) ∧
      closure V ⊆ O ∧ Set.Icc c e ⊆ Set.Ioo l r ∧ K ⊆ V ×ˢ Set.Ioo c e := by
  obtain ⟨V,hV,hKV,hVO,hVC⟩ := exists_open_between_and_isCompact_closure
    (hK.image continuous_fst) hO (by rintro _ ⟨p,hp,rfl⟩; exact (hKQ hp).1)
  obtain ⟨c₀,hc₀,hcK⟩ := hK.exists_forall_le' continuous_snd.continuousOn
    (fun p hp => (hKQ hp).2.1)
  obtain ⟨e₀,he₀,heK⟩ := hK.exists_forall_le' continuous_snd.neg.continuousOn
    (a := -r) (fun p hp => by simpa using neg_lt_neg (hKQ hp).2.2)
  refine ⟨V,(l+c₀)/2,(r-e₀)/2,hV,hVC,hVO,?_,?_⟩
  · intro t ht
    constructor <;> linarith [ht.1,ht.2]
  · intro p hp
    refine ⟨hKV (Set.mem_image_of_mem Prod.fst hp),?_,?_⟩
    · have := hcK p hp
      linarith
    · have hBound : e₀ ≤ -p.2 := heK p hp
      linarith

theorem localEnergy_memLp_on_compact {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G)
    {K : Set (Point n)} (hK : IsCompact K) (hKQ : K ⊆ O ×ˢ Set.Ioo l r) :
    MemLp u 2 (volume.restrict K) ∧
      ∀ i, MemLp (fun p => G p i) 2 (volume.restrict K) := by
  obtain ⟨V,c,e,hV,hVC,hVO,hI,hCover⟩ := compact_subset_relcompact_cylinder hO hK hKQ
  obtain ⟨hu,hG⟩ := hE.2 V c e hV hVC hVO hI
  rw [productVolume_eq_restrict] at hu hG
  exact ⟨hu.mono_measure (Measure.restrict_mono hCover le_rfl),
    fun i => (hG i).mono_measure (Measure.restrict_mono hCover le_rfl)⟩

theorem localEnergy_cutoff_memLp {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G) {η : Point n → ℝ}
    (hη : Continuous η) (hSupport : HasCompactSupport η)
    (hSub : tsupport η ⊆ O ×ˢ Set.Ioo l r) :
    MemLp (fun p => η p * u p) 2 volume ∧
      ∀ i, MemLp (fun p => η p * G p i) 2 volume := by
  obtain ⟨hu,hG⟩ := localEnergy_memLp_on_compact hO hE hSupport hSub
  have hηTop : MemLp η (⊤ : ENNReal) (volume.restrict (tsupport η)) :=
    hη.memLp_top_of_hasCompactSupport hSupport _
  have hLift (z : Point n → ℝ) (hz : MemLp z 2 (volume.restrict (tsupport η))) :
      MemLp (fun p => η p*z p) 2 volume := by
    have hProd : MemLp (fun p => η p*z p) 2 (volume.restrict (tsupport η)) := hηTop.mul hz
    have hInd := (memLp_indicator_iff_restrict (isClosed_tsupport η).measurableSet.nullMeasurableSet).2 hProd
    convert! hInd using 1
    ext p
    by_cases hp : p ∈ tsupport η
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, image_eq_zero_of_notMem_tsupport hp, zero_mul]
  exact ⟨hLift u hu,fun i => hLift (fun p => G p i) (hG i)⟩

theorem localEnergy_cutoff_integrable {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G) {η : Point n → ℝ}
    (hη : Continuous η) (hSupport : HasCompactSupport η)
    (hSub : tsupport η ⊆ O ×ˢ Set.Ioo l r) :
    Integrable (fun p => η p * u p) volume ∧
      ∀ i, Integrable (fun p => η p * G p i) volume := by
  obtain ⟨hu,hG⟩ := localEnergy_memLp_on_compact hO hE hSupport hSub
  have hηTwo : MemLp η 2 (volume.restrict (tsupport η)) :=
    hη.memLp_of_hasCompactSupport hSupport
  have hLift (z : Point n → ℝ) (hz : MemLp z 2 (volume.restrict (tsupport η))) :
      Integrable (fun p => η p*z p) volume := by
    have hProd : Integrable (fun p => η p*z p) (volume.restrict (tsupport η)) :=
      hηTwo.integrable_mul hz
    have hInd := (integrable_indicator_iff (isClosed_tsupport η).measurableSet).2 hProd
    convert! hInd using 1
    ext p
    by_cases hp : p ∈ tsupport η
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp,image_eq_zero_of_notMem_tsupport hp,zero_mul]
  exact ⟨hLift u hu,fun i => hLift (fun p => G p i) (hG i)⟩

end Yau.LeafProofs.L16Aux
