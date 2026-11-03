import Yau.Proofs.V02WallTaylorHadamard
import Yau.Proofs.V02WallTaylorFactors

/-! The set on which every point of a real segment stays in an open domain
is open. This gives uniform small smooth divided differences on compact data. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof

variable {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]

theorem isOpen_compact_section {W : Set (P × Q)} (hW : IsOpen W)
    {J : Set Q} (hJ : IsCompact J) : IsOpen {p : P | ∀ s ∈ J, (p, s) ∈ W} := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  have hh : ({p} : Set P) ×ˢ J ⊆ W := by
    rintro ⟨p', s⟩ ⟨hp', hs⟩
    rcases Set.mem_singleton_iff.mp hp' with rfl
    exact hp s hs
  obtain ⟨A, B, hA, _, hpA, hJB, hAB⟩ :=
    generalized_tube_lemma isCompact_singleton hJ hW hh
  refine ⟨A, ?_, hA, hpA (by simp)⟩
  intro p' hp' s hs
  exact hAB (show (p', s) ∈ A ×ˢ B from ⟨hp', hJB hs⟩)

variable {E T : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

def hadamardSegmentDomain (Ω : Set (E × T)) (D : Set E) (m : E → ℝ) (A : E → T) : Set E :=
  {p | p ∈ D ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, (p, s • (m p • A p)) ∈ Ω}

theorem isOpen_hadamardSegmentDomain {Ω : Set (E × T)} (hΩ : IsOpen Ω)
    {D : Set E} (hD : IsOpen D) {m : E → ℝ} (hm : ContinuousOn m D)
    {A : E → T} (hA : ContinuousOn A D) :
    IsOpen (hadamardSegmentDomain Ω D m A) := by
  let W : Set (E × ℝ) := (D ×ˢ Set.univ) ∩
    (fun w : E × ℝ => (w.1, w.2 • (m w.1 • A w.1))) ⁻¹' Ω
  have hm' : ContinuousOn (fun w : E × ℝ => m w.1) (D ×ˢ Set.univ) :=
    hm.comp continuous_fst.continuousOn (fun w hw => hw.1)
  have hA' : ContinuousOn (fun w : E × ℝ => A w.1) (D ×ˢ Set.univ) :=
    hA.comp continuous_fst.continuousOn (fun w hw => hw.1)
  have hW : IsOpen W := (continuousOn_fst.prodMk
    (continuousOn_snd.smul (hm'.smul hA'))).isOpen_inter_preimage (hD.prod isOpen_univ) hΩ
  have heq : hadamardSegmentDomain Ω D m A = {p | ∀ s ∈ Set.Icc (0 : ℝ) 1, (p, s) ∈ W} := by
    ext p
    constructor
    · rintro ⟨hp, hseg⟩ s hs
      exact ⟨⟨hp, Set.mem_univ _⟩, hseg s hs⟩
    · intro hh
      exact ⟨(hh 0 (by simp)).1.1, fun s hs => (hh s hs).2⟩
  rw [heq]
  exact isOpen_compact_section hW isCompact_Icc

theorem scaledHadamardFactor_contDiffOn_segmentDomain {Ω : Set (E × T)} (hΩ : IsOpen Ω)
    {F : E × T → ℝ} (hF : ContDiffOn ℝ ∞ F Ω)
    {D : Set E} (hD : IsOpen D) {m : E → ℝ} (hm : ContDiffOn ℝ ∞ m D)
    {A : E → T} (hA : ContDiffOn ℝ ∞ A D) :
    ContDiffOn ℝ ∞ (scaledHadamardFactor F m A) (hadamardSegmentDomain Ω D m A) :=
  scaledHadamardFactor_contDiffOn hΩ hF
    (isOpen_hadamardSegmentDomain hΩ hD hm.continuousOn hA.continuousOn)
    (hm.mono (fun _ hp => hp.1)) (hA.mono (fun _ hp => hp.1)) (fun _ hp => hp.2)


/-- One common radius for the genuine derivative integral and its exact
vanishing-factor identity, chosen before any boundary trace. -/
theorem exists_uniform_scaledHadamardFactor {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : Set ((ℂ × P) × T)} (hΩ : IsOpen Ω)
    {F : (ℂ × P) × T → ℝ} (hF : ContDiffOn ℝ ∞ F Ω)
    {D : Set (ℂ × P)} (hD : IsOpen D)
    {m : ℂ × P → ℝ} (hm : ContDiffOn ℝ ∞ m D)
    {A : ℂ × P → T} (hA : ContDiffOn ℝ ∞ A D)
    {K : Set P} (hK : IsCompact K)
    (hzero : ∀ p ∈ K, (0, p) ∈ D ∧ A (0, p) = 0 ∧ ((0, p), 0) ∈ Ω)
    {S : ℝ} (hS : 0 < S) :
    ∃ r : ℝ, 0 < r ∧ r < S ∧ ∀ z ∈ Metric.ball 0 r, ∀ p ∈ K,
      (z, p) ∈ hadamardSegmentDomain Ω D m A ∧
      |scaledHadamardFactor F m A (z, p)| < 1 / 2 ∧
      F ((z, p), m (z, p) • A (z, p)) - F ((z, p), 0) =
        m (z, p) * scaledHadamardFactor F m A (z, p) := by
  let U := hadamardSegmentDomain Ω D m A
  have hU : IsOpen U := isOpen_hadamardSegmentDomain hΩ hD hm.continuousOn hA.continuousOn
  have hfactor := scaledHadamardFactor_contDiffOn_segmentDomain hΩ hF hD hm hA
  have h0 : ∀ p ∈ K, (0, p) ∈ U ∧ scaledHadamardFactor F m A (0, p) = 0 := by
    intro p hp
    rcases hzero p hp with ⟨hpD, hpA, hpΩ⟩
    refine ⟨⟨hpD, ?_⟩, scaledHadamardFactor_zero hpA⟩
    intro s hs
    simpa only [hpA, smul_zero] using hpΩ
  obtain ⟨r, hr, hrS, hbound⟩ := exists_uniform_small_factor hK hU hfactor.continuousOn h0 hS
  refine ⟨r, hr, hrS, fun z hz p hp => ?_⟩
  have hh := hbound z hz p hp
  exact ⟨hh.1, hh.2, scaledHadamardFactor_identity hΩ hF hh.1.2⟩

end Yau.Blueprint.V02WallTaylorProof
