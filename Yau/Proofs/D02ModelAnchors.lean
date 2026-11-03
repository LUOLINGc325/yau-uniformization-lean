import Yau.Proofs.D02MovingAnchors
import Yau.Proofs.B01Volume

/-! The same measurable moving anchors in the exact one-dimensional model
and Lebesgue measure used by the original D04 compactness theorem. -/

open scoped ENNReal
open MeasureTheory Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

def modelAnchorCompact : Set (ComplexVector 1) :=
  Yau.Proofs.B01Aux.complexOneEquiv ''
    {z : ℂ | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 4}

theorem modelAnchorCompact_isCompact : IsCompact modelAnchorCompact :=
  anchorCompactAnnulus_isCompact.image Yau.Proofs.B01Aux.complexOneEquiv.continuous

theorem modelAnchorCompact_subset_disc : modelAnchorCompact ⊆ Metric.ball (0 : ComplexVector 1) 1 := by
  rintro w ⟨z, hz, rfl⟩
  simp only [Metric.mem_ball, dist_zero_right, Yau.Proofs.B01Aux.complexOneEquiv.norm_map]
  exact hz.2.trans_lt (by norm_num : (3 / 4 : ℝ) < 1)

theorem complexOneEquiv_measure_image {S : Set ℂ} (hS : MeasurableSet S) :
    MeasurableSet (Yau.Proofs.B01Aux.complexOneEquiv '' S) ∧
      lebesgueC 1 (Yau.Proofs.B01Aux.complexOneEquiv '' S) = volume S := by
  let e := Yau.Proofs.B01Aux.complexOneEquiv
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hm := he.measurableSet_image' hS
  refine ⟨hm, ?_⟩
  rw [lebesgueC_eq_volume]
  have hmeasure := Yau.Proofs.B01Aux.complexOneEquiv_measurePreserving.measure_preimage
    hm.nullMeasurableSet
  rw [e.injective.preimage_image] at hmeasure
  exact hmeasure.symm

def modelMovingAnchors {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (f : ℂ → M.Carrier) (A : ℝ) : Set (ComplexVector 1) :=
  Yau.Proofs.B01Aux.complexOneEquiv '' anchorAnnulus (goodAngles (discEnergyDensity g f) A)

theorem uniform_modelMovingAnchors {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {K : Set (Pt X)} (hK : IsCompact K) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℂ → Pt X, IsHolomorphicDisc f →
      (∀ z : ℂ, ‖z‖ = 1 → f z ∈ K) →
      discArea X.metric.form f ≤ ENNReal.ofReal A →
      MeasurableSet (modelMovingAnchors X.metric.form f A) ∧
        modelMovingAnchors X.metric.form f A ⊆
          modelAnchorCompact ∩ Metric.ball (0 : ComplexVector 1) 1 ∧
        ENNReal.ofReal (5 * Real.pi / 32) ≤ lebesgueC 1 (modelMovingAnchors X.metric.form f A) ∧
        ∀ w ∈ modelMovingAnchors X.metric.form f A,
          ((-C : ℝ) : EReal) ≤ (immersionPotential X.metric.form F (discModelMap f w) : EReal) := by
  obtain ⟨K₁, C, hK₁, hC, hanchors⟩ := uniform_movingAnchor_potential X hF hImm hK A
  refine ⟨C, hC, fun f hf hb harea => ?_⟩
  obtain ⟨hS, hvol, hsub, hlow⟩ := hanchors f hf hb harea
  obtain ⟨hmodel, hmeasure⟩ := complexOneEquiv_measure_image hS
  refine ⟨hmodel, ?_, ?_, ?_⟩
  · intro w hw
    have hKmodel : w ∈ modelAnchorCompact := image_mono hsub hw
    exact ⟨hKmodel, modelAnchorCompact_subset_disc hKmodel⟩
  · change _ ≤ lebesgueC 1 (Yau.Proofs.B01Aux.complexOneEquiv '' _)
    rw [hmeasure]
    exact hvol
  · rintro w ⟨z, hz, rfl⟩
    change ((-C : ℝ) : EReal) ≤
      (immersionPotential X.metric.form F
        (f (Yau.Proofs.B01Aux.complexOneEquiv.symm (Yau.Proofs.B01Aux.complexOneEquiv z))) : EReal)
    rw [Yau.Proofs.B01Aux.complexOneEquiv.symm_apply_apply]
    exact_mod_cast (hlow z hz).2

end Yau.NodeProofs.D02Aux
