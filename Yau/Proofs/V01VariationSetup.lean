import Yau.Proofs.V01LocalizationData
import Yau.Proofs.V01ScalarData
import Yau.Proofs.V01CotangentSetup
import Yau.Proofs.V01StrictContact
import Yau.Proofs.D02CotangentBox

/-! The full original setup is constructed, including actual metric-box
compactness, obtained from the certified native metric-box theorem. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.Blueprint.V01Proof
variable {n : ℕ} {X : KahlerManifold n}

theorem exists_original_variation_setup
    (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hComp : ScalarComparison X h ρ)
    (hP03 : FiniteInterpolation X) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (T : ℝ) (hT : 0 < T) (x : Pt X)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (η : ComplexVector n)
    (s : ℝ) (hs : s ∈ Ioo 0 T)
    (φ : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (hφ : ContDiffAt ℝ ∞ φ (z, η, s))
    (hφeq : (φ (z, η, s) : EReal) = envelopeChart h T x (z, η, s))
    (hφle : ∀ᶠ p in 𝓝 (z, η, s), (φ p : EReal) ≤ envelopeChart h T x p)
    (α : ℝ) (hα : 0 < α) :
    ∃ (q : ℕ) (d : VariationData X q), VariationSetup d ∧
      d.h = h ∧ d.T = T ∧ d.chart = x ∧
      d.test = chartTest x (canonicalQuadraticSupport φ (z, η, s) α) ∧
      contactAssoc d.contact = (z, η, s) := by
  obtain ⟨q, G, hG, hSpan⟩ := cotangent_setup_of_finiteInterpolation X hP03
  obtain ⟨Q, ρs, A, hQSmooth, hQ, hTail, hSmall, hAMono, hATop, hA⟩ :=
    exists_scalar_localization_data o h U P ρ hloc hComp u hu T hT
  let d₀ := localizationData o h U P ρ Q ρs u A G T x z η s
  obtain ⟨r, _hr, hContact⟩ :=
    exists_original_strict_contact d₀ T x z hz η s hs φ hφ hφeq hφle hα
  let d := strictContactData d₀ x T (z, η, s) r (canonicalQuadraticSupport φ (z, η, s) α)
  refine ⟨q, d, ?_, rfl, rfl, rfl, rfl, rfl⟩
  have hProfiles : WallProfiles d := wallProfiles_actual d
  refine ⟨hT, ?_, ⟨hloc, hComp⟩, hu, hG, hSpan, hProfiles, hContact,
    ⟨hQSmooth, hQ⟩, hTail, hSmall, hAMono, hATop, ?_⟩
  · change T < T + 1
    linarith
  · intro j
    refine ⟨(hA j).1, le_rfl, ?_, ?_⟩
    · change CotangentCompact {y : CotangentPoint X.manifold |
        u y.1 ≤ A j ∧ dualNorm (h 0) y.1 y.2 ≤ ((j : ℝ) + 1) ^ 2}
      rw [hloc.1.1]
      exact Yau.NodeProofs.D02Aux.cotangentBoxCompact n X.manifold X.metric.form
        (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)
        {x | u x ≤ A j} (((j : ℝ) + 1) ^ 2) (hu.2.1 (A j))
    · dsimp only [d, d₀, strictContactData, localizationData, baseCost]
      simpa only [Nat.cast_add, Nat.cast_one] using (hA j).2

end Yau.Blueprint.V01Proof
