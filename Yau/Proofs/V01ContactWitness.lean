import Yau.Proofs.V01VariationSetup
import Yau.Proofs.V01EnlargedSupport
import Yau.Proofs.V01OuterLimit

/-! The quadratic penalty is removed only after the complete inner witness
has been obtained for each fixed positive penalty. -/

noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff Matrix ComplexOrder MatrixOrder
namespace Yau.Blueprint.V01Proof
variable {n : ℕ} {X : KahlerManifold n}

theorem original_contact_schur_witness
    (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hComp : ScalarComparison X h ρ)
    (hP03 : FiniteInterpolation X) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (hSchur : SymplecticSchur n) (hD05 : DiscFramesContract X.manifold)
    (hV02 : V02Contract X) (hV03 : V03Contract X) (hV04 : V04Contract X)
    (T : ℝ) (hT : 0 < T) (x : Pt X)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (η : ComplexVector n)
    (s : ℝ) (hs : s ∈ Ioo 0 T)
    (φ : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (hφ : ContDiffAt ℝ ∞ φ (z, η, s))
    (hφeq : (φ (z, η, s) : EReal) = envelopeChart h T x (z, η, s))
    (hφle : ∀ᶠ p in 𝓝 (z, η, s), (φ p : EReal) ≤ envelopeChart h T x p)
    (hC : (leviMatrix (fun q : CotangentCoord n => φ (q.1, q.2, s))
      (z, η) cotangentDir).toBlocks₂₂.PosDef) :
    let W := leviMatrix (fun q : CotangentCoord n => φ (q.1, q.2, s)) (z, η) cotangentDir
    ∃ K : Herm n, K.PosSemidef ∧ (K - schurComplement W).PosSemidef ∧
      (W.toBlocks₂₂ᵀ * K).trace.re ≤ deriv (fun s' => φ (z, η, s')) s := by
  let W : CotangentMatrix n :=
    leviMatrix (fun q : CotangentCoord n => φ (q.1, q.2, s)) (z, η) cotangentDir
  have hφ₂ : ContDiffAt ℝ 2 φ (z, η, s) := hφ.of_le (by norm_num)
  have hSlice : ContDiffAt ℝ 2 (fun q : CotangentCoord n => φ (q.1, q.2, s)) (z, η) :=
    hφ₂.comp (z, η) ((spatialAffine_contDiff s).contDiffAt.of_le (by norm_num))
  have hW : W.IsHermitian := Yau.Blueprint.V03Proof.leviMatrix_isHermitian hSlice cotangentDir
  apply closed_schur_witness_of_shifted_witnesses W _ hW hC
  intro α hα hCα
  obtain ⟨q, d, hd, _hh, _hTime, hChart, hTest, hPoint⟩ :=
    exists_original_variation_setup o h U P ρ hloc hComp hP03 u hu T hT x z hz η s hs
      φ hφ hφeq hφle α hα
  have hTestd : d.test = chartTest d.chart (canonicalQuadraticSupport φ (z, η, s) α) := by
    rw [hChart]
    exact hTest
  exact schur_witness_of_variation_setup hSchur hD05 hV02 hV03 hV04 d hd
    (z, η, s) hφ₂ α hα hTestd hPoint hCα

end Yau.Blueprint.V01Proof
