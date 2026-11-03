import Yau.Proofs.V01ContactCylinder

/-! The strict cylinder is built from the original chart, physical time,
actual flow and pointwise smooth lower test in EnvelopeInequality. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Manifold
namespace Yau.Blueprint.V01Proof
variable {n : ℕ}

theorem original_contact_cylinder
    (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (η : ComplexVector n)
    (s : ℝ) (hs : s ∈ Ioo 0 T)
    (φ : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (hφ : ContDiffAt ℝ ∞ φ (z, η, s))
    (hφeq : (φ (z, η, s) : EReal) = envelopeChart h T x (z, η, s))
    (hφle : ∀ᶠ p in 𝓝 (z, η, s), (φ p : EReal) ≤ envelopeChart h T x p)
    {α : ℝ} (hα : 0 < α) :
    ∃ (r : ℝ) (V : Set (CotangentCoord n × ℝ)), 0 < r ∧ IsOpen V ∧
      let K := closedBall (z, η) r ×ˢ Icc (s - r) (s + r)
      IsCompact K ∧ ((z, η), s) ∈ interior K ∧ K ⊆ V ∧
      V ⊆ cotangentTarget x ×ˢ Ioo 0 T ∧
      ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
        canonicalQuadraticSupport φ (z, η, s) α (contactAssoc p)) V ∧
      (∀ p ∈ K, (canonicalQuadraticSupport φ (z, η, s) α (contactAssoc p) : EReal) ≤
        envelopeChart h T x (contactAssoc p)) ∧
      (∀ p ∈ K, (canonicalQuadraticSupport φ (z, η, s) α (contactAssoc p) : EReal) =
        envelopeChart h T x (contactAssoc p) ↔ p = ((z, η), s)) ∧
      ∃ gap : ℝ, 0 < gap ∧ ∀ p ∈ frontier K,
        ((canonicalQuadraticSupport φ (z, η, s) α (contactAssoc p) + gap : ℝ) : EReal) ≤
          envelopeChart h T x (contactAssoc p) := by
  have hTarget : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target x).prod isOpen_univ
  have hD : cotangentTarget x ×ˢ Ioo 0 T ∈ 𝓝 ((z, η), s) :=
    (hTarget.prod isOpen_Ioo).mem_nhds ⟨⟨hz, mem_univ η⟩, hs⟩
  exact exists_strict_quadratic_cylinder (z, η, s)
    (hφ.of_le (by norm_num)) hφeq hφle _ hD hα

end Yau.Blueprint.V01Proof
