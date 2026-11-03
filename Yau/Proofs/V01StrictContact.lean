import Yau.Proofs.V01OriginalContact
import Yau.Proofs.V01ChartTest

/-! Every clause of the original strict-contact predicate is obtained from
its actual lower test, in the same given chart and physical clock. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Manifold
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

def strictContactData (d : VariationData X q) (x : Pt X) (T : ℝ)
    (a : ComplexVector n × ComplexVector n × ℝ) (r : ℝ)
    (ψ : ComplexVector n × ComplexVector n × ℝ → ℝ) : VariationData X q :=
  {d with
    T := T
    chart := x
    cylinderCenter := (a.1, a.2.1)
    cylinderRadius := r
    cylinderTimeLo := a.2.2 - r
    cylinderTimeHi := a.2.2 + r
    contact := ((a.1, a.2.1), a.2.2)
    test := chartTest x ψ}

theorem exists_original_strict_contact
    (d : VariationData X q) (T : ℝ) (x : Pt X)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (η : ComplexVector n)
    (s : ℝ) (hs : s ∈ Ioo 0 T)
    (φ : ComplexVector n × ComplexVector n × ℝ → ℝ)
    (hφ : ContDiffAt ℝ ∞ φ (z, η, s))
    (hφeq : (φ (z, η, s) : EReal) = envelopeChart d.h T x (z, η, s))
    (hφle : ∀ᶠ p in 𝓝 (z, η, s), (φ p : EReal) ≤ envelopeChart d.h T x p)
    {α : ℝ} (hα : 0 < α) :
    ∃ r : ℝ, 0 < r ∧ StrictEnvelopeContact
      (strictContactData d x T (z, η, s) r (canonicalQuadraticSupport φ (z, η, s) α)) := by
  let ψ := canonicalQuadraticSupport φ (z, η, s) α
  obtain ⟨r, V, hr, hV, hK, hInterior, hKV, hVD, _hSmooth, hLe, hEq, gap, hgap, hGap⟩ :=
    original_contact_cylinder X d.h T x z hz η s hs φ hφ hφeq hφle hα
  let K := closedBall (z, η) r ×ˢ Icc (s - r) (s + r)
  have hKD : K ⊆ cotangentTarget x ×ˢ Ioo 0 T := hKV.trans hVD
  refine ⟨r, hr, ?_⟩
  dsimp only [StrictEnvelopeContact, centerCylinder, strictContactData]
  refine ⟨hK, hInterior, hKD, ?_, ?_, ?_, V, hV, hKV, hVD, ?_⟩
  · intro p hp
    rw [chartTest_chartInv x ψ (hKD hp).1 p.2]
    exact hLe p hp
  · intro p hp
    rw [chartTest_chartInv x ψ (hKD hp).1 p.2]
    exact hEq p hp
  · refine ⟨gap, hgap, ?_⟩
    intro p hp
    have hpK : p ∈ K := hK.isClosed.frontier_subset hp
    rw [chartTest_chartInv x ψ (hKD hpK).1 p.2]
    exact hGap p hp
  · exact chartTest_contDiffOn x (canonicalQuadraticSupport_contDiff φ (z, η, s) α)
      (fun p hp => ⟨(hVD hp).1, mem_univ _⟩)

end Yau.Blueprint.V01Proof
