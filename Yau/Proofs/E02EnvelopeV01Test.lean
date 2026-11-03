import Yau.Proofs.E02EnvelopeBounds
import Yau.Proofs.E02CotangentTensor
import Yau.Proofs.E02CotangentQuadratic

open Matrix Set Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

variable {n : ℕ} (X : KahlerManifold n)

def packedEnvelopeReal (h : Flow X) (T : ℝ) (x : Pt X)
    (q : EuclideanSpace ℝ (Fin (4*n+1))) : ℝ :=
  chartEnvelopeReal X h T x ((envelopeRealCoordinates n).symm q)

/-- At one fixed κ-contact, the genuine translated Peano polynomial
satisfies the original V01 test at its actual attained source. -/
theorem attained_source_V01_test (h : Flow X) (hV : EnvelopeInequality X h)
    (T : ℝ) (x : Pt X)
    (K : Set (EuclideanSpace ℝ (Fin (4*n+1))))
    (hDom : ∀ q ∈ K, (envelopeRealCoordinates n).symm q ∈ envelopeDomain X T x)
    {κ : ℝ} (hκ : 0 < κ) (q : EuclideanSpace ℝ (Fin (4*n+1)))
    (a : ComplexVector n × ComplexVector n × ℝ)
    (ha : envelopeRealCoordinates n a ∈ interior K)
    (hMin : compactInfConvolution K (packedEnvelopeReal X h T x) κ q =
      packedEnvelopeReal X h T x (envelopeRealCoordinates n a)+
        ‖q-envelopeRealCoordinates n a‖^2/(2*κ))
    (p : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hJet : RealSecondJet (compactInfConvolution K (packedEnvelopeReal X h T x) κ) q p A)
    {ε : ℝ} (hε : 0 < ε)
    (hC : (cotangentTensor A-(ε : ℂ) • 1).toBlocks₂₂.PosDef) :
    ∃ L : Herm n, L.PosSemidef ∧
      (L-schurComplement (cotangentTensor A-(ε : ℂ) • 1)).PosSemidef ∧
      (Matrix.trace ((cotangentTensor A-(ε : ℂ) • 1).toBlocks₂₂ᵀ*L)).re ≤
        p (envelopeRealCoordinates n (0,0,1)) := by
  have haDom : a ∈ envelopeDomain X T x := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      hDom (envelopeRealCoordinates n a) (interior_subset ha)
  have hv0 : ∀ y ∈ K, 0 ≤ packedEnvelopeReal X h T x y := by
    intro y hy
    exact (chartEnvelopeReal_finite_bounds X h T x _ (hDom y hy)).2.2.2.1
  let c := packedEnvelopeReal X h T x (envelopeRealCoordinates n a)
  let φ := envelopeLowerPolynomial c a p A ε
  have hLower := envelopeLowerPolynomial_source_test K (packedEnvelopeReal X h T x)
    hv0 hκ q a ha hMin p A hJet hε
  have hAt : (φ a : EReal) = envelopeChart h T x a := by
    rw [show φ a = c from hLower.1]
    change (chartEnvelopeReal X h T x ((envelopeRealCoordinates n).symm
      (envelopeRealCoordinates n a)) : EReal) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (chartEnvelopeReal_finite_bounds X h T x a haDom).2.2.1
  have hNear : ∀ᶠ y in 𝓝 a, (φ y : EReal) ≤ envelopeChart h T x y := by
    filter_upwards [hLower.2,(isOpen_envelopeDomain X T x).mem_nhds haDom] with y hy hyDom
    rw [←(chartEnvelopeReal_finite_bounds X h T x y hyDom).2.2.1]
    apply EReal.coe_le_coe_iff.mpr
    simpa only [φ,c,packedEnvelopeReal,ContinuousLinearEquiv.symm_apply_apply] using hy
  have hLevi := envelopeLowerPolynomial_levi_sub_epsilon c a p A hJet.1 ε
  change leviMatrix (fun y => φ (y.1,y.2,a.2.2)) (a.1,a.2.1) cotangentDir =
    cotangentTensor A-(ε : ℂ) • 1 at hLevi
  have hSmooth : ContDiffAt ℝ ∞ φ a := (envelopeLowerPolynomial_contDiff c a p A ε).contDiffAt
  have hOut := hV T (haDom.2.1.trans haDom.2.2) x a.1 a.2.1 a.2.2
    haDom.1 haDom.2.1 haDom.2.2 φ hSmooth hAt hNear
  dsimp only at hOut
  rw [hLevi] at hOut
  have hOut' := hOut hC
  rw [envelopeLowerPolynomial_time_deriv c a p A hJet.1 ε] at hOut'
  exact hOut'

end Yau.NodeProofs.E02Aux
