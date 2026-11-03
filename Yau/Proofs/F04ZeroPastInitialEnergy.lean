import Yau.Proofs.F04LocalInitialEnergy
import Yau.Proofs.F04CompactWeakFields
import Yau.Proofs.F04ZeroPastLocalEnergy
import Yau.Proofs.F04ZeroPastEquation

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- A classical homogeneous solution with the original local O(t) initial
 bound gives actual weak energy and the actual homogeneous weak equation
 across the initial face. Flux and drift integrability are outputs here. -/
theorem classical_homogeneous_zeroPast_initial_energy {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) {S lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hEll : Elliptic (O ×ˢ Icc 0 S) a lam upper)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo 0 S))
    (hEq : ∀ p ∈ O ×ˢ Ioo 0 S, linearOp (O ×ˢ Icc 0 S) a b u p = 0)
    (hGrowth : ∀ W : Set (Space n), IsOpen W → IsCompact (closure W) → closure W ⊆ O →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ W, ∀ t ∈ Ioo 0 S, |u (x, t)| ≤ K * t)
    (V : Set (Space n)) (s : ℝ) (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVO : closure V ⊆ O) (hs : 0 < s) (hsS : s < S) :
    LocalEnergy V (Ioo (-s) s) (zeroPast u) (fun p i => zeroPast (fun q => dgGradient u q i) p) ∧
      WeakEquation V (Ioo (-s) s) a b (fun _ => 0) (zeroPast u)
        (fun p i => zeroPast (fun q => dgGradient u q i) p) := by
  obtain ⟨hGrad, hU, hG, _hSlice, _hTrace, hWeak⟩ :=
    local_initial_energy hO hSmooth hEll hu hEq hGrowth V s hV hVC hVO hs hsS
  obtain ⟨hFlux, hDrift⟩ := compact_buffer_weak_fields_memLp hO hV hVC hVO hs hsS.le hSmooth hG
  obtain ⟨K, hK, hKb⟩ := hGrowth V hV hVC hVO
  have hKb' : ∀ p ∈ V ×ˢ Ioo 0 s, |u p| ≤ K * p.2 := fun p hp =>
    hKb p.1 hp.1 p.2 ⟨hp.2.1, hp.2.2.trans hsS⟩
  exact ⟨zeroPast_localEnergy hV.measurableSet (neg_nonpos.mpr hs.le) hU hG hGrad,
    zeroPast_homogeneous_weakEquation hV.measurableSet (neg_nonpos.mpr hs.le) hK
      hU hFlux hDrift hKb' hWeak⟩

end Yau.F04Proof
