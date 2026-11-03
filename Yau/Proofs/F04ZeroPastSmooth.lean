import Yau.Proofs.F04ZeroPastContinuity
import Yau.Proofs.F04ZeroPastInitialEnergy
import Yau.LeafProofs.L16InteriorSmoothing

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- Native weak smoothing applies to the proved zero-past energy/equation.
 Continuity identifies its representative with the actual zero-past function. -/
theorem zeroPast_smooth_of_energy {n : ℕ} (hn : 0 < n)
    {O : Set (Space n)} (hO : IsOpen O) {s lam upper K : ℝ} (hs : 0 < s) (hK : 0 ≤ K)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Ioo (-s) s) a b)
    (hEll : Elliptic (O ×ˢ Ioo (-s) s) a lam upper)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hu : ContinuousOn u (O ×ˢ Ioo 0 s))
    (hGrowth : ∀ p ∈ O ×ˢ Ioo 0 s, |u p| ≤ K * p.2)
    (hE : LocalEnergy O (Ioo (-s) s) (zeroPast u) G)
    (hEq : WeakEquation O (Ioo (-s) s) a b (fun _ => 0) (zeroPast u) G) :
    ContDiffOn ℝ ∞ (zeroPast u) (O ×ˢ Ioo (-s) s) ∧
      ∀ p ∈ O ×ˢ Ioo (-s) s, linearOp (O ×ˢ Ioo (-s) s) a b (zeroPast u) p = 0 := by
  have hC := zeroPast_continuousOn_of_linear_growth hO hK hu hGrowth
  obtain ⟨v, hv, hAE, hClass⟩ := Yau.LeafProofs.L16Interior.homogeneousInteriorSmoothing
    n hn O (-s) s lam upper hO (by linarith) a b (zeroPast u) G hSmooth hEll hE hEq
  rw [productVolume_eq_restrict] at hAE
  have hQ : IsOpen (O ×ˢ Ioo (-s) s) := hO.prod isOpen_Ioo
  have hIdent : EqOn (zeroPast u) v (O ×ˢ Ioo (-s) s) :=
    Measure.eqOn_open_of_ae_eq hAE hQ hC hv.continuousOn
  refine ⟨hv.congr hIdent, ?_⟩
  intro p hp
  have he : zeroPast u =ᶠ[𝓝 p] v := eventually_of_mem (hQ.mem_nhds hp) (fun _ hq => hIdent hq)
  exact (linearOp_congr_open_sets hQ hQ a b hp hp he).trans (hClass p hp)

/-- The complete homogeneous initial-face bridge, with the actual crossing
 coefficient extension stated explicitly. There is no weak-solver premise. -/
theorem classical_homogeneous_zeroPast_smooth {n : ℕ} (hn : 0 < n)
    {O : Set (Space n)} (hO : IsOpen O) {S lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hEll : Elliptic (O ×ˢ Icc 0 S) a lam upper)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo 0 S))
    (hEq : ∀ p ∈ O ×ˢ Ioo 0 S, linearOp (O ×ˢ Icc 0 S) a b u p = 0)
    (hGrowth : ∀ W : Set (Space n), IsOpen W → IsCompact (closure W) → closure W ⊆ O →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ W, ∀ t ∈ Ioo 0 S, |u (x, t)| ≤ K * t)
    (V : Set (Space n)) (s : ℝ) (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVO : closure V ⊆ O) (hs : 0 < s) (hsS : s < S)
    (hCrossSmooth : SmoothCoefficients (V ×ˢ Ioo (-s) s) a b)
    (hCrossEll : Elliptic (V ×ˢ Ioo (-s) s) a lam upper) :
    ContDiffOn ℝ ∞ (zeroPast u) (V ×ˢ Ioo (-s) s) ∧
      ∀ p ∈ V ×ˢ Ioo (-s) s, linearOp (V ×ˢ Ioo (-s) s) a b (zeroPast u) p = 0 := by
  obtain ⟨hE, hWeak⟩ := classical_homogeneous_zeroPast_initial_energy hO hSmooth hEll hu hEq hGrowth
    V s hV hVC hVO hs hsS
  obtain ⟨K, hK, hKb⟩ := hGrowth V hV hVC hVO
  have hSub : V ×ˢ Ioo (0 : ℝ) s ⊆ O ×ˢ Ioo 0 S := fun p hp =>
    ⟨hVO (subset_closure hp.1), hp.2.1, hp.2.2.trans hsS⟩
  exact zeroPast_smooth_of_energy hn hV hs hK hCrossSmooth hCrossEll
    (hu.continuousOn.mono hSub)
    (fun p hp => hKb p.1 hp.1 p.2 ⟨hp.2.1, hp.2.2.trans hsS⟩) hE hWeak

end Yau.F04Proof
