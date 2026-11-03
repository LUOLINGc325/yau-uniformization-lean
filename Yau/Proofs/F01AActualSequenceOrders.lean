import Yau.Proofs.F01ACompactActualBounds
import Yau.Proofs.F01AAmbientApproximationSequence
import Yau.Proofs.F01PotentialMetricAssembly

/-! The actual compact comparison estimates become eventual orders of
the ambient potential matrices. They do not assert that early members
are positive or that their zero extensions are global smooth solutions. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem actual_approximation_eventual_native_orders
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef)
    {c : ℝ} (hc : 0 ≤ c)
    (hgrowth : ∀ x, Ξ x ≤ c * (1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2)))
    (L : ℕ → ℝ) (ho : ∀ m : ℕ, u o < L m)
    (h : ∀ m : ℕ, ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o (L m) (ho m)))
    (U : ∀ m : ℕ, (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier → ℝ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsol : ∀ m : ℕ, NativePotentialSlab
      (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m))
      ((m : ℝ) + 2) (h m) (U m)) :
    let f : ℕ → STF X := fun m => ambientApproximationPotential X o u hu (L m) (ho m) (U m)
    ∀ x t, 0 ≤ t → ∃ ell : ℝ, 0 < ell ∧ ∃ R : ℝ,
      (∀ᶠ m in atTop, (nativePotentialMatrix X.metric.form (f m) t x -
        (ell : ℂ) • gMat X.metric.form x).PosSemidef) ∧
      (∀ᶠ m in atTop, ((Real.exp (2 * R / L m) : ℂ) • gMat X.metric.form x -
        nativePotentialMatrix X.metric.form (f m) t x).PosSemidef) := by
  dsimp only
  intro x t ht
  let K : Set (Pt X) := {x}
  let T : ℝ := t + 1
  have hK : IsCompact K := isCompact_singleton
  have hT : 0 < T := by dsimp only [T]; linarith
  have htT : t ∈ Icc 0 T := ⟨ht, by dsimp only [T]; linarith⟩
  obtain ⟨a0, L0, A, ell, R, _, _, _, hell, _, hBound⟩ :=
    actual_compact_uniform_bounds X o u hu Ξ hΞ hRic hc hgrowth hK hT
  obtain ⟨Le, _, hExact⟩ := compact_approximation_identity X o u hu hK
  have hAmbient := actual_approximation_sequence_eventual_ambient_identity
    X o u hu L ho h U hL hsol hK T
  have hHorizon : ∀ᶠ m : ℕ in atTop, T < (m : ℝ) + 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt T
    filter_upwards [eventually_ge_atTop N] with m hm
    have hcast : (N : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hOrders : ∀ᶠ m : ℕ in atTop,
      (nativePotentialMatrix X.metric.form
        (ambientApproximationPotential X o u hu (L m) (ho m) (U m)) t x -
        (ell : ℂ) • gMat X.metric.form x).PosSemidef ∧
      ((Real.exp (2 * R / L m) : ℂ) • gMat X.metric.form x -
        nativePotentialMatrix X.metric.form
          (ambientApproximationPotential X o u hu (L m) (ho m) (U m)) t x).PosSemidef := by
    filter_upwards [hAmbient, hL.eventually (eventually_ge_atTop L0),
      hL.eventually (eventually_ge_atTop Le), hHorizon] with m hm hmL hmE hmT
    let xm : (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier :=
      ⟨x, hm.1 (mem_singleton x)⟩
    have hNative := (hm.2 xm (mem_singleton x) t htT).1
    have hBase := ((hExact (L m) hmE (ho m)).2 xm (mem_singleton x)).2.1
    have hb := hBound (L m) hmL (ho m) ((m : ℝ) + 2) (h m) (U m) hmT (hsol m)
      xm (mem_singleton x) t htT
    have hlo := hb.2.2.2.1
    have hhi := hb.2.2.2.2
    rw [hBase, hNative] at hlo hhi
    exact ⟨hlo,hhi⟩
  exact ⟨ell, hell, R, hOrders.mono (fun _ hm => hm.1), hOrders.mono (fun _ hm => hm.2)⟩

end Yau.NodeProofs.F01Aux
