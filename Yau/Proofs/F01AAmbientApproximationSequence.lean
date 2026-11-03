import Yau.Proofs.F01AActualApproximationSequence
import Yau.Proofs.F01CompactAmbientFlowIdentity
import Yau.Proofs.F01AAmbientPotentialSmooth

/-! The chosen continued solutions are extended only as scalar values.
Every compact core eventually carries the exact ambient potential identity
and closed-time equation of this same sequence. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

def ambientApproximationPotential
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u) (L : ℝ) (ho : u o < L)
    (U : (sublevelManifold X.manifold u hu.1 o L ho).Carrier → ℝ → ℝ) : STF X :=
  openExtendedPotential X.manifold (sublevelOpens X.manifold u hu.1 o L)
    (sublevelComponent_isConnected ho) U

theorem ambientApproximationPotential_initial
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u) (L : ℝ) (ho : u o < L)
    (U : (sublevelManifold X.manifold u hu.1 o L ho).Carrier → ℝ → ℝ)
    (hU0 : ∀ x, U x 0 = 0) :
    ∀ x, ambientApproximationPotential X o u hu L ho U x 0 = 0 := by
  classical
  intro x
  unfold ambientApproximationPotential openExtendedPotential
  split_ifs with hx
  · exact hU0 _
  · rfl

theorem actual_approximation_sequence_eventual_ambient_identity
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u)
    (L : ℕ → ℝ) (ho : ∀ m, u o < L m)
    (h : ∀ m, ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o (L m) (ho m)))
    (U : ∀ m, (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier → ℝ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsol : ∀ m, NativePotentialSlab
      (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m))
      ((m : ℝ) + 2) (h m) (U m))
    {K : Set (Pt X)} (hK : IsCompact K) (T : ℝ) :
    ∀ᶠ m in atTop,
      K ⊆ sublevelComponent u o (L m) ∧
      ∀ x : (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier,
        x.val ∈ K → ∀ t ∈ Icc 0 T,
          gMat (h m t) x = gMat X.metric.form x.val -
            (t : ℂ) • ricci X.metric.form x.val +
            levi (fun y => ambientApproximationPotential X o u hu (L m) (ho m) (U m) y t) x.val ∧
          HasDerivWithinAt
            (ambientApproximationPotential X o u hu (L m) (ho m) (U m) x.val)
            (Real.log ((gMat (h m t) x).det.re / (gMat X.metric.form x.val).det.re))
            (Icc 0 T) t := by
  obtain ⟨L0, _, hcore⟩ := compact_ambient_approximate_flow_identity X o u hu hK
  obtain ⟨N, hN⟩ := exists_nat_gt T
  filter_upwards [hL.eventually (eventually_ge_atTop L0), eventually_ge_atTop N] with m hm hmN
  have hmT : T ≤ (m : ℝ) + 2 := by
    have hcast : (N : ℝ) ≤ m := by exact_mod_cast hmN
    linarith
  have hsub : Icc (0 : ℝ) T ⊆ Icc 0 ((m : ℝ) + 2) :=
    fun t ht => ⟨ht.1, ht.2.trans hmT⟩
  obtain ⟨_, _, _, _, C, _, hdata⟩ := hsol m
  obtain ⟨hsubset, hidentity⟩ := hcore (L m) hm (ho m)
  refine ⟨hsubset, ?_⟩
  intro x hx t ht
  have hh := hidentity (h m) (U m) (Icc 0 T)
    (fun x t ht => (hdata x t (hsub ht)).2.2.1)
    (fun x t ht => ((hdata x t (hsub ht)).2.2.2).mono hsub) x hx t ht
  exact hh

theorem actual_approximation_sequence_eventual_chart_smoothness
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u)
    (L : ℕ → ℝ) (ho : ∀ m, u o < L m)
    (h : ∀ m, ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o (L m) (ho m)))
    (U : ∀ m, (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier → ℝ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsol : ∀ m, NativePotentialSlab
      (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m))
      ((m : ℝ) + 2) (h m) (U m))
    (e : OpenPartialHomeomorph (ComplexVector n) X.manifold.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKe : K ⊆ e.source) (T : ℝ) :
    ∀ᶠ m in atTop, ContDiffOn ℝ ∞
      (fun p : ComplexVector n × ℝ =>
        ambientApproximationPotential X o u hu (L m) (ho m) (U m) (e p.1) p.2)
      (K ×ˢ Icc 0 T) := by
  have hImage : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKe)
  obtain ⟨L0, _, hcore⟩ := compact_approximation_identity X o u hu hImage
  obtain ⟨N, hN⟩ := exists_nat_gt T
  filter_upwards [hL.eventually (eventually_ge_atTop L0), eventually_ge_atTop N] with m hm hmN
  have hmT : T ≤ (m : ℝ) + 2 := by
    have hcast : (N : ℝ) ≤ m := by exact_mod_cast hmN
    linarith
  have hsub : Icc (0 : ℝ) T ⊆ Icc 0 ((m : ℝ) + 2) :=
    fun t ht => ⟨ht.1, ht.2.trans hmT⟩
  have hUm : SmoothSpaceTime (U m) (Icc 0 T) :=
    fun x => ((hsol m).2.2.1 x).mono (prod_mono Subset.rfl hsub)
  apply openExtendedPotential_holomorphic_chart_smooth X.manifold
    (sublevelOpens X.manifold u hu.1 o (L m)) (sublevelComponent_isConnected (ho m))
    (U m) hUm e he hKe
  intro z hz
  exact (hcore (L m) hm (ho m)).1 ⟨z, hz, rfl⟩

end Yau.NodeProofs.F01Aux
