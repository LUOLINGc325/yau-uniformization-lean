import Yau.Proofs.D02FiberLimitGlobal
import Yau.Proofs.P03FieldGeneration

open scoped Manifold Topology ContDiff ENNReal
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02FiberLimitAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.NodeProofs.D02Aux Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

/-- The original base sequential conclusion is used internally, and the same
finite global spanning fields produce precisely the fourth D02 conclusion. -/
theorem cotangent_sequential_of_base_sequential {n m : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {K : Set M.Carrier} (hK : IsCompact K) (A₀ R : ℝ)
    (V : Fin m → VectorField M) (hV : ∀ a, IsHolomorphicField (V a))
    (hspan : ∀ x, Submodule.span ℂ (Set.range fun i ↦ V i x) = ⊤)
    (hbase : ∀ fs : ℕ → ℂ → M.Carrier,
      (∀ k, IsHolomorphicDisc (fs k) ∧ (∀ ζ : ℂ, ‖ζ‖ = 1 → fs k ζ ∈ K) ∧
        discArea g.form (fs k) ≤ ENNReal.ofReal A₀) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → M.Carrier,
        MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f (ball 0 1) ∧
        ∀ L ⊆ ball (0 : ℂ) 1, IsCompact L → ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ k, N ≤ k →
          ∀ ζ ∈ L, lengthEDist g.form (fs (φ k) ζ) (f ζ) < ε) :
    ∀ (fs : ℕ → ℂ → M.Carrier) (ξs : ℕ → ℂ → Covector n),
      (∀ k, IsCotangentDisc (fs k) (ξs k) ∧
        (∀ ζ : ℂ, ‖ζ‖ = 1 → InCotangentCompact g.form K R (fs k ζ) (ξs k ζ)) ∧
        discArea g.form (fs k) ≤ ENNReal.ofReal A₀) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (f : ℂ → M.Carrier) (ξ : ℂ → Covector n),
        MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f (ball 0 1) ∧
        (∀ L ⊆ ball (0 : ℂ) 1, IsCompact L → ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ k, N ≤ k →
          ∀ ζ ∈ L, lengthEDist g.form (fs (φ k) ζ) (f ζ) < ε) ∧
        ∀ ζ₀ ∈ ball (0 : ℂ) 1, ∃ W ∈ 𝓝 ζ₀,
          DifferentiableOn ℂ (fun ζ ↦ covectorCoords (f ζ₀) (f ζ) (ξ ζ)) W ∧
          TendstoUniformlyOn (fun k ζ ↦ covectorCoords (f ζ₀) (fs (φ k) ζ) (ξs (φ k) ζ))
            (fun ζ ↦ covectorCoords (f ζ₀) (f ζ) (ξ ζ)) atTop W := by
  intro fs ξs hfs
  obtain ⟨φ₀, hφ₀, f, hf, hconv₀⟩ := hbase fs
    (fun j ↦ ⟨(hfs j).1.1, fun z hz ↦ ((hfs j).2.1 z hz).1, (hfs j).2.2⟩)
  obtain ⟨φ₁, hφ₁, e, he, heconv⟩ := evaluationVector_subsequence g.form
    (L12Aux.metricSmooth_of_smoothMetric g) hK R V hV
    (fun j ↦ fs (φ₀ j)) (fun j ↦ ξs (φ₀ j)) (fun j ↦ (hfs (φ₀ j)).1)
    (fun j z hz ↦ (hfs (φ₀ j)).2.1 z hz)
  let φ := φ₀ ∘ φ₁
  have hconv : ∀ L ⊆ ball (0 : ℂ) 1, IsCompact L → ∀ ε : ENNReal, 0 < ε → ∃ N,
      ∀ k, N ≤ k → ∀ ζ ∈ L, lengthEDist g.form (fs (φ k) ζ) (f ζ) < ε := by
    intro L hLD hL ε hε
    obtain ⟨N, hN⟩ := hconv₀ L hLD hL ε hε
    exact ⟨N, fun k hk ↦ hN (φ₁ k) (hk.trans (hφ₁.id_le k))⟩
  letI := L12Aux.inducedMetricSpace g
  have hloc : TendstoLocallyUniformlyOn (fun j ↦ fs (φ j)) f atTop (ball 0 1) := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mpr
    intro L hLD hL
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hconv L hLD hL (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
    filter_upwards [eventually_ge_atTop N] with j hj z hz
    have hh := hN j hj z hz
    change ENNReal.ofReal (dist (fs (φ j) z) (f z)) < ENNReal.ofReal ε at hh
    have hd : dist (fs (φ j) z) (f z) < ε := (ENNReal.ofReal_lt_ofReal_iff hε).mp hh
    simpa only [dist_comm] using hd
  obtain ⟨ξ, hξ⟩ := global_fiber_limit g V hV hspan (fun j ↦ fs (φ j)) (fun j ↦ ξs (φ j))
    (fun j ↦ (hfs (φ j)).1) f hf hloc e he heconv
  exact ⟨φ, hφ₀.comp hφ₁, f, ξ, hf, hconv, hξ⟩

/-- The actual accepted original P03 field producer closes the finite-field
input, leaving only the original base conclusion as an internal argument. -/
theorem original_fourth_conj_of_base {n : ℕ} (X : KahlerManifold n)
    {K : Set (Pt X)} (hK : IsCompact K) (A₀ R : ℝ)
    (hbase : ∀ fs : ℕ → ℂ → Pt X,
      (∀ k, IsHolomorphicDisc (fs k) ∧ (∀ ζ : ℂ, ‖ζ‖ = 1 → fs k ζ ∈ K) ∧
        discArea X.metric.form (fs k) ≤ ENNReal.ofReal A₀) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → Pt X,
        MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f (ball 0 1) ∧
        ∀ L ⊆ ball (0 : ℂ) 1, IsCompact L → ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ k, N ≤ k →
          ∀ ζ ∈ L, lengthEDist X.metric.form (fs (φ k) ζ) (f ζ) < ε) :
    ∀ (fs : ℕ → ℂ → Pt X) (ξs : ℕ → ℂ → Covector n),
      (∀ k, IsCotangentDisc (fs k) (ξs k) ∧
        (∀ ζ : ℂ, ‖ζ‖ = 1 → InCotangentCompact X.metric.form K R (fs k ζ) (ξs k ζ)) ∧
        discArea X.metric.form (fs k) ≤ ENNReal.ofReal A₀) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (f : ℂ → Pt X) (ξ : ℂ → Covector n),
        MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f (ball 0 1) ∧
        (∀ L ⊆ ball (0 : ℂ) 1, IsCompact L → ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ k, N ≤ k →
          ∀ ζ ∈ L, lengthEDist X.metric.form (fs (φ k) ζ) (f ζ) < ε) ∧
        ∀ ζ₀ ∈ ball (0 : ℂ) 1, ∃ W ∈ 𝓝 ζ₀,
          DifferentiableOn ℂ (fun ζ ↦ covectorCoords (f ζ₀) (f ζ) (ξ ζ)) W ∧
          TendstoUniformlyOn (fun k ζ ↦ covectorCoords (f ζ₀) (fs (φ k) ζ) (ξs (φ k) ζ))
            (fun ζ ↦ covectorCoords (f ζ₀) (f ζ) (ξ ζ)) atTop W := by
  obtain ⟨m, V, hV, hspan⟩ := Yau.NodeProofs.P03Aux.field_finite_generation X
  exact cotangent_sequential_of_base_sequential X.metric hK A₀ R V hV hspan hbase

end Yau.NodeProofs.D02FiberLimitAux
