import Yau.Proofs.F01CountableUniformSubsequence
import Yau.Proofs.F01DerivativeBoundCompactness
import Yau.Proofs.F01SmoothJetLimit

/-! Uniform bounds for every actual derivative on a convex compact
domain construct one smooth limit and one subsequence converging in every
derivative order, with the closed faces included. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction NNReal
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem compact_smooth_subsequence
    {S : Set E} (hS : Convex ℝ S) (hcompact : IsCompact S) (hUnique : UniqueDiffOn ℝ S)
    (f : ℕ → E → F) (hf : ∀ m, ContDiffOn ℝ ∞ (f m) S)
    (C : ℕ → ℝ≥0)
    (hbound : ∀ k m x, x ∈ S → ‖iteratedFDerivWithin ℝ k (f m) S x‖ ≤ C k) :
    ∃ g : E → F, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ContDiffOn ℝ ∞ g S ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun m x => iteratedFDerivWithin ℝ k (f (σ m)) S x)
        (iteratedFDerivWithin ℝ k g S) atTop S := by
  classical
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hcompact
  let J : ℕ → Type _ := fun k => ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F
  letI (k : ℕ) : FiniteDimensional ℝ (J k) :=
    FiniteDimensional.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  have hTaylor (m : ℕ) : HasFTaylorSeriesUpToOn ∞ (f m)
      (ftaylorSeriesWithin ℝ (f m) S) S := (hf m).ftaylorSeriesWithin hUnique
  have hc (m k : ℕ) : ContinuousOn (iteratedFDerivWithin ℝ k (f m) S) S :=
    (hTaylor m).cont k (by simp)
  let u : ℕ → ∀ k, S →ᵇ J k := fun m k => BoundedContinuousFunction.mkOfCompact
    ⟨(fun x : S => iteratedFDerivWithin ℝ k (f m) S x), (hc m k).restrict⟩
  have hLip (k m : ℕ) : LipschitzWith (C (k + 1)) (fun x : S => u m k x) := by
    have hk : (k : ℕ∞ω) < ∞ := by exact_mod_cast (ENat.natCast_lt_top k)
    apply convex_derivative_bound_lipschitz hS (iteratedFDerivWithin ℝ k (f m) S)
      (fun x => (iteratedFDerivWithin ℝ (k + 1) (f m) S x).curryLeft) (C (k + 1))
    · exact fun x hx => (hTaylor m).fderivWithin k hk x hx
    · intro x hx
      simpa only [ContinuousMultilinearMap.curryLeft_norm] using hbound (k + 1) m x hx
  have hEqui (k : ℕ) : Equicontinuous (fun m x => u m k x) :=
    (LipschitzWith.uniformEquicontinuous (fun m x => u m k x) (C (k + 1)) (hLip k)).equicontinuous
  obtain ⟨v, σ, hσ, hconv⟩ := countable_uniform_subsequence u hEqui (fun k => (C k : ℝ))
    (fun k m x => hbound k m x x.property)
  let q : E → FormalMultilinearSeries ℝ E F := fun x k =>
    if hx : x ∈ S then v k ⟨x, hx⟩ else 0
  have hUniformJet (k : ℕ) : TendstoUniformlyOn
      (fun m x => iteratedFDerivWithin ℝ k (f (σ m)) S x) (fun x => q x k) atTop S := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp (hconv k)) ε hε] with m hm
    intro x hx
    have h := hm ⟨x, hx⟩
    change dist (v k ⟨x, hx⟩) (iteratedFDerivWithin ℝ k (f (σ m)) S x) < ε at h
    simpa only [q, dif_pos hx] using h
  obtain ⟨hg, hq⟩ := smooth_closed_jet_limit hS hUnique (fun m => f (σ m))
    (fun m => hf (σ m)) q hUniformJet
  refine ⟨(fun x => (q x 0).curry0), σ, hσ, hg, ?_⟩
  intro k
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hUniformJet k)) ε hε] with m hm
  intro x hx
  rw [← hq k x hx]
  exact hm x hx

end Yau.NodeProofs.F01Aux
