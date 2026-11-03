import Yau.Proofs.F01UniformTimeHolderLimit
import Yau.Proofs.F01SmoothJetLimit

/-! All genuine spatial jets with a common parabolic Holder modulus
construct a smooth terminal slice along every Cauchy clock sequence.
Only spatial smoothness of the approximants is required here. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem smooth_spatial_limit_of_parabolic_jet_holder
    (f : ℝ → Space n → F) (O : Set (Space n)) (I : Set ℝ)
    (hO : IsOpen O) (hConv : Convex ℝ O)
    {α : ℝ} (hα : 0 < α) (B : ℕ → ℝ)
    (hf : ∀ t ∈ I, ContDiffOn ℝ ∞ (f t) O)
    (hJets : ∀ k, HolderBound α (O ×ˢ I)
      (fun p => iteratedFDeriv ℝ k (f p.2) p.1) (B k))
    (τ : ℕ → ℝ) (hτ : ∀ m, τ m ∈ I) (hCauchy : CauchySeq τ) :
    ∃ g : Space n → F, ContDiffOn ℝ ∞ g O ∧
      ∀ k, TendstoUniformlyOn
        (fun m x => iteratedFDeriv ℝ k (f (τ m)) x)
        (iteratedFDeriv ℝ k g) atTop O := by
  classical
  have hEach (k : ℕ) : ∃ q : Space n → ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) F,
      TendstoUniformlyOn (fun m x => iteratedFDeriv ℝ k (f (τ m)) x) q atTop O := by
    apply uniform_limit_of_time_holder
      (fun t x => iteratedFDeriv ℝ k (f t) x) O I (C := B k) (γ := α / 2)
      (by linarith) ?_ τ hτ hCauchy
    intro s hs t ht x hx
    simpa only [holderWeight, sub_self, norm_zero, Real.zero_rpow hα.ne', zero_add] using
      (hJets k).2.2 (x, s) ⟨hx, hs⟩ (x, t) ⟨hx, ht⟩
  choose Q hQ using hEach
  let q : Space n → FormalMultilinearSeries ℝ (Space n) F := fun x k => Q k x
  have hWithin (k : ℕ) : TendstoUniformlyOn
      (fun m x => iteratedFDerivWithin ℝ k (f (τ m)) O x) (fun x => q x k) atTop O := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hQ k)) ε hε] with m hm
    intro x hx
    rw [iteratedFDerivWithin_of_isOpen k hO hx]
    exact hm x hx
  obtain ⟨hg, hJet⟩ := smooth_closed_jet_limit hConv hO.uniqueDiffOn
    (fun m => f (τ m)) (fun m => hf (τ m) (hτ m)) q hWithin
  refine ⟨fun x => (q x 0).curry0, hg, ?_⟩
  intro k
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hQ k)) ε hε] with m hm
  intro x hx
  rw [← iteratedFDerivWithin_of_isOpen k hO hx, ← hJet k x hx]
  exact hm x hx

end Yau.NodeProofs.F01Aux
