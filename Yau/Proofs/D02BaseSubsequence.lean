import Yau.Proofs.D02AtomZero
import Yau.Proofs.D02DistanceConvergence

/-! Once the actual atoms vanish, the SAME regular-domain extraction is
the exact original base-disc subsequence on the entire unit disc. -/

open scoped Topology Manifold ContDiff ENNReal
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

theorem baseDisc_subsequence_of_injective_immersion {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (hinj : Function.Injective F) {K : Set (Pt X)} (hK : IsCompact K)
    (A : ℝ) (fs : ℕ → ℂ → Pt X)
    (hfs : ∀ j, IsHolomorphicDisc (fs j) ∧ (∀ z : ℂ, ‖z‖ = 1 → fs j z ∈ K) ∧
      discArea X.metric.form (fs j) ≤ ENNReal.ofReal A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → Pt X,
      MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f (ball (0 : ℂ) 1) ∧
      ∀ L ⊆ ball (0 : ℂ) 1, IsCompact L → ∀ ε : ENNReal, 0 < ε → ∃ J, ∀ j, J ≤ j →
        ∀ z ∈ L, lengthEDist X.metric.form (fs (φ j) z) (f z) < ε := by
  letI := L12Aux.inducedMetricSpace X.metric
  obtain ⟨φ, u, μ, f, B_F, B_u, hφ, _, hBu, hlocal, hμ, _, hdist, _, _, hf, hconv, _, henergy, hbound⟩ :=
    discFamily_regular_holomorphic_subsequence X hF hImm hK A fs hfs
  have hae := immersionPotential_limit_ae_on_disc X hF hImm (fun j => fs (φ j)) f u μ
    (fun j => (hfs (φ j)).1) hf.continuousOn hconv hlocal hμ
  have hatom : ∀ z ∈ ball (0 : ℂ) 1, μ {z} = 0 := fun z hz =>
    regular_limit_riesz_atom_zero X hF hImm hinj f u μ hμ hdist hae hf B_F B_u hBu.le hbound henergy hz
  have hΩ := regularPotentialDomain_eq_disc_of_zero_atoms μ hatom
  have hfD : ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f (ball (0 : ℂ) 1) := by
    simpa only [hΩ] using hf
  have hconvD : TendstoLocallyUniformlyOn (fun j => fs (φ j)) f atTop (ball (0 : ℂ) 1) := by
    simpa only [hΩ] using hconv
  refine ⟨φ, hφ, f, hfD.mdifferentiableOn (by simp), ?_⟩
  intro L hLD hL
  exact (tendstoUniformlyOn_lengthEDist_iff X.metric (fun j => fs (φ j)) f L).mp
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hconvD L hLD hL)

theorem baseDisc_compact_centres {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (hinj : Function.Injective F) {K : Set (Pt X)} (hK : IsCompact K) (A : ℝ) :
    ∃ Kc : Set (Pt X), IsCompact Kc ∧ ∀ f : ℂ → Pt X,
      IsHolomorphicDisc f → (∀ z : ℂ, ‖z‖ = 1 → f z ∈ K) →
      discArea X.metric.form f ≤ ENNReal.ofReal A → f 0 ∈ Kc := by
  let P : (ℂ → Pt X) → Prop := fun f => IsHolomorphicDisc f ∧
    (∀ z : ℂ, ‖z‖ = 1 → f z ∈ K) ∧ discArea X.metric.form f ≤ ENNReal.ofReal A
  obtain ⟨Kc, hKc, hcenter⟩ := compact_centres_of_subsequence X.metric P (by
    intro fs hfs
    obtain ⟨φ, hφ, f, _, hconv⟩ := baseDisc_subsequence_of_injective_immersion X hF hImm hinj hK A fs hfs
    refine ⟨φ, hφ, f 0, fun ε hε => ?_⟩
    obtain ⟨J, hJ⟩ := hconv {0} (singleton_subset_iff.mpr (mem_ball_self (by norm_num)))
      isCompact_singleton ε hε
    exact ⟨J, fun j hj => hJ j hj 0 (mem_singleton 0)⟩)
  exact ⟨Kc, hKc, fun f hf hb ha => hcenter f ⟨hf, hb, ha⟩⟩

end Yau.NodeProofs.D02Aux
