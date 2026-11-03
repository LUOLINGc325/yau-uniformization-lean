import Yau.Proofs.D03ImageJets
import Yau.Proofs.D03GermClosure
import Yau.Proofs.D03ClosureSubmoduleRecovery

noncomputable section

open MeasureTheory Filter Set Bundle
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.Proofs.D03Aux
open Yau Yau.BundleDbar Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1} {r q : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Genuine positive-exponent approximants, their actual image germs, closed
finite jet images and Krull intersection recover the original section itself. -/
theorem extra_integrability_of_approximants
    (hKrull : Yau.LeafObligations.L25)
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (k : BundleDbar.Metric E)
    (hk : BundleDbar.SmoothMetric (r := r) E k)
    (A : MapToTrivial E q) (hE : Holomorphic (r := r) E)
    (hHA : HolomorphicMap (r := r) E A) (hA : PointwiseInjective E A)
    (hBound : BoundedMap E k A)
    (s : Section E) (hs : HolomorphicSection (r := r) E s)
    (hInt : sectionIntegral E c k s < ⊤)
    (b : ℕ → Section E) (hb : ∀ n, HolomorphicSection (r := r) E (b n))
    (hbFinite : ∀ n, sectionIntegral E c k (b n) < ⊤)
    (hbExtra : ∀ n, weightedSectionIntegral E c k (b n)
      (Real.exp (-2 * correctionParameter n)) (2 / correctionParameter n) < ⊤)
    (hbConv : Tendsto (fun n => sectionIntegral E c k (fun x => b n x - s x)) atTop (𝓝 0)) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < σ ∧ weightedSectionIntegral E c k s ρ σ < ⊤ := by
  obtain ⟨F, Fn, hF, hFn, hFEq, hFnEq, hDiffFinite, hDiffConv⟩ :=
    image_extensions_and_l2_convergence E c hc k hk A hE hHA hBound s hs hInt b hb hbFinite hbConv
  have hF0 : AnalyticAt ℂ F 0 := hF.analyticAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)))
  have hFn0 (n : ℕ) : AnalyticAt ℂ (Fn n) 0 := (hFn n).analyticAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)))
  let S := extraImageGerms (r := r) E c hc k hk A
  let g : Fin q → AnalyticGerm := vectorGerm F hF0
  let gn : ℕ → Fin q → AnalyticGerm := fun n => vectorGerm (Fn n) (hFn0 n)
  have hgn (n : ℕ) : gn n ∈ S := by
    apply (mem_extraImageGerms E c hc k hk A (gn n)).mpr
    refine ⟨Real.exp (-2 * correctionParameter n), 2 / correctionParameter n,
      (correction_radius_bounds n).1, (correction_radius_bounds n).2,
      correction_exponent_pos n, b n, ?_, hbExtra n, Fn n, hFn0 n, ?_, rfl, ?_⟩
    · intro a
      exact (hb n a).mono inter_subset_left
    · exact (hFn n).mono (Metric.ball_subset_ball (correction_radius_bounds n).2.le)
    · intro z hz0 hzρ
      exact hFnEq n z ⟨hz0, hzρ.trans (correction_radius_bounds n).2⟩
  have hcomponents := holomorphic_l2_component_iteratedDeriv_tendsto 1 (by norm_num)
    F Fn hF hFn hDiffFinite hDiffConv
  have hderivatives : ∀ (i : Fin q) (j : ℕ), Tendsto
      (fun n => germDerivative j (gn n i)) atTop (𝓝 (germDerivative j (g i))) := by
    intro i j
    have hgnDeriv (n : ℕ) : germDerivative j (gn n i) =
        iteratedDeriv j (fun z => Fn n z i) 0 :=
      germDerivative_ofAnalytic j _ _
    have hgDeriv : germDerivative j (g i) = iteratedDeriv j (fun z => F z i) 0 :=
      germDerivative_ofAnalytic j _ _
    simpa only [hgnDeriv, hgDeriv] using hcomponents i j
  have hjets := jet_tendsto_of_component_derivatives q gn g hderivatives
  have hg : g ∈ S := mem_of_tendsto_all_jets hKrull q S gn g hgn hjets
  apply extra_integrability_of_imageGerm_mem E c hc k hk A hA s F hF0 1
    (by norm_num) _ hg
  intro z hz0 hz1
  exact hFEq z ⟨hz0, hz1⟩

end Yau.Proofs.D03Aux
