import Yau.Proofs.F04CompactPotentialSequence
import Yau.Proofs.F04CutoffPotentialConvergence
import Yau.Proofs.F04CompactAntitoneConvergence

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- The ORIGINAL supercaloric-tail clause is constructed from the SAME
 localized flow. Exact P07 supplies the controlled exhaustion; exact G02
 supplies the initial volume; F03 is used only through the previously proved
 caloric uniqueness. Actual compact-source potentials, closed-face
 regularity, source-cutoff convergence and a compact finite-cover argument
 produce every requested tail and quantifier. -/
theorem flow_supercaloric_tails_from_dependencies
    (hP07 : P07) (hF03 : F03) (hG02 : G02)
    {n : ℕ} (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T) :
    ∃ ρs : ℕ → STF X, ∃ Cs : ℕ → ℝ,
      (∀ j, SmoothSpaceTime (ρs j) (Icc 0 T) ∧ ∀ x t, t ∈ Icc 0 T →
        0 ≤ ρs j x t ∧ ρs j x t ≤ ρ x t ∧ ρ x t-Cs j ≤ ρs j x t ∧
        0 ≤ heatOp h (Icc 0 T) (ρs j) x t) ∧
      ∀ K : Set (Pt X), IsCompact K → ∀ ε, 0 < ε → ∃ J, ∀ j, J ≤ j →
        ∀ x ∈ K, ∀ t ∈ Icc 0 T, ρs j x t ≤ ε := by
  classical
  obtain ⟨u,hu⟩ := hP07 n X o
  obtain ⟨μ,hμ,_⟩ := hG02 n X.manifold X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)
  have hS : 0 < 2*T := by positivity
  have hTS : T < 2*T := by linarith
  obtain ⟨qs,v,M,hqs,hCut,hMono,hData⟩ := flow_compact_source_potential_sequence hn X o h U P ρ hloc
    μ hμ u hu hS hT hTS
  have hBound : ∀ j x t, t ∈ Icc 0 (2*T) → 0 ≤ v j x t ∧ v j x t ≤ ρ x t :=
    fun j x t ht => ⟨((hData j).2.1 x t ht).1,((hData j).2.1 x t ht).2.1⟩
  have hConv := cutoff_potentials_tend_rho_from_dependencies hP07 hF03 hG02 hn X o h U P ρ hloc
    hS hT hTS qs hCut v hMono hBound (fun j => (hData j).2.2.1)
    (fun j => (hData j).2.2.2.1) (fun j => (hData j).2.2.2.2.1)
  have hρ : SmoothSpaceTime ρ (Icc 0 T) := fun c => (hloc.2.2.2.1 c).mono
    (Set.prod_mono (Subset.refl _) (fun _ ht => ht.1))
  let ρs : ℕ → STF X := fun j x t => ρ x t-v j x t
  have hSmooth (j : ℕ) : SmoothSpaceTime (ρs j) (Icc 0 T) :=
    fun c => (hρ c).sub ((hData j).2.2.2.2.2.1 c)
  refine ⟨ρs,(fun j => M j*T),?_,?_⟩
  · intro j
    refine ⟨hSmooth j,?_⟩
    intro x t ht
    have htS : t ∈ Icc 0 (2*T) := ⟨ht.1,ht.2.trans hTS.le⟩
    have hb := (hData j).2.1 x t htS
    have hLinear : v j x t ≤ M j*T := hb.2.2.trans (mul_le_mul_of_nonneg_left ht.2 (hData j).1)
    refine ⟨sub_nonneg.mpr hb.2.1,sub_le_self _ hb.1,sub_le_sub_left hLinear _,?_⟩
    have he := heatOp_sub_smooth h hT hρ ((hData j).2.2.2.2.2.1) x ht
    change 0 ≤ heatOp h (Icc 0 T) (fun x t => ρ x t-v j x t) x t
    rw [he,rho_source_equation o h U P ρ hloc T hT x t ht,(hData j).2.2.2.2.2.2 x t ht]
    have hNN := mul_nonneg (sub_nonneg.mpr ((hqs j).2.2 x).2) (source_nonneg o h U P ρ hloc x t ht.1)
    nlinarith only [hNN]
  · intro K hK ε hε
    have hCont (j : ℕ) : ContinuousOn (fun p : Pt X × ℝ => ρs j p.1 p.2) (K ×ˢ Icc 0 T) :=
      (smoothSpaceTime_continuousOn (hSmooth j)).mono (Set.prod_mono (subset_univ K) (Subset.refl _))
    have hAnti (p : Pt X × ℝ) (hp : p ∈ K ×ˢ Icc 0 T) : Antitone (fun j => ρs j p.1 p.2) := by
      intro i j hij
      exact sub_le_sub_left (hMono p.1 p.2 ⟨hp.2.1,hp.2.2.trans hTS.le⟩ hij) _
    have hPoint (p : Pt X × ℝ) (hp : p ∈ K ×ˢ Icc 0 T) :
        Tendsto (fun j => ρs j p.1 p.2) atTop (𝓝 0) := by
      have hh : Tendsto (fun j => ρ p.1 p.2-v j p.1 p.2) atTop
          (𝓝 (ρ p.1 p.2-ρ p.1 p.2)) := tendsto_const_nhds.sub (hConv p.1 p.2 hp.2)
      simpa only [ρs,sub_self] using hh
    obtain ⟨J,hJ⟩ := compact_antitone_uniform_upper_zero (hK.prod isCompact_Icc)
      (fun j p => ρs j p.1 p.2) hCont hAnti hPoint ε hε
    exact ⟨J,fun j hj x hx t ht => hJ j hj (x,t) ⟨hx,ht⟩⟩

end Yau.F04Proof
