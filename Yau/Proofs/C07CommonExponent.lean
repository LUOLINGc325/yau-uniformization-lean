import Yau.Proofs.C07CommonNegativeBound
import Yau.Proofs.C07ManifoldLogNorm
import Yau.Proofs.C07DecayNormalization

open MeasureTheory Filter Set
open scoped Topology Manifold

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

/-- The common-exponent step for the same exhausting inverse maps.  A
uniform chart-radius bound and compact-dependent local exponential decay
are upgraded using genuine psh compactness and the original Liouville
predecessor; no common exponent is supplied as a premise. -/
theorem common_exponent_of_local_decay {n m : ℕ} (X : KahlerManifold n)
    (g : HermitianField X.manifold) (hg : MetricSmooth g)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume g μ) (hLiouville : PshLiouville X)
    (Ω : ℝ → Set (Pt X)) (f : ℝ → Pt X → ComplexVector m)
    (s : ℝ → ℝ) (hclock : Tendsto s atTop atTop) (T₀ r : ℝ) (hr : 0 < r)
    (hopen : ∀ t, T₀ ≤ t → IsOpen (Ω t)) (hmono : MonotoneOn Ω (Ici T₀))
    (hexhaust : ∀ K : Set (Pt X), IsCompact K → ∃ T, ∀ t, T ≤ t → K ⊆ Ω t)
    (hf : ∀ t, T₀ ≤ t → MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector m) (f t) (Ω t))
    (hball : ∀ t, T₀ ≤ t → ∀ x ∈ Ω t, ‖f t x‖ ≤ r)
    (hlocal : ∀ K : Set (Pt X), IsCompact K → ∃ a C T : ℝ, 0 < a ∧
      ∀ t, T ≤ t → ∀ x ∈ K, ‖f t x‖ ≤ C * Real.exp (-a * s t)) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ K : Set (Pt X), IsCompact K → ∃ T, ∀ t, T ≤ t →
      ∀ x ∈ K, ‖f t x‖ ≤ Real.exp (-σ * s t) := by
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (hclock.eventually (eventually_ge_atTop (1 : ℝ)))
  let T := max T₀ T₁
  let v := fun t x => ((s t)⁻¹ : ℝ) * (ENNReal.log (ENNReal.ofReal ‖f t x‖) : EReal)
  have ht₀ {t : ℝ} (ht : T ≤ t) : T₀ ≤ t := (le_max_left _ _).trans ht
  have hs {t : ℝ} (ht : T ≤ t) : 0 < s t :=
    lt_of_lt_of_le zero_lt_one (hT₁ t ((le_max_right _ _).trans ht))
  have hvpsh : ∀ t, T ≤ t → PshOnManifold (v t) (Ω t) := by
    intro t ht
    exact manifold_psh_positive_scale (manifold_logNorm_psh (hopen t (ht₀ ht)) (hf t (ht₀ ht)))
      (inv_pos.mpr (hs ht))
  have hvlocal (K : Set (Pt X)) (hK : IsCompact K) :
      ∃ b S : ℝ, 0 < b ∧ ∀ t, S ≤ t → ∀ x ∈ K, v t x ≤ ((-b : ℝ) : EReal) := by
    obtain ⟨a, C, S, ha, hdecay⟩ := hlocal K hK
    obtain ⟨S₁, hS₁⟩ := eventual_pure_exponential f K hclock ha hdecay
    refine ⟨a / 2, max T S₁, by positivity, ?_⟩
    intro t ht x hx
    simpa only [v, neg_div] using (normalized_logNorm_le_real_iff
      (f t x) (hs ((le_max_left _ _).trans ht)) (-a / 2)).mpr
      (by simpa only [neg_div] using hS₁ t ((le_max_right _ _).trans ht) x hx)
  have hvupper : ∀ K : Set (Pt X), IsCompact K → ∃ C : ℝ, ∀ t,
      T ≤ t → K ⊆ Ω t → ∀ x ∈ K, v t x ≤ (C : EReal) := by
    intro K hK
    let C := max 0 (Real.log r)
    refine ⟨C, ?_⟩
    intro t ht hKt x hx
    apply (normalized_logNorm_le_real_iff (f t x) (hs ht) C).mpr
    have hst : 1 ≤ s t := hT₁ t ((le_max_right _ _).trans ht)
    have hC : 0 ≤ C := le_max_left _ _
    have hlog : Real.log r ≤ C * s t :=
      (le_max_right _ _).trans (by nlinarith)
    exact (hball t (ht₀ ht) x (hKt hx)).trans
      ((show r = Real.exp (Real.log r) from (Real.exp_log hr).symm) ▸ Real.exp_le_exp.mpr hlog)
  have hvzero : ∀ K : Set (Pt X), IsCompact K → ∃ S, ∀ t, S ≤ t →
      ∀ x ∈ K, v t x ≤ (0 : EReal) := by
    intro K hK
    obtain ⟨b, S, hb, hS⟩ := hvlocal K hK
    exact ⟨S, fun t ht x hx => (hS t ht x hx).trans (EReal.coe_le_coe_iff.mpr (by linarith))⟩
  obtain ⟨K₀, hK₀, _, hμK₀⟩ := Yau.Proofs.D04AtlasGlueAux.exists_compact_positive_subset
    g hg μ hμ isOpen_univ (Set.univ_nonempty : (univ : Set (Pt X)).Nonempty)
  obtain ⟨b, S, hb, hS⟩ := hvlocal K₀ hK₀
  have hcommon := common_negative_bound X g hg μ hμ hLiouville Ω v T
    (fun t ht => hopen t (ht₀ ht))
    (fun t ht u hu htu => hmono (ht₀ ht) (ht₀ hu) htu)
    hexhaust hvpsh hvupper hvzero K₀ hK₀ hμK₀ hb ⟨S, hS⟩
  refine ⟨b / 4, by positivity, ?_⟩
  intro K hK
  obtain ⟨S₂, hS₂⟩ := hcommon K hK
  refine ⟨max T S₂, ?_⟩
  intro t ht x hx
  have hneg := hS₂ t ((le_max_right _ _).trans ht) x hx
  have hnorm := (normalized_logNorm_le_real_iff (f t x) (hs ((le_max_left _ _).trans ht))
    (-b / 4)).mp hneg
  simpa only [neg_div] using hnorm

end Yau.Proofs.C07Aux
