import Yau.Proofs.C07LimitUpperBound
import Yau.Proofs.C07ManifoldUpperBound
import Yau.Proofs.D04

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

/-- The psh compactness and Liouville step in the common-exponent argument.
One fixed negative neighborhood forces the same negative bound on every
compact along a subsequence, including the collapsing alternative. -/
theorem negative_psh_subsequence {n : ℕ} (X : KahlerManifold n)
    (g : HermitianField X.manifold) (hg : MetricSmooth g)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume g μ) (hLiouville : PshLiouville X)
    (Ω : ℕ → Set (Pt X)) (us : ℕ → Pt X → EReal)
    (hΩ : ∀ j, IsOpen (Ω j) ∧ Ω j ⊆ Ω (j + 1)) (hcover : (⋃ j, Ω j) = univ)
    (hpsh : ∀ j, PshOnManifold (us j) (Ω j))
    (hupper : ∀ K : Set (Pt X), IsCompact K → ∃ C : ℝ, ∀ j,
      K ⊆ Ω j → ∀ x ∈ K, us j x ≤ (C : EReal))
    (hzero : ∀ K : Set (Pt X), IsCompact K → ∃ N, ∀ j, N ≤ j →
      ∀ x ∈ K, us j x ≤ (0 : EReal))
    (K₀ : Set (Pt X)) (hK₀ : IsCompact K₀) (hμK₀ : 0 < μ K₀)
    {a : ℝ} (ha : 0 < a)
    (hnegative : ∃ N, ∀ j, N ≤ j → ∀ x ∈ K₀, us j x ≤ ((-a : ℝ) : EReal)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ K : Set (Pt X), IsCompact K →
      ∃ N, ∀ j, N ≤ j → ∀ x ∈ K, us (φ j) x ≤ ((-a / 2 : ℝ) : EReal) := by
  obtain ⟨φ, hφ, halt, _, _⟩ :=
    Yau.NodeProofs.D04_proved n X.manifold g hg μ hμ Ω us hΩ hcover hpsh hupper
  refine ⟨φ, hφ, ?_⟩
  rcases halt with hcollapse | ⟨u, hupsh, hune, _, hL1, hhartogs⟩
  · intro K hK
    simpa only [neg_div] using hcollapse K hK (a / 2)
  · have hlimitUpper {K : Set (Pt X)} (hK : IsCompact K) {C : ℝ}
        (hC : ∃ N, ∀ j, N ≤ j → ∀ x ∈ K, us j x ≤ (C : EReal)) :
        ∀ᵐ x ∂μ.restrict K, u x ≤ (C : EReal) := by
      obtain ⟨N, hN⟩ := hC
      have hseqmeas := Yau.Proofs.D04AtlasGlueAux.eventually_aemeasurable_on_compact
        Ω us hΩ hcover hpsh hφ hK μ
      apply limit_ae_le_of_eventually_bounded hseqmeas hupsh.2.1.measurable.aemeasurable
        (hL1 K hK).2
      filter_upwards [eventually_ge_atTop N] with j hj
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact hN (φ j) (hj.trans (hφ.id_le j)) x hx
    have hubound : ∀ x, u x ≤ (0 : EReal) :=
      manifold_psh_le_of_ae_compact_bound g hg μ hμ hupsh (fun K hK => hlimitUpper hK (hzero K hK))
    have hconst := hLiouville u hupsh ⟨0, hubound⟩
    obtain ⟨x₀, hx₀⟩ := hune
    let c := (u x₀).toReal
    have hc₀ : u x₀ = (c : EReal) :=
      (EReal.coe_toReal (ne_of_lt (hupsh.1 x₀)) hx₀).symm
    have huc : ∀ x, u x = (c : EReal) := fun x => (hconst x x₀).trans hc₀
    have haeref := hlimitUpper hK₀ hnegative
    obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hμK₀.ne' haeref
    have hca : c ≤ -a := EReal.coe_le_coe_iff.mp (by simpa only [huc x] using hx)
    intro K hK
    obtain ⟨N, hN⟩ := hhartogs c huc K hK (a / 2) (by positivity)
    refine ⟨N, ?_⟩
    intro j hj x hxK
    exact (hN j hj x hxK).trans (EReal.coe_le_coe_iff.mpr (by linarith))

end Yau.Proofs.C07Aux
