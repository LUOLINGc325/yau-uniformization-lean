import Yau.Proofs.V03Elementary

/-! Uniform convergence on a compact fiber from actual joint continuity
at that fiber, with a one-sided radial parameter. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem tendstoUniformlyOn_of_continuousWithinAt_fiber {F : Type*} [PseudoMetricSpace F]
    {K : Set ℝ} (hK : IsCompact K) {A : ℝ → ℝ → F}
    (hA : ∀ θ ∈ K, ContinuousWithinAt (fun p : ℝ × ℝ => A p.1 p.2)
      (Set.Icc 0 1 ×ˢ Set.univ) (1, θ))
    (hbase : ∀ θ ∈ K, ContinuousAt (A 1) θ) :
    TendstoUniformlyOn A (A 1) (𝓝[Set.Icc 0 1] 1) K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hnear : ∀ θ ∈ K,
      ∀ᶠ p : ℝ × ℝ in (𝓝[Set.Icc 0 1] (1 : ℝ)) ×ˢ 𝓝 θ,
        dist (A 1 p.2) (A p.1 p.2) < ε := by
    intro θ hθ
    have hb : ContinuousAt (fun p : ℝ × ℝ => A 1 p.2) (1, θ) :=
      (hbase θ hθ).comp continuousAt_snd
    have hd := hb.continuousWithinAt.dist (hA θ hθ)
    have hh := hd.eventually (Iio_mem_nhds (by simpa using hε : dist (A 1 θ) (A 1 θ) < ε))
    simpa only [nhdsWithin_prod_eq, nhdsWithin_univ] using hh
  have hmem : ∀ᶠ p : ℝ × ℝ in (𝓝[Set.Icc 0 1] (1 : ℝ)) ×ˢ 𝓝ˢ K,
      dist (A 1 p.2) (A p.1 p.2) < ε := hK.mem_prod_nhdsSet_of_forall hnear
  exact hmem.curry.mono fun _ hr => hr.self_of_nhdsSet

end Yau.Blueprint.V03Proof
