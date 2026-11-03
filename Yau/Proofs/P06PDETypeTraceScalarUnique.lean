import Yau.Proofs.P06PDETypeTraceInitial
import Yau.Proofs.P06ScalarUniqueness

/-! The original smooth scalar initial class implies the original continuous
initial class on every manifold compact, so its existing PDE uniqueness applies. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff Manifold
namespace Yau.NodeProofs.P06Aux.PDETypeTrace
open Yau Yau.Blueprint
variable {n : ℕ} {M : ComplexManifold n}

 theorem scalarSmoothInitial_uniform_on_compact {u : ℝ → M.Carrier → ℝ}
    {f : M.Carrier → ℝ} (h : ScalarSmoothInitial u f)
    (K : Set M.Carrier) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ → ∀ x ∈ K, |u t x - f x| ≤ ε := by
  classical
  have hc (x : M.Carrier) : ∃ O : Set (ComplexVector n),
      IsOpen O ∧ {chartPt x x} ⊆ O ∧ closure O ⊆ chartTarget x ∧ IsCompact (closure O) :=
    exists_open_between_and_isCompact_closure isCompact_singleton
      (isOpen_extChartAt_target (I := ComplexModel n) x)
      (singleton_subset_iff.mpr (mem_extChartAt_target x))
  choose O hO hxO hOt hOc using hc
  let W : M.Carrier → Set M.Carrier := fun x =>
    (extChartAt (ComplexModel n) x).source ∩ chartPt x ⁻¹' O x
  have hW (x : M.Carrier) : W x ∈ 𝓝 x := by
    exact inter_mem (extChartAt_source_mem_nhds (I := ComplexModel n) x)
      ((continuousAt_extChartAt (I := ComplexModel n) x).preimage_mem_nhds
        ((hO x).mem_nhds (hxO x (mem_singleton _))))
  obtain ⟨s, hsK, hsW⟩ := hK.elim_nhds_subcover W (fun x hx => hW x)
  have he (x : M.Carrier) : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ W x, |u t y - f y| ≤ ε := by
    obtain ⟨δ, hδ, hh⟩ := h.2 x (closure (O x)) (hOc x) (hOt x) 0 ε hε
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    intro y hy
    have hz := hh t ht.1 ht.2 (chartPt x y) (subset_closure hy.2)
    have hi : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy.1
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, inChart, hi] using hz.le
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ K, |u t x - f x| ≤ ε := by
    filter_upwards [(Finset.eventually_all _).mpr (fun x (hx : x ∈ s) => he x)] with t ht
    intro x hx
    obtain ⟨y, hys, hxy⟩ := mem_iUnion₂.mp (hsW hx)
    exact ht y hys x hxy
  obtain ⟨δ, hδ, hh⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hall
  exact ⟨δ, hδ, fun t ht htδ => hh ⟨ht, htδ⟩⟩

 theorem boundedScalarHeat_continuousInitial {g : HermitianField M}
    {f : M.Carrier → ℝ} {u : ℝ → M.Carrier → ℝ}
    (hu : IsBoundedScalarHeat g f u) : IsContinuousInitialScalarHeat g f u := by
  refine ⟨fun x => congrFun hu.2.1.1 x, hu.1, hu.2.2.2, ?_, ?_⟩
  · intro T hT
    obtain ⟨B, hB, hh⟩ := hu.2.2.1 T hT
    exact ⟨B, hB.le, hh⟩
  · exact scalarSmoothInitial_uniform_on_compact hu.2.1

 theorem boundedScalarHeat_unique (X : KahlerManifold n) (f : Pt X → ℝ)
    (u v : ℝ → Pt X → ℝ) (hu : IsBoundedScalarHeat X.metric.form f u)
    (hv : IsBoundedScalarHeat X.metric.form f v) (t : ℝ) (ht : 0 ≤ t) : u t = v t := by
  rcases ht.eq_or_lt with rfl | ht
  · exact hu.2.1.1.trans hv.2.1.1.symm
  exact continuousInitialScalarHeat_unique X f u v
    (boundedScalarHeat_continuousInitial hu) (boundedScalarHeat_continuousInitial hv) t ht

end Yau.NodeProofs.P06Aux.PDETypeTrace
