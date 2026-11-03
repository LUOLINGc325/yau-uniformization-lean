import Yau.Proofs.D02DiscLevi
import Yau.Proofs.D02PlanarMaximum

/-! Actual smooth Levi-nonnegative functions obey the maximum principle
on the original closed discs, with one bound for the entire boundary family. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Metric
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

theorem complexOneEquiv_eq_smul (ζ : ℂ) :
    Yau.Proofs.B01Aux.complexOneEquiv ζ = ζ • (stdVec 0 : ComplexVector 1) := by
  ext i
  fin_cases i
  simp [Yau.Proofs.B01Aux.complexOneEquiv_apply, stdVec]

theorem smoothLevi_disc_lowerSupports {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hL : ∀ y, (levi u y).PosSemidef)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f)
    (a : ℂ) (ha : a ∈ ball (0 : ℂ) 1) :
    ∃ s : ℂ → ℝ, ContDiffAt ℝ 2 s a ∧ s a = u (f a) ∧
      (∀ᶠ z in 𝓝 a, s z ≤ u (f z)) ∧ 0 ≤ P02Aux.planarTrace s a := by
  let e := Yau.Proofs.B01Aux.complexOneEquiv
  let g : ComplexVector 1 → ℝ := fun w => u (discModelMap f w)
  have hEa : e a ∈ ball (0 : ComplexVector 1) 1 := by
    simpa only [mem_ball, dist_zero_right, e.norm_map] using ha
  obtain ⟨hc, hpos⟩ := smoothLevi_disc_model hu hL hf (e a) hEa
  have heR : ContDiff ℝ 2 (fun ζ : ℂ => e ζ) :=
    e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.restrict_scalars ℝ
  have hfun : (fun ζ => u (f ζ)) = g ∘ e := by
    funext ζ
    change u (f ζ) = u (f (e.symm (e ζ)))
    rw [e.symm_apply_apply]
  have hscalar : ContDiffAt ℝ 2 (fun ζ => u (f ζ)) a := by
    rw [hfun]
    exact hc.comp a heR.contDiffAt
  have hpoint (ζ : ℂ) : (0 : ComplexVector 1) + ζ • stdVec 0 = e ζ := by
    rw [zero_add, ← complexOneEquiv_eq_smul]
  have hfun' : (fun ζ => u (f ζ)) = (fun ζ => g (0 + ζ • stdVec 0)) := by
    funext ζ
    rw [hpoint]
    exact congrFun hfun ζ
  have hc' : ContDiffAt ℝ 2 g (0 + a • stdVec 0) := by
    rw [hpoint]
    exact hc
  refine ⟨fun ζ => u (f ζ), hscalar, rfl, Filter.Eventually.of_forall (fun _ => le_rfl), ?_⟩
  rw [hfun', P02Aux.planarTrace_complexAffine g 0 (stdVec 0) a hc', hpoint]
  exact mul_nonneg (by norm_num) (hpos (stdVec 0))

theorem smoothLevi_disc_maximum {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hL : ∀ y, (levi u y).PosSemidef)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) (B : ℝ)
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → u (f ζ) ≤ B) :
    ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → u (f ζ) ≤ B := by
  intro ζ hζ
  exact planar_maximum_of_lower_supports (fun z => u (f z))
    (smoothFn_disc_continuousOn hu hf) (smoothLevi_disc_lowerSupports hu hL hf) B hboundary ζ
      (by simpa only [mem_closedBall, dist_zero_right] using hζ)

/-- The bound is selected from K before any varying holomorphic disc. -/
theorem smoothLevi_uniformDisc_bound {n : ℕ} {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (hL : ∀ y, (levi u y).PosSemidef)
    {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : ℂ → M.Carrier, IsHolomorphicDisc f →
      (∀ ζ : ℂ, ‖ζ‖ = 1 → f ζ ∈ K) → ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → u (f ζ) ≤ B := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image (L18Aux.continuous_of_smoothFn hu).continuousOn
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right B 1), ?_⟩
  intro f hf hboundary
  apply smoothLevi_disc_maximum hu hL hf (max B 1)
  intro ζ hζ
  exact (hB (Set.mem_image_of_mem u (hboundary ζ hζ))).trans (le_max_left B 1)

end Yau.NodeProofs.D02Aux
