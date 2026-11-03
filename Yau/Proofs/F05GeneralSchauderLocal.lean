import Yau.Proofs.F05GeneralSourceBounds
import Yau.Proofs.F05SmoothSchauder
import Yau.Proofs.F05SmoothSlices
import Yau.Proofs.F05SmoothContinuity
import Yau.Proofs.F05GeneralLocal

/-! The nonconstant-profile local solution has a genuine full Schauder
bound with constants preceding all short endpoints. This retains the exact
regularity needed for the individual positive-time bootstrap. -/

open Set
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_schauder_nonlinear_local_general {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ) {S α : ℝ} (hS : 0 < S)
    (hh : MetricFamilySmooth h (Icc 0 S)) (hp : SmoothSpaceTime p (Icc 0 S))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S))
    (hα : 0 < α) (hα1 : α < 1)
    (hCompat : ∀ x, derivWithin (p x) (Icc 0 S) 0 =
      Real.exp (-p x 0)*laplacian (h 0) (fun y => p y 0) x+
        (1-Real.exp (-p x 0))*scalarCurvature (h 0) x) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ S ∧ δ ≤ 1 ∧ 0 < K ∧ ∀ (T : ℝ), 0 < T → T ≤ δ →
      ∃ w : M.Carrier → ℝ → ℝ,
        (∀ i, SchauderBound α (F05Q A i T) (pull A i w) K) ∧
        ContinuousOn (fun q : M.Carrier × ℝ => w q.1 q.2) (closure O ×ˢ Icc 0 T) ∧
        (∀ x ∈ closure O, w x 0 = p x 0) ∧
        (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = p x t) ∧
        ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
          derivWithin (w x) (Icc 0 T) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
            (1-Real.exp (-w x t))*scalarCurvature (h t) x := by
  obtain ⟨K,hK,hPBudget⟩ := F05_smooth_schauder_uniform hA p hS hp
  obtain ⟨B,hB,hCoeff⟩ := F05_background_holder_budgets hA h p hS hh hp hR
  obtain ⟨F₀,hF₀,hZero⟩ := F05_zero_source_small_general hA h p hS hh hp hR hCompat
  have hCompatT (T : ℝ) (hT : 0 < T) (hTS : T ≤ S) (x : M.Carrier) :
      derivWithin (p x) (Icc 0 T) 0 = Real.exp (-p x 0)*laplacian (h 0) (fun y => p y 0) x+
        (1-Real.exp (-p x 0))*scalarCurvature (h 0) x := by
    rw [F05_derivWithin_Icc_restrict hT hTS ⟨le_rfl,hT.le⟩
      ((F05_smooth_time_slice hp x).differentiableOn (by simp) 0 ⟨le_rfl,hS.le⟩)]
    exact hCompat x
  obtain ⟨δ,hδ,hδS,hδ1,hSolve⟩ := F05_nonlinear_local_general_from_background_bounds hA hχ h p hS hh hp
    hα hα1 hB hF₀ (fun T hT hTS i => F05_smooth_actual_chart_c2 hA hp hT hTS i)
    hCompatT (hCoeff α hα hα1) (hZero α hα hα1)
  refine ⟨δ,K+1,hδ,hδS,hδ1,by positivity,?_⟩
  intro T hT hTδ
  obtain ⟨z,hz,hEquation⟩ := hSolve T hT hTδ
  let w := fun x t => p x t+F05CanonicalJetFunction A χ α hT.le z x t
  have hSub : closure O ×ˢ Icc 0 T ⊆ univ ×ˢ Icc 0 S :=
    fun q hq => ⟨mem_univ _,hq.2.1,hq.2.2.trans (hTδ.trans hδS)⟩
  have hSubT : closure O ×ˢ Icc 0 T ⊆ univ ×ˢ Icc 0 T := fun q hq => ⟨mem_univ _,hq.2⟩
  refine ⟨w,?_,((F05_smooth_spacetime_continuousOn hp).mono hSub).add
    ((F05CanonicalJetFunction_continuousOn hA hχ α hT z).mono hSubT),?_,?_,hEquation⟩
  · intro i
    have hNorm : ‖(z.val i).val‖ ≤ 1 := (norm_le_pi_norm z.val i).trans hz
    have hZBudget := schauderBound_mono_const (F05CanonicalJetFunction_schauder hA hχ α hT z i) hNorm
    exact schauderBound_add (hPBudget α hα hα1 T hT (hTδ.trans hδS) i) hZBudget
  · intro x hx
    dsimp only [w]
    rw [F05CanonicalJetFunction_initial,add_zero]
  · intro x hx t ht
    dsimp only [w]
    rw [F05CanonicalJetFunction_lateral hA hχ α hT.le z hx ht,add_zero]

end Yau.Proofs.F05Aux
