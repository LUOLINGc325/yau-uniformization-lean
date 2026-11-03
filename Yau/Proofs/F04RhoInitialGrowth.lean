import Yau.Proofs.F04FlowRhoLp

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint
variable {n : ℕ}

/-- The actual original rho has a uniform linear initial-time bound on
 each compact physical set. The constant is selected before x and t from
 the actual continuous scalar curvature and the true closed-time derivative. -/
theorem flow_rho_compact_initial_growth
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S : ℝ} (hS : 0 < S)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ t ∈ Icc 0 S, |ρ x t| ≤ C * t := by
  have hRc := flow_scalarCurvature_continuousOn_closed X o h U P ρ hloc hS
  obtain ⟨C, hC, hCb⟩ := compact_scalar_profile_bound hS.le
    (fun x t => scalarCurvature (h t) x) hRc K hK
  refine ⟨C, hC, ?_⟩
  intro x hx t ht
  have hd (s : ℝ) (hs : s ∈ Icc 0 S) :=
    rho_hasDerivWithinAt_Icc o h U P ρ hloc S x s hs
  have hb (s : ℝ) (hs : s ∈ Icc 0 S) : ‖scalarCurvature (h s) x‖ ≤ C := by
    simpa only [timeClamp_eq_of_mem S hS.le hs] using hCb x hx s
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc 0 S)
    (show (0 : ℝ) ∈ Icc 0 S from ⟨le_rfl, hS.le⟩) ht
  simpa only [rho_initial o h U P ρ hloc x, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] using hm

/-- Every actual nonnegative function dominated by the supplied rho
 inherits the same uniform compact O(t) bound without a derivative inlet. -/
theorem rho_dominated_compact_initial_growth
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S : ℝ} (hS : 0 < S)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Pt X → ℝ → ℝ,
      (∀ x ∈ K, ∀ t ∈ Icc 0 S, 0 ≤ w x t ∧ w x t ≤ ρ x t) →
      ∀ x ∈ K, ∀ t ∈ Icc 0 S, |w x t| ≤ C * t := by
  obtain ⟨C, hC, hb⟩ := flow_rho_compact_initial_growth X o h U P ρ hloc hS K hK
  refine ⟨C, hC, ?_⟩
  intro w hw x hx t ht
  rw [abs_of_nonneg (hw x hx t ht).1]
  exact (hw x hx t ht).2.trans ((le_abs_self _).trans (hb x hx t ht))

end Yau.F04Proof
