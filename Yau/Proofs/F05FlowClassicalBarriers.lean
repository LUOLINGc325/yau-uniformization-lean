import Yau.Proofs.F05ClassicalBounds
import Yau.Proofs.F05FlowScalarSmooth
import Yau.Proofs.F05SmoothContinuity

/-! Actual classical solutions on the supplied flow satisfy the two original
barriers. Nonnegativity is proved, rather than assumed in comparison. -/

open Set
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_classical_barriers {O : Set (Pt X)} {A : AtlasData X.manifold}
    (hA : GenuineAtlas O A) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {T a : ℝ} (hT : 0 < T) (ha : 0 ≤ a)
    (w : STF X)
    (hCont : ContinuousOn (fun q : Pt X × ℝ => w q.1 q.2) (closure O ×ˢ Icc 0 T))
    (hC2 : ∀ i, C2 (F05Q A i T) (pull A i w))
    (hInitial : ∀ x ∈ closure O, w x 0 = a)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, 0 ≤ w x t ∧ w x t ≤ ρ x t+2*a)
    (hEquation : ∀ x ∈ O, ∀ t ∈ Ioc 0 T, derivWithin (w x) (Icc 0 T) t =
      scalarNonlinearRHS (scalarCurvature (h t) x) (laplacian (h t) (fun y => w y t) x) (w x t)) :
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T, 0 ≤ w x t ∧ w x t ≤ ρ x t+2*a := by
  have hh : MetricFamilySmooth h (Icc 0 T) := fun x a b =>
    (hloc.1.2.1 x a b).mono (fun q hq => ⟨hq.1,hq.2.1⟩)
  have hR := F05_flow_scalar_smooth o h U P ρ hloc hT
  have hZeroC2 (i : Fin A.count) : C2 (F05Q A i T) (pull A i (fun _ _ => 0)) := c2_zero _
  have hZeroSub (x : Pt X) (_ : x ∈ O) (t : ℝ) (_ : t ∈ Ioc 0 T) :
      derivWithin (fun _ => (0 : ℝ)) (Icc 0 T) t ≤ scalarNonlinearRHS (scalarCurvature (h t) x)
        (laplacian (h t) (fun _ => 0) x) 0 := by
    rw [Yau.LeafProofs.L18Aux.laplacian_const,scalarNonlinearRHS_zero]
    simp
  have hLower := F05_classical_comparison hA h hT hh hR (fun _ _ => 0) w continuousOn_const hCont hZeroC2 hC2
    (fun x hx => by change 0 ≤ w x 0; rw [hInitial x hx]; exact ha)
    (fun x hx t ht => (hBoundary x hx t ht).1) hZeroSub
    (fun x hx t ht => (hEquation x hx t ht).ge)
  let b := fun x t => ρ x t+2*a
  have hbSmooth : SmoothSpaceTime b (Icc 0 T) := fun x =>
    ((hloc.2.2.2.1 x).mono (fun q hq => ⟨hq.1,hq.2.1⟩)).add contDiffOn_const
  have hbCont : ContinuousOn (fun q : Pt X × ℝ => b q.1 q.2) (closure O ×ˢ Icc 0 T) :=
    (F05_smooth_spacetime_continuousOn hbSmooth).mono (fun q hq => ⟨mem_univ _,hq.2⟩)
  have hbC2 (i : Fin A.count) : C2 (F05Q A i T) (pull A i b) :=
    F05_smooth_actual_chart_c2 hA hbSmooth hT le_rfl i
  have hUpper := F05_classical_comparison hA h hT hh hR w b hCont hbCont hC2 hbC2
    (fun x hx => by
      change w x 0 ≤ ρ x 0+2*a
      rw [hInitial x hx,Yau.F04Proof.rho_initial o h U P ρ hloc x]
      linarith)
    (fun x hx t ht => (hBoundary x hx t ht).2)
    (fun x hx t ht => (hEquation x hx t ht).le)
    (fun x _ t ht => shifted_rho_supersolution o h U P ρ hloc T hT (2*a) x t ⟨ht.1.le,ht.2⟩)
  intro x hx t ht
  exact ⟨hLower x hx t ht,hUpper x hx t ht⟩

end Yau.Proofs.F05Aux
