import Yau.Proofs.F05JetInitialSpatial

/-! The total physical jet functions have zero initial values everywhere;
their values outside the physical chart set are literal zeros. -/

open Set
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05LocalZeroFTCGraph_initial_total (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalZeroFTCGraph A i α hT) (z : Space n) :
    F05BCFFun u.val.1 (z,0) = 0 ∧ F05BCFFun u.val.2.1 (z,0) = 0 ∧
      F05BCFFun u.val.2.2.1.val.1 (z,0) = 0 ∧ F05BCFFun u.val.2.2.2.val.1 (z,0) = 0 := by
  classical
  by_cases hz : z ∈ F05D A i
  · rw [F05BCFFun_apply u.val.1 ⟨(z,0),hz,le_rfl,hT⟩,
      F05BCFFun_apply u.val.2.1 ⟨(z,0),hz,le_rfl,hT⟩,
      F05BCFFun_apply u.val.2.2.1.val.1 ⟨(z,0),hz,le_rfl,hT⟩,
      F05BCFFun_apply u.val.2.2.2.val.1 ⟨(z,0),hz,le_rfl,hT⟩]
    exact ⟨F05LocalZeroFTCGraph_initial_value A i α hT u ⟨z,hz⟩,
      F05LocalZeroFTCGraph_initial_gradient A i α hT u hz,
      F05LocalZeroFTCGraph_initial_hessian A i α hT u hz,
      F05LocalZeroFTCGraph_initial_time A i α hT u ⟨z,hz⟩⟩
  · have hOut : (z,0) ∉ F05Q A i T := fun h => hz h.1
    simp only [F05BCFFun,dite_eq_right hOut,and_self]

end Yau.Proofs.F05Aux
