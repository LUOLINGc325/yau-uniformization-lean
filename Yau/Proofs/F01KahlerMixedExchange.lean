import Yau.Proofs.F01WirtingerCoordinateChain

/-! The second diagonal derivative exchange follows from actual first
Kähler jets, Hermitian symmetry and the native mixed-derivative commutation. -/
noncomputable section
open Set Filter
open scoped Matrix ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem wirt_eq_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} {z : E} (h : f =ᶠ[𝓝 z] g) (v : E) : wirt f z v = wirt g z v := by
  unfold wirt
  rw [h.fderiv_eq]

theorem wirtBar_eq_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} {z : E} (h : f =ᶠ[𝓝 z] g) (v : E) : wirtBar f z v = wirtBar g z v := by
  unfold wirtBar
  rw [h.fderiv_eq]

theorem hermitian_wirtBar_symm_of_wirt_symm
    (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ w, (H w).IsHermitian) (z : ComplexVector n)
    (hsym : ∀ p q l, wirt (fun y => H y p q) z (stdVec l) =
      wirt (fun y => H y p l) z (stdVec q)) (i j k : Fin n) :
    wirtBar (fun w => H w i j) z (stdVec k) =
      wirtBar (fun w => H w k j) z (stdVec i) := by
  have hstar (p q : Fin n) : (fun w => H w p q) = (fun w => star (H w q p)) := by
    funext w
    exact (hH w).apply p q |>.symm
  rw [hstar i j, hstar k j, L14Aux.wirtBar_star, L14Aux.wirtBar_star]
  exact congrArg star (hsym j i k)

theorem kahler_diagonal_mixed_exchange
    (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ w, (H w).IsHermitian) {S : Set (ComplexVector n)} (hS : IsOpen S)
    {z : ComplexVector n} (hz : z ∈ S)
    (hsmooth : ∀ i j, ContDiffAt ℝ 2 (fun w => H w i j) z)
    (hsym : ∀ w ∈ S, ∀ p q l, wirt (fun y => H y p q) w (stdVec l) =
      wirt (fun y => H y p l) w (stdVec q)) (i a : Fin n) :
    wirt (fun w => wirtBar (fun y => H y i i) w (stdVec a)) z (stdVec a) =
      wirt (fun w => wirtBar (fun y => H y a a) w (stdVec i)) z (stdVec i) := by
  have hbar : (fun w => wirtBar (fun y => H y i i) w (stdVec a)) =ᶠ[𝓝 z]
      (fun w => wirtBar (fun y => H y a i) w (stdVec i)) := by
    filter_upwards [hS.mem_nhds hz] with w hw
    exact hermitian_wirtBar_symm_of_wirt_symm H hH w (hsym w hw) i i a
  have hunbar : (fun w => wirt (fun y => H y a i) w (stdVec a)) =ᶠ[𝓝 z]
      (fun w => wirt (fun y => H y a a) w (stdVec i)) := by
    filter_upwards [hS.mem_nhds hz] with w hw
    exact hsym w hw a i a
  rw [wirt_eq_of_eventuallyEq hbar,
    L14Aux.wirt_wirtBar_comm (fun y => H y a i) z (hsmooth a i),
    wirtBar_eq_of_eventuallyEq hunbar,
    ← L14Aux.wirt_wirtBar_comm (fun y => H y a a) z (hsmooth a a)]

end Yau.NodeProofs.F01Aux
