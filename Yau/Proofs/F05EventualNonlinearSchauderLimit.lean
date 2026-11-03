import Yau.Proofs.F05NonlinearSchauderLimit

/-! Early exhaustion members need not contain a fixed chart. Common
Schauder bounds and the exact nonlinear equation are therefore used only
eventually; a genuine tail makes both hypotheses simultaneous. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ}

def F05RelativeNonlinearEquation (ν : Option (RIdx n)) (r s T : ℝ)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (R v : Point n → ℝ) : Prop :=
  ∀ z ∈ region ν r ×ˢ Icc s T,
    F05RelT (Icc s T) v z = Real.exp (-v z)*
      ((∑ i,∑ j,a z i j*F05RelDD (region ν r) v z (realVec i) (realVec j))+
        ∑ i,b z i*F05RelD (region ν r) v z (realVec i))+(1-Real.exp (-v z))*R z

theorem F05_eventual_nonlinear_relative_schauder_limit (ν : Option (RIdx n))
    {r s T α C : ℝ} (hr : 0 < r) (hsT : s < T) (hα : 0 < α)
    {v : ℕ → Point n → ℝ} {vLim : Point n → ℝ}
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (R : Point n → ℝ)
    (hv : ∀ᶠ k in atTop, F05RelSchauder α (region ν r) (Icc s T) (v k) C)
    (hLim : TendstoUniformlyOn v vLim atTop (region ν r ×ˢ Icc s T))
    (hEq : ∀ᶠ k in atTop, F05RelativeNonlinearEquation ν r s T a b R (v k)) :
    F05RelSchauder α (region ν r) (Icc s T) vLim C ∧
      F05RelativeNonlinearEquation ν r s T a b R vLim := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hv.and hEq)
  have hMono : StrictMono (fun k : ℕ => k+N) := fun a b hab => Nat.add_lt_add_right hab N
  have hTail : TendstoUniformlyOn (fun k => v (k+N)) vLim atTop (region ν r ×ˢ Icc s T) :=
    fun U hU => hMono.tendsto_atTop.eventually (hLim U hU)
  exact F05_nonlinear_relative_schauder_limit ν hr hsT hα a b R
    (fun k => (hN (k+N) (by omega)).1) hTail
    (fun k z hz => (hN (k+N) (by omega)).2 z hz)

end Yau.Proofs.F05Aux
