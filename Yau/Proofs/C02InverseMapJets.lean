import Yau.Proofs.C02OpenCompositionJets
import Yau.Proofs.C02InverseMapJetMajorants

/-! The actual inverse-coordinate differential equation gives every jet
bound through the triangular numerical recursion. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverseCoordinateMap_jet_norm_le
    {O V : Set E} (hO : IsOpen O) (hV : IsOpen V)
    {g : E → E} {C : E → E →L[ℝ] E}
    (hg : ContDiffOn ℝ ∞ g O) (hC : ContDiffOn ℝ ∞ C V)
    (hMaps : MapsTo g O V)
    (hEquation : ∀ y ∈ O, fderiv ℝ g y = C (g y))
    (c : ℕ → ℝ) (hBound : ∀ m y, y ∈ V → ‖iteratedFDeriv ℝ m C y‖ ≤ c m)
    {x : E} (hx : x ∈ O) (R : ℝ) (hPosition : ‖g x‖ ≤ R) (m : ℕ) :
    ‖iteratedFDeriv ℝ m g x‖ ≤ inverseMapJetMajorant c R m := by
  let a := fun i => ‖iteratedFDeriv ℝ i g x‖
  have hInitial : a 0 ≤ |R| + 1 := by
    dsimp only [a]
    rw [norm_iteratedFDeriv_zero]
    linarith [le_abs_self R]
  have hEq : fderiv ℝ g =ᶠ[𝓝 x] C ∘ g := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact hEquation y hy
  apply inverseMapJetMajorant_dominates a c R (fun i => norm_nonneg _) hInitial _ m
  intro k
  calc
    a (k + 1) = ‖iteratedFDeriv ℝ k (fderiv ℝ g) x‖ := norm_iteratedFDeriv_fderiv.symm
    _ = ‖iteratedFDeriv ℝ k (C ∘ g) x‖ := by rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
    _ ≤ (k.factorial : ℝ) * finiteJetEnvelope c k * finiteJetEnvelope a k ^ k :=
      norm_iteratedFDeriv_comp_on_le hO hV hg hC hMaps hx k c a
        (fun i _ => hBound i (g x) (hMaps hx)) (fun i _ _ => le_refl _)

end Yau.Blueprint.C02Proof
