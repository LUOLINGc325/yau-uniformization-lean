import Yau.Proofs.C05GradientFlowLoopChart
import Yau.Proofs.C05FreeContraction

/-! The actual flow homotopy transports the terminal chart contraction back to the original loop. -/
noncomputable section
open scoped Topology Manifold
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem loop_nullhomotopic_of_contracting_family (g : SmoothMetric M)
    (o : M.Carrier) (a r : ℝ) (ha : 0 < a) (hr : 0 < r)
    (F : ℝ → M.Carrier → M.Carrier)
    (hF0 : ∀ x ∈ gradientTrap g o r, F 0 x = x)
    (hFK : ∀ t, 0 ≤ t → ∀ x ∈ gradientTrap g o r, F t x ∈ gradientTrap g o r)
    (hcont : ContinuousOn (fun p : ℝ × M.Carrier => F p.1 p.2)
      (Set.Ici 0 ×ˢ gradientTrap g o r))
    (hcontract : ∀ t, 0 ≤ t → ∀ x ∈ gradientTrap g o r, ∀ y ∈ gradientTrap g o r,
      inducedDistance g.form (F t x) (F t y) ≤ Real.exp (-a * t) * inducedDistance g.form x y)
    {x : M.Carrier} (γ : Path x x) (hγ : ∀ u, γ u ∈ gradientTrap g o r) :
    γ.Homotopic (Path.refl x) := by
  classical
  let K := gradientTrap g o r
  obtain ⟨T, hT, c, ε, hε, hball, hcarry⟩ :=
    exists_time_carries_trap_into_convex_chart g o a r ha hr F hFK hcontract
  let inc : C(K, M.Carrier) := ⟨Subtype.val, continuous_subtype_val⟩
  let terminal : C(K, M.Carrier) :=
    ⟨fun z => F T z, hcont.comp_continuous (continuous_const.prodMk continuous_subtype_val)
      (fun z => ⟨hT, z.2⟩)⟩
  let H : inc.Homotopy terminal :=
    { toFun := fun p => F ((p.1 : ℝ) * T) p.2.1
      continuous_toFun := hcont.comp_continuous
        (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk
          (continuous_subtype_val.comp continuous_snd))
        (fun p => ⟨mul_nonneg p.1.2.1 hT, p.2.2⟩)
      map_zero_left := fun z => by
        change F (0 * T) z = z
        rw [zero_mul]
        exact hF0 z z.2
      map_one_left := fun z => by
        change F (1 * T) z = F T z
        rw [one_mul] }
  have hx : x ∈ K := by simpa only [γ.source] using hγ 0
  let xK : K := ⟨x, hx⟩
  let γK : Path xK xK :=
    { toFun := fun u => ⟨γ u, hγ u⟩
      continuous_toFun := γ.continuous.subtype_mk _
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  have hterminal : (γK.map terminal.continuous).Homotopic (Path.refl (terminal xK)) :=
    loop_nullhomotopic_in_convex_chart (γK.map terminal.continuous) c ε hε hball
      (fun u => (hcarry (γ u) (hγ u)).1) (fun u => (hcarry (γ u) (hγ u)).2)
  have Hnull := C05Aux.loop_nullhomotopic_of_map_homotopy H γK hterminal
  convert Hnull using 1 <;> ext u <;> rfl

end Yau.Proofs.C05GradientFlowAux
