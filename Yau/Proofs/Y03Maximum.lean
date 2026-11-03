import Yau.Blueprint.Alignment

/-! Elementary maximum principles for the real rectangles used in the strip argument. -/

open scoped Topology
open Filter Set

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

theorem secondDeriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hpos : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hmin := isLocalMin_of_deriv_deriv_pos hpos hmax.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmax, hmin] with y hymax hymin
    exact le_antisymm hymax hymin
  have hz := heq.deriv.deriv_eq
  have hz0 : deriv (deriv (fun _ : ℝ => f x)) x = 0 := by
    rw [deriv_const', deriv_const]
  rw [hz0] at hz
  exact (ne_of_gt hpos) hz

def axisLaplacian (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  deriv (deriv (fun x => f (x, z.2))) z.1 + deriv (deriv (fun y => f (z.1, y))) z.2

theorem axisLaplacian_nonpos_of_isLocalMax {f : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hmax : IsLocalMax f z) (hc : ContinuousAt f z) : axisLaplacian f z ≤ 0 := by
  have hx : IsLocalMax (fun x => f (x, z.2)) z.1 :=
    hmax.comp_continuous (continuousAt_id.prodMk continuousAt_const)
  have hy : IsLocalMax (fun y => f (z.1, y)) z.2 :=
    hmax.comp_continuous (continuousAt_const.prodMk continuousAt_id)
  exact add_nonpos (secondDeriv_nonpos_of_isLocalMax hx
    (hc.comp (continuousAt_id.prodMk continuousAt_const)))
    (secondDeriv_nonpos_of_isLocalMax hy
      (hc.comp (continuousAt_const.prodMk continuousAt_id)))

theorem rectangle_strict_maximum {f : ℝ × ℝ → ℝ} {a b c d B : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hc : ContinuousOn f (Icc a b ×ˢ Icc c d))
    (hlap : ∀ z ∈ Ioo a b ×ˢ Ioo c d, 0 < axisLaplacian f z)
    (hboundary : ∀ z ∈ Icc a b ×ˢ Icc c d,
      z.1 = a ∨ z.1 = b ∨ z.2 = c ∨ z.2 = d → f z ≤ B) :
    ∀ z ∈ Icc a b ×ˢ Icc c d, f z ≤ B := by
  obtain ⟨zmax, hzmax, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    ⟨(a, c), ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hcd⟩⟩⟩ hc
  have hmaxB : f zmax ≤ B := by
    by_cases hbdy : zmax.1 = a ∨ zmax.1 = b ∨ zmax.2 = c ∨ zmax.2 = d
    · exact hboundary zmax hzmax hbdy
    · have hxi : a < zmax.1 ∧ zmax.1 < b := by
        have hneA : zmax.1 ≠ a := fun heq => hbdy (Or.inl heq)
        have hneB : zmax.1 ≠ b := fun heq => hbdy (Or.inr (Or.inl heq))
        exact ⟨lt_of_le_of_ne hzmax.1.1 (Ne.symm hneA), lt_of_le_of_ne hzmax.1.2 hneB⟩
      have hyi : c < zmax.2 ∧ zmax.2 < d := by
        have hneC : zmax.2 ≠ c := fun heq => hbdy (Or.inr (Or.inr (Or.inl heq)))
        have hneD : zmax.2 ≠ d := fun heq => hbdy (Or.inr (Or.inr (Or.inr heq)))
        exact ⟨lt_of_le_of_ne hzmax.2.1 (Ne.symm hneC), lt_of_le_of_ne hzmax.2.2 hneD⟩
      have hnhds : Icc a b ×ˢ Icc c d ∈ 𝓝 zmax :=
        prod_mem_nhds (Icc_mem_nhds hxi.1 hxi.2) (Icc_mem_nhds hyi.1 hyi.2)
      have hlocal := hmax.isLocalMax hnhds
      have hnonpos := axisLaplacian_nonpos_of_isLocalMax hlocal (hc.continuousAt hnhds)
      exact False.elim ((not_lt_of_ge hnonpos) (hlap zmax ⟨hxi, hyi⟩))
  intro z hz
  exact (hmax hz).trans hmaxB

end Yau.Blueprint.Alignment.Y03Proof
