import Yau.LeafProofs.L05ChuCutoffSource

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem chu_spatial_holder_any_time {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {gamma C : ℝ} (hg : 0 < gamma) {v : Space n → V}
    (hv : HolderBound gamma (cylinder Set.univ 0 0) (fun p => v p.1) C)
    (Q : Set (Point n)) : HolderBound gamma Q (fun p => v p.1) C := by
  have hmem (x : Space n) : (x,0) ∈ cylinder (n := n) Set.univ 0 0 :=
    ⟨Set.mem_univ _,le_rfl,le_rfl⟩
  refine ⟨hv.1,fun p hp => hv.2.1 (p.1,0) (hmem _),?_⟩
  intro p hp q hq
  have hh := hv.2.2 (p.1,0) (hmem _) (q.1,0) (hmem _)
  simp only [holderWeight,sub_self,abs_zero,Real.zero_rpow (show gamma/2 ≠ 0 by linarith),add_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)) hv.1)

theorem chu_spatial_cutoff_budgets {n : ℕ} {gamma : ℝ} (hg : 0 < gamma) (hg1 : gamma < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ) (hh : 0 < h), h ≤ 1 → ∀ (c : Space n) (l r : ℝ),
      let phi : Space n → ℝ := L16Aux.innerPatchBump h hh c
      HolderBound gamma (cylinder Set.univ l r) (fun p => phi p.1) (2*(h⁻¹*C)*h^(1-gamma)) ∧
      HolderBound gamma (cylinder Set.univ l r) (fun p => fderiv ℝ phi p.1) (2*((h⁻¹)^2*C)*h^(1-gamma)) ∧
      HolderBound gamma (cylinder Set.univ l r) (fun p => fderiv ℝ (fderiv ℝ phi) p.1) (2*((h⁻¹)^3*C)*h^(1-gamma)) := by
  obtain ⟨C,hC,hRule⟩ := L16Aux.patchBumps_uniform_three_holderBounds (n := n) hg hg1
  refine ⟨C,hC,?_⟩
  intro h hh hh1 c l r
  have hs := hRule h hh hh1 0 c (L16Aux.innerPatchBump h hh c) (Or.inl rfl)
  exact ⟨chu_spatial_holder_any_time hg hs.1 _,chu_spatial_holder_any_time hg hs.2.1 _,
    chu_spatial_holder_any_time hg hs.2.2 _⟩

theorem chu_innerPatchBump_unit {n : ℕ} {h : ℝ} (hh : 0 < h) (c x : Space n) :
    |L16Aux.innerPatchBump h hh c x| ≤ 1 := by
  rw [abs_of_nonneg (L16Aux.innerPatchBump h hh c).nonneg]
  exact (L16Aux.innerPatchBump h hh c).le_one

theorem chu_innerPatchBump_support {n : ℕ} {h : ℝ} (hh : 0 < h) (c : Space n) :
    tsupport (L16Aux.innerPatchBump h hh c : Space n → ℝ) ⊆ Metric.ball c (2*h) := by
  rw [(L16Aux.innerPatchBump h hh c).tsupport_eq]
  intro x hx
  have hnorm : dist x c ≤ 3*h/2 := hx
  exact Metric.mem_ball.mpr (hnorm.trans_lt (by linarith only [hh]))

end Yau.LeafProofs.L05Aux
