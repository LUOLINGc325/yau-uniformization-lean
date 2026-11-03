import Yau.Proofs.C01LocalRicciCoercivity

/-! A finite genuine chart-neighborhood cover supplies one positive
Ricci coercivity constant on each original compact set at time one. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_compact_ricci_coercivity_one
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : ComplexVector n,
      c * matrixQuadraticReal (gMat (h 1) x) v ≤ matrixQuadraticReal (ricci (h 1) x) v := by
  classical
  by_cases hKne : K.Nonempty
  · choose c hc O hO hxO hbound using
      (fun x : Pt X => localizedFlow_local_ricci_coercivity_one hflow hjoint x)
    have hcover : K ⊆ ⋃ x, O x := by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hxO x⟩
    obtain ⟨F, hF⟩ := hK.elim_finite_subcover O hO hcover
    have hFne : F.Nonempty := by
      obtain ⟨x, hx⟩ := hKne
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hF hx)
      obtain ⟨hyF, _⟩ := Set.mem_iUnion.mp hy
      exact ⟨y, hyF⟩
    let cK := (F.image c).min' (hFne.image c)
    have hcK : 0 < cK := by
      obtain ⟨x, _hx, hxeq⟩ := Finset.mem_image.mp ((F.image c).min'_mem (hFne.image c))
      have hp := hc x
      rw [hxeq] at hp
      exact hp
    have hcle (y : Pt X) (hy : y ∈ F) : cK ≤ c y :=
      Finset.min'_le (F.image c) (c y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    refine ⟨cK, hcK, ?_⟩
    intro x hx v
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hF hx)
    obtain ⟨hyF, hyO⟩ := Set.mem_iUnion.mp hy
    have hqH : 0 ≤ matrixQuadraticReal (gMat (h 1) x) v := by
      have hp := (Complex.nonneg_iff.mp
        ((Yau.Blueprint.Alignment.Y03Proof.hMat_posDef (h 1) x (chartPt x x)
          (mem_extChartAt_target (I := ComplexModel n) x)).posSemidef.dotProduct_mulVec_nonneg
            (WithLp.ofLp v))).1
      simpa only [matrixQuadraticReal, gMat] using hp
    exact (mul_le_mul_of_nonneg_right (hcle y hyF) hqH).trans (hbound y x hyO v)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exact (hKne ⟨x, hx⟩).elim

end Yau.NodeProofs.C01Aux
