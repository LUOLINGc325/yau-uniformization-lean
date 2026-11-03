import Yau.Proofs.V01TraceCompact

/-! V01 scratch source: a convergent Hermitian family with a positive limit
has one uniform positive lower bound. The zero-dimensional case is explicit. -/

noncomputable section
open Set Filter Matrix
open scoped Topology Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Yau.Blueprint.V01Proof

variable {n : ℕ}

theorem real_algebraMap_matrix (r : ℝ) :
    algebraMap ℝ (Herm n) r = (r : ℂ) • (1 : Herm n) := by
  rw [Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

theorem exists_pos_lower_bound_of_posDef {C : Herm n} (hC : C.PosDef) :
    ∃ a : ℝ, 0 < a ∧ (C - (a : ℂ) • (1 : Herm n)).PosSemidef := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨1, zero_lt_one, ?_⟩
    convert (Matrix.PosSemidef.zero : (0 : Herm 0).PosSemidef) using 1
    ext i j
    exact Fin.elim0 i
  · let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    obtain ⟨a, ha, hbound⟩ :=
      (CFC.exists_pos_algebraMap_le_iff C hC.isHermitian.isSelfAdjoint).mpr
        (fun x hx => hC.isStrictlyPositive.spectrum_pos hx)
    refine ⟨a, ha, ?_⟩
    simpa only [Matrix.le_iff, real_algebraMap_matrix] using hbound

theorem half_lower_bound_of_norm_sub_le
    {C D : Herm n} (hC : C.IsHermitian) (hD : D.IsHermitian)
    {a : ℝ} (hCa : (C - (a : ℂ) • (1 : Herm n)).PosSemidef)
    (hDC : ‖D - C‖ ≤ a / 2) :
    (D - ((a / 2 : ℝ) : ℂ) • (1 : Herm n)).PosSemidef := by
  have hδ : (D - C).IsHermitian := hD.sub hC
  have hδbound : (D - C + (‖D - C‖ : ℂ) • (1 : Herm n)).PosSemidef := by
    simpa only [Matrix.le_iff, sub_neg_eq_add, real_algebraMap_matrix] using
      IsSelfAdjoint.neg_algebraMap_norm_le_self (D - C) hδ.isSelfAdjoint
  have hmargin : (((a / 2 - ‖D - C‖ : ℝ) : ℂ) • (1 : Herm n)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.mpr hDC)
  have hsplit : (a : ℂ) • (1 : Herm n) =
      ((a / 2 : ℝ) : ℂ) • (1 : Herm n) + ((a / 2 : ℝ) : ℂ) • (1 : Herm n) := by
    rw [← add_smul]
    congr 1
    push_cast
    ring
  have hmargin_eq : ((a / 2 - ‖D - C‖ : ℝ) : ℂ) • (1 : Herm n) =
      ((a / 2 : ℝ) : ℂ) • (1 : Herm n) - (‖D - C‖ : ℂ) • (1 : Herm n) := by
    rw [Complex.ofReal_sub, sub_smul]
  convert (hCa.add hδbound).add hmargin using 1
  rw [hsplit, hmargin_eq]
  abel

theorem eventually_uniform_pos_lower_bound
    (C : ℕ → Herm n) {C₀ : Herm n} (hC₀ : C₀.PosDef)
    (hlim : Tendsto C atTop (𝓝 C₀))
    (hHerm : ∀ᶠ m in atTop, (C m).IsHermitian) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ m in atTop, (C m - (c : ℂ) • (1 : Herm n)).PosSemidef := by
  obtain ⟨a, ha, hCa⟩ := exists_pos_lower_bound_of_posDef hC₀
  refine ⟨a / 2, half_pos ha, ?_⟩
  have hnorm : Tendsto (fun m => ‖C m - C₀‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hlim.sub (tendsto_const_nhds (x := C₀))).norm
  have hsmall : ∀ᶠ m in atTop, ‖C m - C₀‖ < a / 2 :=
    hnorm.eventually (gt_mem_nhds (half_pos ha))
  filter_upwards [hHerm, hsmall] with m hmHerm hmSmall
  exact half_lower_bound_of_norm_sub_le hC₀.isHermitian hmHerm hCa hmSmall.le

theorem posDef_of_pos_lower_bound {C : Herm n} {c : ℝ} (hc : 0 < c)
    (hC : (C - (c : ℂ) • (1 : Herm n)).PosSemidef) : C.PosDef := by
  have hI : ((c : ℂ) • (1 : Herm n)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hc)
  convert hI.add_posSemidef hC using 1
  abel

theorem eventually_posDef_of_tendsto
    (C : ℕ → Herm n) {C₀ : Herm n} (hC₀ : C₀.PosDef)
    (hlim : Tendsto C atTop (𝓝 C₀))
    (hHerm : ∀ᶠ m in atTop, (C m).IsHermitian) :
    ∀ᶠ m in atTop, (C m).PosDef := by
  obtain ⟨c, hc, hbound⟩ := eventually_uniform_pos_lower_bound C hC₀ hlim hHerm
  exact hbound.mono (fun _ hm => posDef_of_pos_lower_bound hc hm)

end Yau.Blueprint.V01Proof
