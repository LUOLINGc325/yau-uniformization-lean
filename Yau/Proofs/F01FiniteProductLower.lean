import spec.CHAIN.CONTRACTS

/-! A positive product and a common upper bound give a quantitative lower
bound for each actual factor, including the empty index type. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finite_factor_lower_of_product (values : ι → ℝ) {C d : ℝ}
    (hC : 1 ≤ C) (hv0 : ∀ i, 0 ≤ values i) (hvC : ∀ i, values i ≤ C)
    (hd : d ≤ ∏ i, values i) (i : ι) : d / C ^ Fintype.card ι ≤ values i := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hothers : (∏ j ∈ Finset.univ.erase i, values j) ≤ C ^ Fintype.card ι := by
    calc
      _ ≤ ∏ j ∈ Finset.univ.erase i, C :=
        Finset.prod_le_prod₀ (fun j _ => hv0 j) (fun j _ => hvC j)
      _ ≤ ∏ j : ι, C := Finset.prod_le_prod_of_subset_of_one_le₀
        (Finset.erase_subset i Finset.univ) (fun _ _ => hC0.le) (fun _ _ _ => hC)
      _ = _ := by simp
  have hprod : (∏ j, values j) ≤ values i * C ^ Fintype.card ι := by
    rw [← Finset.prod_erase_mul Finset.univ values (Finset.mem_univ i)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hothers (hv0 i)
  exact (div_le_iff₀ (pow_pos hC0 _)).mpr (hd.trans hprod)

end Yau.NodeProofs.F01Aux
