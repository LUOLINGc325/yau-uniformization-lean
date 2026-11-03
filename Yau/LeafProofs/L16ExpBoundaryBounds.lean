import Yau.LeafProofs.L16ExpBoundaryErrorEquation

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

/-- Coefficient and source constants are selected from the fixed compact data. -/
theorem compact_coefficient_source_bounds {n : ℕ} {O : Set (Space n)}
    (hO : SmoothDomain O) {T : ℝ} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {R : Point n → ℝ}
    (hab : SmoothCoefficients (cylinder (closure O) 0 T) a b)
    (hR : ContDiffOn ℝ ∞ R (cylinder (closure O) 0 T)) :
    ∃ A₀ b₀ R₀ : ℝ, 0 < A₀ ∧ 0 < b₀ ∧ 0 < R₀ ∧
      (∀ z ∈ cylinder (closure O) 0 T, ∀ i j, |a z i j| ≤ A₀) ∧
      (∀ z ∈ cylinder (closure O) 0 T, ∀ i, |b z i| ≤ b₀) ∧
      ∀ z ∈ cylinder (closure O) 0 T, |R z| ≤ R₀ := by
  classical
  have hK : IsCompact (cylinder (closure O) 0 T) := hO.2.2.1.prod isCompact_Icc
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn hab.1.continuousOn
  have hEach (i : Yau.RIdx n) : ∃ C : ℝ, ∀ z ∈ cylinder (closure O) 0 T, |b z i| ≤ C := by
    simpa only [Real.norm_eq_abs] using hK.exists_bound_of_continuousOn (hab.2 i).continuousOn
  choose C hC using hEach
  obtain ⟨F,hF⟩ := hK.exists_bound_of_continuousOn hR.continuousOn
  refine ⟨1+|A|,1+∑ i, |C i|,1+|F|,by positivity,by positivity,by positivity,?_,?_,?_⟩
  · intro z hz i j
    exact (L16Aux.frobenius_entry_abs_le _ i j).trans
      ((hA z hz).trans (by linarith [le_abs_self A]))
  · intro z hz i
    have hi : |C i| ≤ ∑ j, |C j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)
    exact (hC i z hz).trans (by linarith [le_abs_self (C i)])
  · intro z hz
    have hh : |R z| ≤ F := by simpa only [Real.norm_eq_abs] using hF z hz
    exact hh.trans (by linarith [le_abs_self F])

theorem abs_div_bound {x q m A : ℝ} (hm : 0 < m) (hq : m ≤ q)
    (hA : 0 ≤ A) (hx : |x| ≤ A) : |x/q| ≤ A/m := by
  have hqpos : 0 < q := hm.trans_le hq
  rw [abs_div,abs_of_pos hqpos]
  exact (div_le_div_of_nonneg_right hx hqpos.le).trans
    (div_le_div_of_nonneg_left hA hm hq)

/-- A pointwise forcing bound uses value bounds and the fixed data jets only. -/
theorem log_error_source_bound {n : ℕ} {a : Point n → Mat n}
    {b : Point n → Yau.RIdx n → ℝ} {R P q : Point n → ℝ}
    {Q : Set (Point n)} {z : Point n} {m A₀ b₀ R₀ P₁ P₂ : ℝ}
    (hm : 0 < m) (hq : m ≤ q z)
    (hA₀ : 0 ≤ A₀) (hb₀ : 0 ≤ b₀) (hR₀ : 0 ≤ R₀)
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (ha : ∀ i j, |a z i j| ≤ A₀) (hb : ∀ i, |b z i| ≤ b₀) (hR : |R z| ≤ R₀)
    (hPt : |timeD Q P z| ≤ P₁)
    (hPD : ∀ i, |spatialD P z (Yau.realVec i)| ≤ P₁)
    (hPDD : ∀ i j, |spatialDD P z (Yau.realVec i) (Yau.realVec j)| ≤ P₂) :
    |(1-1/q z)*R z-timeD Q P z +
        (∑ i, ∑ j, (a z i j/q z)*spatialDD P z (Yau.realVec i) (Yau.realVec j)) +
        ∑ i, (b z i/q z)*spatialD P z (Yau.realVec i)| ≤
      (1+1/m)*R₀+P₁+(∑ _i : Yau.RIdx n, ∑ _j : Yau.RIdx n, (A₀/m)*P₂) +
        ∑ _i : Yau.RIdx n, (b₀/m)*P₁ := by
  have hqpos : 0 < q z := hm.trans_le hq
  have hf : |(1-1/q z)*R z| ≤ (1+1/m)*R₀ := by
    rw [abs_mul]
    apply mul_le_mul _ hR (abs_nonneg _) (by positivity)
    have hi := one_div_le_one_div_of_le hm hq
    have ht := abs_sub (1 : ℝ) (1/q z)
    simp only [abs_one,abs_of_pos (one_div_pos.mpr hqpos)] at ht
    exact ht.trans (add_le_add le_rfl hi)
  have hAA : |∑ i, ∑ j, (a z i j/q z)*spatialDD P z (Yau.realVec i) (Yau.realVec j)| ≤
      ∑ _i : Yau.RIdx n, ∑ _j : Yau.RIdx n, (A₀/m)*P₂ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [abs_mul]
    exact mul_le_mul (abs_div_bound hm hq hA₀ (ha i j)) (hPDD i j)
      (abs_nonneg _) (by positivity)
  have hbb : |∑ i, (b z i/q z)*spatialD P z (Yau.realVec i)| ≤
      ∑ _i : Yau.RIdx n, (b₀/m)*P₁ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul]
    exact mul_le_mul (abs_div_bound hm hq hb₀ (hb i)) (hPD i)
      (abs_nonneg _) (by positivity)
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add hf hPt)) hAA)) hbb)

end Yau.LeafProofs.L16ExpBoundaryAux
