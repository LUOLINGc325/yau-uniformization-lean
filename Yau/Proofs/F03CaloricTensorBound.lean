import Yau.Proofs.F03CaloricCompactJetBound
import Yau.Proofs.F03DirectionalTensor

/-! Full joint Fréchet tensors, uniformly on the fixed caloric source space. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem caloricRepresentative_iteratedFDeriv_smul
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (c : ℝ) (e : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB)
    (m : ℕ) (p : Point d) (hp : p ∈ O ×ˢ Ioo l r) :
    iteratedFDeriv ℝ m (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll (c • e)) p=
      c • iteratedFDeriv ℝ m (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e) p := by
  let R := caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll
  have hgerm : R (c • e) =ᶠ[𝓝 p] (fun q => c*R e q) := by
    filter_upwards [(hO.prod isOpen_Ioo).mem_nhds hp] with q hq
    exact caloricRepresentative_const_smul hd O l r lam upper hO hlr a b hAB hEll c e hq
  have hm : ContDiffAt ℝ m (R e) p :=
    ((caloricRepresentative_spec hd O l r lam upper hO hlr a b hAB hEll e).1.contDiffAt
      ((hO.prod isOpen_Ioo).mem_nhds hp)).of_le (by simp)
  rw [(hgerm.iteratedFDeriv ℝ m).eq_of_nhds]
  simpa only [R,smul_eq_mul] using (iteratedFDeriv_const_smul_apply' (a := c) hm)

theorem caloricRepresentative_compact_tensor_unit_bound
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (K : Set (Point d)) [CompactSpace K]
    [IsFiniteMeasure (volume.comap ((↑) : K → Point d))]
    (hKc : IsCompact K) (hreg : K=closure (interior K)) (hKD : K ⊆ O ×ˢ Ioo l r) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB,
      ‖e‖ ≤ 1 → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ m (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e) p‖ ≤ C := by
  let E := CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB
  let I := {e : E // ‖e‖ ≤ 1}
  let F : I → Point d → ℝ := fun e => caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e.val
  have hWords : ∀ w : List (Point d), ∃ C : ℝ, ∀ e : I, ∀ p ∈ K,
      |directionalWordDerivative (F e) w p| ≤ C := by
    intro w
    obtain ⟨C,hC,hbound⟩ := caloricRepresentative_compact_word_bound hd O l r lam upper hO hlr a b hAB hEll
      K hKc hreg hKD w
    exact ⟨C,fun e p hp => (hbound e.val p hp).trans
      ((mul_le_mul_of_nonneg_left e.property hC.le).trans_eq (mul_one C))⟩
  obtain ⟨C,hC⟩ := iteratedFDeriv_uniform_bound_of_words (hO.prod isOpen_Ioo) hKD F
    (fun e => (caloricRepresentative_spec hd O l r lam upper hO hlr a b hAB hEll e.val).1) hWords m
  exact ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun e he p hp => (hC ⟨e,he⟩ p hp).trans (le_max_right _ _)⟩

theorem caloricRepresentative_compact_tensor_bound
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (K : Set (Point d)) [CompactSpace K]
    [IsFiniteMeasure (volume.comap ((↑) : K → Point d))]
    (hKc : IsCompact K) (hreg : K=closure (interior K)) (hKD : K ⊆ O ×ˢ Ioo l r) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB,
      ∀ p ∈ K,
      ‖iteratedFDeriv ℝ m (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e) p‖ ≤ C*‖e‖ := by
  obtain ⟨C,hC,hbound⟩ := caloricRepresentative_compact_tensor_unit_bound hd O l r lam upper hO hlr a b hAB hEll
    K hKc hreg hKD m
  refine ⟨C,hC,?_⟩
  intro e p hp
  by_cases he : e=0
  · subst e
    have hz := caloricRepresentative_iteratedFDeriv_smul hd O l r lam upper hO hlr a b hAB hEll 0 0 m p (hKD hp)
    simp only [zero_smul] at hz
    rw [hz]
    simp
  · have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
    let c : ℝ := ‖e‖⁻¹
    have hc : 0 < c := inv_pos.mpr hn
    have heunit : ‖c • e‖ ≤ 1 := by
      rw [norm_smul,Real.norm_of_nonneg hc.le]
      dsimp [c]
      exact (inv_mul_cancel₀ (show ‖e.val‖ ≠ 0 from hn.ne')).le
    have hu := hbound (c • e) heunit p hp
    rw [caloricRepresentative_iteratedFDeriv_smul hd O l r lam upper hO hlr a b hAB hEll c e m p (hKD hp),
      norm_smul,Real.norm_of_nonneg hc.le] at hu
    have hdv : ‖iteratedFDeriv ℝ m (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e) p‖/‖e‖ ≤ C := by
      simpa only [c,div_eq_mul_inv,mul_comm] using hu
    exact (div_le_iff₀ hn).mp hdv

end Yau.Proofs.F03Aux
