import Yau.LeafProofs.L16Scaling

/-! Uniform Holder estimates for the finite normalized L16 source cutoffs. -/

open Filter
open scoped Topology ContDiff
noncomputable section

namespace Yau.LeafProofs.L16Aux

open Yau.Parabolic

theorem holderBound_mono_const {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C D : ℝ} {Q : Set (Point n)} {f : Point n → V}
    (hf : HolderBound α Q f C) (hCD : C ≤ D) : HolderBound α Q f D := by
  refine ⟨hf.1.trans hCD,fun p hp => (hf.2.1 p hp).trans hCD,?_⟩
  intro p hp q hq
  exact (hf.2.2 p hp q hq).trans (mul_le_mul_of_nonneg_right hCD
    (by dsimp [holderWeight]; positivity))

theorem inverse_norm_le_four_of_lower_quarter {z : ℝ} (hz : (1/4 : ℝ) ≤ z) :
    ‖z⁻¹‖ ≤ 4 := by
  have hz0 : 0 < z := lt_of_lt_of_le (by norm_num) hz
  rw [norm_inv,Real.norm_eq_abs,abs_of_pos hz0]
  calc
    z⁻¹ = 1/z := (one_div _).symm
    _ ≤ 1/(1/4 : ℝ) := one_div_le_one_div_of_le (by norm_num) hz
    _ = 4 := by norm_num

theorem holderBound_inverse_of_lower_quarter {n : ℕ} {α D : ℝ}
    {Q : Set (Point n)} {d : Point n → ℝ} (hd : HolderBound α Q d D)
    (hLower : ∀ p ∈ Q, (1/4 : ℝ) ≤ d p) :
    HolderBound α Q (fun p => (d p)⁻¹) (4+16*D) := by
  have hInv : ∀ p ∈ Q, ‖(d p)⁻¹‖ ≤ 4 :=
    fun p hp => inverse_norm_le_four_of_lower_quarter (hLower p hp)
  refine ⟨by linarith [hd.1],fun p hp => (hInv p hp).trans (by linarith [hd.1]),?_⟩
  intro p hp q hq
  have hp0 : 0 < d p := lt_of_lt_of_le (by norm_num) (hLower p hp)
  have hq0 : 0 < d q := lt_of_lt_of_le (by norm_num) (hLower q hq)
  have hW : 0 ≤ holderWeight α p q := by dsimp [holderWeight]; positivity
  calc
    ‖(d p)⁻¹-(d q)⁻¹‖ = ‖(d p)⁻¹‖*‖d p-d q‖*‖(d q)⁻¹‖ := by
      rw [inv_sub_inv' hp0.ne' hq0.ne',norm_mul,norm_mul,norm_sub_rev (d q) (d p)]
    _ ≤ 4*(D*holderWeight α p q)*4 := by
      apply mul_le_mul
        (mul_le_mul (hInv p hp) (hd.2.2 p hp q hq) (norm_nonneg _) (by norm_num))
        (hInv q hq) (norm_nonneg _)
        (mul_nonneg (by norm_num) (mul_nonneg hd.1 hW))
    _ = (16*D)*holderWeight α p q := by ring
    _ ≤ (4+16*D)*holderWeight α p q :=
      mul_le_mul_of_nonneg_right (by linarith) hW

theorem patchDenominator_interval_lipschitz (M : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ z ∈ Set.Icc 0 M, ∀ w ∈ Set.Icc 0 M,
      ‖patchDenominator z-patchDenominator w‖ ≤ L*‖z-w‖ := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ patchDenominator) :=
    patchDenominator_contDiff.fderiv_right (by simp)
  obtain ⟨A,hA⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) M)).exists_bound_of_continuousOn
    hD.continuous.continuousOn
  let L : ℝ := 1+|A|
  refine ⟨L,by dsimp [L]; positivity,?_⟩
  intro z hz w hw
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.Icc 0 M)
    (fun x _ => patchDenominator_contDiff.differentiable (by simp) x)
    (fun x hx => (hA x hx).trans (by dsimp [L]; linarith [le_abs_self A]))
    (convex_Icc _ _) hw hz

theorem holderBound_patchDenominator {n : ℕ} {α F M L : ℝ}
    {Q : Set (Point n)} {Z : Point n → ℝ} (hZ : HolderBound α Q Z F)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hRange : ∀ p ∈ Q, Z p ∈ Set.Icc 0 M)
    (hLip : ∀ z ∈ Set.Icc 0 M, ∀ w ∈ Set.Icc 0 M,
      ‖patchDenominator z-patchDenominator w‖ ≤ L*‖z-w‖) :
    HolderBound α Q (fun p => patchDenominator (Z p)) ((M+1)+L*F) := by
  have hM1 : 0 ≤ M+1 := by linarith
  have hLF : 0 ≤ L*F := mul_nonneg hL hZ.1
  refine ⟨add_nonneg hM1 hLF,?_,?_⟩
  · intro p hp
    have hZp := hRange p hp
    rw [Real.norm_eq_abs,abs_of_pos (patchDenominator_pos hZp.1)]
    have hD : patchDenominator (Z p) ≤ M+1 := by
      have hχ := Real.smoothTransition.nonneg (4*Z p-1)
      dsimp only [patchDenominator]
      linarith [hZp.2]
    exact hD.trans (le_add_of_nonneg_right hLF)
  · intro p hp q hq
    have hW : 0 ≤ holderWeight α p q := by dsimp [holderWeight]; positivity
    calc
      _ ≤ L*‖Z p-Z q‖ := hLip _ (hRange p hp) _ (hRange q hq)
      _ ≤ L*(F*holderWeight α p q) := mul_le_mul_of_nonneg_left (hZ.2.2 p hp q hq) hL
      _ = (L*F)*holderWeight α p q := by ring
      _ ≤ ((M+1)+L*F)*holderWeight α p q :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM1) hW

theorem radius_holder_scale_ge_one {r α : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hα : 0 ≤ α) :
    1 ≤ r⁻¹*r^(1-α) := by
  have hPow : r ≤ r^(1-α) := Real.self_le_rpow_of_le_one hr.le hr1 (by linarith)
  calc
    1 = r⁻¹*r := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hPow (inv_nonneg.mpr hr.le)

theorem holderBound_one_sub {n : ℕ} {α D : ℝ} {Q : Set (Point n)} {q : Point n → ℝ}
    (hq : HolderBound α Q q D) : HolderBound α Q (fun p => 1-q p) (1+D) := by
  refine ⟨by linarith [hq.1],?_,?_⟩
  · intro p hp
    calc
      ‖1-q p‖ ≤ ‖(1 : ℝ)‖+‖q p‖ := norm_sub_le _ _
      _ ≤ 1+D := by simpa only [norm_one] using add_le_add le_rfl (hq.2.1 p hp)
  · intro p hp z hz
    have hW : 0 ≤ holderWeight α p z := by dsimp [holderWeight]; positivity
    have heq : (1-q p)-(1-q z) = -(q p-q z) := by ring
    rw [heq,norm_neg]
    exact (hq.2.2 p hp z hz).trans
      (mul_le_mul_of_nonneg_right (by linarith : D ≤ 1+D) hW)

theorem normalizedPatchCutoff_uniform_holderBound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) → ∀ (T : ℝ) (c : Space n),
      HolderBound α (cylinder Set.univ 0 T) (fun p => normalizedPatchCutoff s r hr c p.1)
        (C*r⁻¹*r^(1-α)) := by
  obtain ⟨A,hA,hCut⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  obtain ⟨B,hB,hSum⟩ := patchSum_uniform_holderBound (n := n) hα hα1
  let M : ℝ := ((5^(Module.finrank ℝ (Space n)) : ℕ) : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨L,hL,hLip⟩ := patchDenominator_interval_lipschitz M
  let C : ℝ := 4+16*(M+1)+16*L*B+8*A
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro s r hr hr1 hSep T c
  have hZ := hSum s r hr hr1 hSep T
  have hRange : ∀ p ∈ cylinder Set.univ 0 T, patchSum s r hr p.1 ∈ Set.Icc 0 M := by
    intro p _
    exact ⟨patchSum_nonneg s hr p.1,patchSum_le_overlap_bound hr s hSep p.1⟩
  have hDen := holderBound_patchDenominator hZ hM hL.le hRange hLip
  have hLower : ∀ p ∈ cylinder Set.univ 0 T,
      (1/4 : ℝ) ≤ patchDenominator (patchSum s r hr p.1) := by
    intro p _
    exact patchDenominator_lower (patchSum_nonneg s hr p.1)
  have hInv := holderBound_inverse_of_lower_quarter hDen hLower
  have hη := (hCut r hr hr1 T c _ (Or.inl rfl)).1
  have hηSup : ∀ p ∈ cylinder Set.univ 0 T, |innerPatchBump r hr c p.1| ≤ 1 := by
    intro p _
    rw [abs_of_nonneg (innerPatchBump r hr c).nonneg]
    exact (innerPatchBump r hr c).le_one
  have hInvSup : ∀ p ∈ cylinder Set.univ 0 T,
      ‖(patchDenominator (patchSum s r hr p.1))⁻¹‖ ≤ 4 :=
    fun p hp => inverse_norm_le_four_of_lower_quarter (hLower p hp)
  have hProduct := holderBound_smul_refined hη hInv (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 4) hηSup hInvSup
  have hFun : (fun p : Point n => innerPatchBump r hr c p.1 •
      (patchDenominator (patchSum s r hr p.1))⁻¹) =
      (fun p : Point n => normalizedPatchCutoff s r hr c p.1) := by
    funext p
    simp only [smul_eq_mul,normalizedPatchCutoff,div_eq_mul_inv]
  rw [hFun] at hProduct
  apply holderBound_mono_const hProduct
  let S : ℝ := r⁻¹*r^(1-α)
  have hScale : 1 ≤ S := radius_holder_scale_ge_one hr hr1 hα.le
  have hConst : 0 ≤ 4+16*(M+1) := by positivity
  calc
    1*(4+16*((M+1)+L*(B*r⁻¹*r^(1-α))))+(2*(r⁻¹*A)*r^(1-α))*4 =
        (4+16*(M+1))+(16*L*B+8*A)*S := by dsimp [S]; ring
    _ ≤ (4+16*(M+1))*S+(16*L*B+8*A)*S :=
      add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hScale hConst) le_rfl
    _ = C*r⁻¹*r^(1-α) := by dsimp [C,S]; ring

theorem exteriorSourceCutoff_uniform_holderBound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) → ∀ T : ℝ,
      HolderBound α (cylinder Set.univ 0 T) (fun p => exteriorSourceCutoff s r hr p.1)
        (C*r⁻¹*r^(1-α)) := by
  classical
  obtain ⟨A,hA,hNormalized⟩ := normalizedPatchCutoff_uniform_holderBound (n := n) hα hα1
  let M : ℕ := 5^(Module.finrank ℝ (Space n))
  let C : ℝ := 1+2*(M : ℝ)*A
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro s r hr hr1 hSep T
  have hBudget : 0 ≤ A*r⁻¹*r^(1-α) := by positivity
  have hEach : ∀ c ∈ s, HolderBound α (cylinder Set.univ 0 T)
      (fun p => normalizedPatchCutoff s r hr c p.1) (A*r⁻¹*r^(1-α)) := by
    intro c _
    exact hNormalized s r hr hr1 hSep T c
  have hOverlap : ∀ p ∈ cylinder Set.univ 0 T,
      (s.filter (fun c => normalizedPatchCutoff s r hr c p.1 ≠ 0)).card ≤ M := by
    intro p _
    apply (Finset.card_le_card (show
      s.filter (fun c => normalizedPatchCutoff s r hr c p.1 ≠ 0) ⊆
        s.filter (fun c => innerPatchBump r hr c p.1 ≠ 0) from ?_)).trans
      (innerPatchBump_overlap_bound hr s hSep p.1)
    intro c hc
    obtain ⟨hcs,hc0⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨hcs,?_⟩
    intro hη
    exact hc0 (by simp only [normalizedPatchCutoff,hη,zero_div])
  have hSum := holderBound_sum_boundedOverlap s hBudget hEach hOverlap
  have hSource := holderBound_one_sub hSum
  have hFun : (fun p : Point n => 1-∑ c ∈ s, normalizedPatchCutoff s r hr c p.1) =
      (fun p : Point n => exteriorSourceCutoff s r hr p.1) := by
    funext p
    dsimp only [exteriorSourceCutoff,normalizedPatchCutoff,patchSum]
    rw [Finset.sum_div]
  rw [hFun] at hSource
  apply holderBound_mono_const hSource
  let S : ℝ := r⁻¹*r^(1-α)
  have hScale : 1 ≤ S := radius_holder_scale_ge_one hr hr1 hα.le
  calc
    1+2*(M : ℝ)*(A*r⁻¹*r^(1-α)) = 1+(2*(M : ℝ)*A)*S := by dsimp [S]; ring
    _ ≤ S+(2*(M : ℝ)*A)*S := add_le_add hScale le_rfl
    _ = C*r⁻¹*r^(1-α) := by dsimp [C,S]; ring

end Yau.LeafProofs.L16Aux
