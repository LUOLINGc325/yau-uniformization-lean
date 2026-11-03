import Yau.LeafProofs.L16ShortInverse

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem frozen_patch_coefficient_sup_holder {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {α M r ε τ : ℝ} (hα : 0 ≤ α)
    (ha : HolderBound α Q a M) (hr : 0 < r)
    (c : Space n) (hFrozen : (c,τ) ∈ Q) {p : Point n} (hp : p ∈ Q)
    (hTime : |p.2-τ| ≤ ε) (i j : Yau.RIdx n) :
    |outerPatchBump r hr c p.1*(a (c,τ) i j-a p i j)| ≤
      M*((2*r)^α+ε^(α/2)) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hTime
  have hM : 0 ≤ M := ha.1
  have hBudget : 0 ≤ M*((2*r)^α+ε^(α/2)) := by positivity
  by_cases hφ : outerPatchBump r hr c p.1 = 0
  · rw [hφ,zero_mul,abs_zero]
    exact hBudget
  have hSpace := outerPatchBump_nonzero_norm_lt hr hφ
  have hWeight : holderWeight α (c,τ) p ≤ (2*r)^α+ε^(α/2) := by
    apply add_le_add
    · apply Real.rpow_le_rpow (norm_nonneg _) _ hα
      rw [norm_sub_rev]
      exact hSpace.le
    · apply Real.rpow_le_rpow (abs_nonneg _) _ (by positivity)
      simpa only [abs_sub_comm] using hTime
  have hEntry : |a (c,τ) i j-a p i j| ≤ M*((2*r)^α+ε^(α/2)) := by
    have h := (frobenius_entry_abs_le (a (c,τ)-a p) i j).trans
      ((ha.2.2 (c,τ) hFrozen p hp).trans (mul_le_mul_of_nonneg_left hWeight ha.1))
    simpa only [Matrix.sub_apply] using h
  rw [abs_mul,abs_of_nonneg (outerPatchBump r hr c).nonneg]
  exact (mul_le_mul (outerPatchBump r hr c).le_one hEntry (abs_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)

theorem holderBound_cutoff_source_refined {n : ℕ} {α P F S : ℝ} {Q : Set (Point n)}
    {χ f : Point n → ℝ} (hχ : HolderBound α Q χ P)
    (hχSup : ∀ p ∈ Q, |χ p| ≤ 1) (hf : HolderBound α Q f F)
    (hS : 0 ≤ S) (hSup : ∀ p ∈ Q, |f p| ≤ S) :
    HolderBound α Q (fun p => χ p*f p) (F+P*S) := by
  have h := holderBound_smul_refined hχ hf (by norm_num : (0 : ℝ) ≤ 1) hS hχSup
    (fun p hp => by simpa only [Real.norm_eq_abs] using hSup p hp)
  simpa only [smul_eq_mul,one_mul] using h

theorem source_cutoffs_uniform_refined_holderBound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ P : ℝ, 0 < P ∧ ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) → ∀ T F S : ℝ,
      ∀ f : Point n → ℝ, HolderBound α (cylinder Set.univ 0 T) f F → 0 ≤ S →
      (∀ p ∈ cylinder Set.univ 0 T, |f p| ≤ S) →
      (∀ c ∈ s, HolderBound α (cylinder Set.univ 0 T)
        (fun p => normalizedPatchCutoff s r hr c p.1*f p) (F+(P*r⁻¹*r^(1-α))*S)) ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => exteriorSourceCutoff s r hr p.1*f p) (F+(P*r⁻¹*r^(1-α))*S) := by
  obtain ⟨P,hP,hSource⟩ := source_cutoffs_uniform_holderBound (n := n) hα hα1
  refine ⟨P,hP,?_⟩
  intro s r hr hr1 hSep T F S f hf hS hSup
  constructor
  · intro c hc
    apply holderBound_cutoff_source_refined ((hSource s r hr hr1 hSep T).1 c) _ hf hS hSup
    intro p hp
    rw [abs_of_nonneg (normalizedPatchCutoff_nonneg s hr c p.1)]
    exact normalizedPatchCutoff_le_one s hr hc p.1
  · apply holderBound_cutoff_source_refined (hSource s r hr hr1 hSep T).2 _ hf hS hSup
    intro p hp
    rw [abs_of_nonneg (exteriorSourceCutoff_mem_Icc s hr p.1).1]
    exact (exteriorSourceCutoff_mem_Icc s hr p.1).2

/-- The supremum estimate keeps the small Hessian supremum and does not use
    its generally nonsmall Holder budget. -/
theorem hessian_contraction_sup_bound {n : ℕ} {A D : ℝ} {Q : Set (Point n)}
    {q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ}
    {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hD : 0 ≤ D) (hq : ∀ i j, ∀ p ∈ Q, |q i j p| ≤ A)
    (hH : ∀ p ∈ Q, ‖H p‖ ≤ D) {p : Point n} (hp : p ∈ Q) :
    |∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
      q i j p*H p (Yau.realVec i) (Yau.realVec j)| ≤
      (Fintype.card (Yau.RIdx n) : ℝ)^2*A*D := by
  have hEach (i j : Yau.RIdx n) :
      |q i j p*H p (Yau.realVec i) (Yau.realVec j)| ≤ A*D := by
    rw [abs_mul]
    calc
      _ = |H p (Yau.realVec i) (Yau.realVec j)| * |q i j p| := mul_comm _ _
      _ ≤ D*A := mul_le_mul
        ((norm_hessian_component_le (H p) i j).trans (hH p hp))
        (hq i j p hp) (abs_nonneg _) hD
      _ = A*D := mul_comm _ _
  calc
    _ ≤ ∑ i : Yau.RIdx n, |∑ j : Yau.RIdx n,
        q i j p*H p (Yau.realVec i) (Yau.realVec j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Yau.RIdx n, ∑ _j : Yau.RIdx n, A*D := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j hj => hEach i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem frozenPatchResidual_sup_bound {n : ℕ} {α A0 D M E0 E1 E2 J : ℝ}
    {Q : Set (Point n)} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {A : Mat n} {φ : Space n → ℝ} {v : Point n → ℝ} (hD : 0 ≤ D)
    (ha : HolderBound α Q a M) (hb : ∀ i, HolderBound α Q (fun p => b p i) M)
    (hφ : HolderBound α Q (fun p => φ p.1) E0)
    (hφD : ∀ i : Yau.RIdx n,
      HolderBound α Q (fun p => fderiv ℝ φ p.1 (Yau.realVec i)) E1)
    (hφDD : ∀ i j : Yau.RIdx n, HolderBound α Q
      (fun p => fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)) E2)
    (hJet : HolderBound α Q (fun p => (v p,spatialD v p)) J)
    (hHessSup : ∀ p ∈ Q, ‖spatialDD v p‖ ≤ D)
    (hCoeffSup : ∀ i j : Yau.RIdx n, ∀ p ∈ Q, |φ p.1*(A i j-a p i j)| ≤ A0)
    {p : Point n} (hp : p ∈ Q) :
    |frozenPatchResidual Q a b A φ v p| ≤
      (Fintype.card (Yau.RIdx n) : ℝ)^2*A0*D+lowerCutoffBudget n M E0 E1 E2*J := by
  rw [frozenPatchResidual_eq_principal_sub_lower]
  have hLower := (lowerPatchResidual_holderBound ha hb hφ hφD hφDD hJet).2.1 p hp
  have hPrincipal := hessian_contraction_sup_bound hD hCoeffSup hHessSup hp
  exact (abs_sub _ _).trans (add_le_add hPrincipal hLower)

def holderOnlyInteriorHolderRate (n : ℕ) (α Cφ CH M N r T : ℝ) : ℝ :=
  let E0 := cutoffJetBudget α Cφ r 0
  let E1 := cutoffJetBudget α Cφ r 1
  let E2 := cutoffJetBudget α Cφ r 2
  CH*N*((Fintype.card (Yau.RIdx n) : ℝ)^2*
    (M*((2*r)^α+T^(α/2))+4*E0*M*T^(α/2))+
    lowerCutoffBudget n M E0 E1 E2*(T^(1/2:ℝ)+T^((1-α)/2)))

def holderOnlyInteriorSupRate (n : ℕ) (α Cφ CH M N r T : ℝ) : ℝ :=
  let E0 := cutoffJetBudget α Cφ r 0
  let E1 := cutoffJetBudget α Cφ r 1
  let E2 := cutoffJetBudget α Cφ r 2
  CH*N*((Fintype.card (Yau.RIdx n) : ℝ)^2*
    (M*((2*r)^α+T^(α/2))*T^(α/2))+
    lowerCutoffBudget n M E0 E1 E2*(T^(1/2:ℝ)+T^((1-α)/2)))

/-- Actual frozen heat residual estimates under Holder coefficient bounds alone.
    The source Holder and supremum budgets remain separate. -/
theorem interiorHeatResidual_holder_only_refined_bounds {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ P Cφ CH : ℝ, 0 < P ∧ 0 < Cφ ∧ 0 < CH ∧
      ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) →
      ∀ (T F S M N : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (B : Space n ≃L[ℝ] Space n) (c : Space n) (f : Point n → ℝ),
      c ∈ s → 0 < T → T ≤ 1 → constantHeatNormFactor α B ≤ N →
      HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      HolderBound α (cylinder Set.univ 0 T) f F → 0 ≤ S →
      (∀ p ∈ cylinder Set.univ 0 T, |f p| ≤ S) →
      HolderBound α (cylinder Set.univ 0 T)
        (frozenPatchResidual (cylinder Set.univ 0 T) a b (a (c,0)) (outerPatchBump r hr c)
          (constantHeatDuhamel B (fun p => normalizedPatchCutoff s r hr c p.1*f p)))
        (holderOnlyInteriorHolderRate n α Cφ CH M N r T*(F+(P*r⁻¹*r^(1-α))*S)) ∧
      (∀ p ∈ cylinder Set.univ 0 T,
        |frozenPatchResidual (cylinder Set.univ 0 T) a b (a (c,0)) (outerPatchBump r hr c)
          (constantHeatDuhamel B (fun p => normalizedPatchCutoff s r hr c p.1*f p)) p| ≤
        holderOnlyInteriorSupRate n α Cφ CH M N r T*(F+(P*r⁻¹*r^(1-α))*S)) := by
  obtain ⟨P,hP,hSource⟩ := source_cutoffs_uniform_refined_holderBound (n := n) hα hα1
  obtain ⟨Cφ,hCφ,hCutoff⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  obtain ⟨CH,hCH,hHeat⟩ := constantHeatDuhamel_controlled_bounds (n := n) hα hα1
  refine ⟨P,Cφ,CH,hP,hCφ,hCH,?_⟩
  intro s r hr hr1 hSep T F S M N a b B c f hc hT hT1 hN ha hb hf hS hSup
  let E0 := cutoffJetBudget α Cφ r 0
  let E1 := cutoffJetBudget α Cφ r 1
  let E2 := cutoffJetBudget α Cφ r 2
  let W : ℝ := F+(P*r⁻¹*r^(1-α))*S
  let G : ℝ := CH*N
  let w : Point n → ℝ := fun p => normalizedPatchCutoff s r hr c p.1*f p
  let u : Point n → ℝ := constantHeatDuhamel B w
  have hWeighted : HolderBound α (cylinder Set.univ 0 T) w W :=
    (hSource s r hr hr1 hSep T F S f hf hS hSup).1 c hc
  have hHeatBounds := hHeat N B hN T W hT hT1 w hWeighted
  have hHeatScale : CH*W*N = G*W := by dsimp only [G]; ring
  rw [hHeatScale] at hHeatBounds
  have hCut := hCutoff r hr hr1 T c _ (Or.inr rfl)
  have hφ : HolderBound α (cylinder Set.univ 0 T) (fun p => outerPatchBump r hr c p.1) E0 := by
    simpa only [E0,cutoffJetBudget,Nat.zero_add,pow_one] using hCut.1
  have hφD : HolderBound α (cylinder Set.univ 0 T)
      (fun p => fderiv ℝ (outerPatchBump r hr c) p.1) E1 := by
    simpa only [E1,cutoffJetBudget] using hCut.2.1
  have hφDD : HolderBound α (cylinder Set.univ 0 T)
      (fun p => fderiv ℝ (fderiv ℝ (outerPatchBump r hr c)) p.1) E2 := by
    simpa only [E2,cutoffJetBudget] using hCut.2.2
  have hOrigin : (c,(0 : ℝ)) ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,le_rfl,hT.le⟩
  have hA0 : 0 ≤ M*((2*r)^α+T^(α/2)) := mul_nonneg ha.1 (by positivity)
  have hD0 : 0 ≤ G*W*T^(α/2) :=
    mul_nonneg hHeatBounds.1.2.1 (Real.rpow_nonneg hT.le _)
  have hCoeff (i j : Yau.RIdx n) := frozen_patch_coefficient_holderBound ha hφ c 0 hOrigin i j
  have hCoeffSup (i j : Yau.RIdx n) (p : Point n) (hp : p ∈ cylinder Set.univ 0 T) :
      |outerPatchBump r hr c p.1*(a (c,0) i j-a p i j)| ≤ M*((2*r)^α+T^(α/2)) := by
    apply frozen_patch_coefficient_sup_holder hα.le ha hr c hOrigin hp
    simpa only [sub_zero,abs_of_nonneg hp.2.1] using hp.2.2
  constructor
  · have hBound := frozenPatchResidual_holderBound hA0 hD0 ha hb hφ
      (fun i => holderBound_gradient_component hφD i)
      (fun i j => holderBound_hessian_component hφDD i j)
      hHeatBounds.2.2 hHeatBounds.1.2.2.2.1 hHeatBounds.2.1 hCoeff hCoeffSup
    change HolderBound α (cylinder Set.univ 0 T)
      (frozenPatchResidual (cylinder Set.univ 0 T) a b (a (c,0)) (outerPatchBump r hr c) u) _
    convert hBound using 1
    dsimp only [holderOnlyInteriorHolderRate,lowerCutoffBudget,E0,E1,E2,G,W]
    ring
  · intro p hp
    have hBound := frozenPatchResidual_sup_bound hD0 ha hb hφ
      (fun i => holderBound_gradient_component hφD i)
      (fun i j => holderBound_hessian_component hφDD i j)
      hHeatBounds.2.2 hHeatBounds.2.1 hCoeffSup hp
    change |frozenPatchResidual (cylinder Set.univ 0 T) a b (a (c,0)) (outerPatchBump r hr c) u p| ≤ _
    convert hBound using 1
    dsimp only [holderOnlyInteriorSupRate,lowerCutoffBudget,E0,E1,E2,G,W]
    ring

theorem holderOnlyInteriorHolderRate_zero (n : ℕ) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (Cφ CH M N r : ℝ) :
    holderOnlyInteriorHolderRate n α Cφ CH M N r 0 =
      CH*N*(Fintype.card (Yau.RIdx n) : ℝ)^2*M*(2*r)^α := by
  have hα2 : α/2 ≠ 0 := ne_of_gt (by positivity)
  have hHalf : (1/2 : ℝ) ≠ 0 := by norm_num
  have hRest : (1-α)/2 ≠ 0 := ne_of_gt (by linarith)
  simp only [holderOnlyInteriorHolderRate,Real.zero_rpow hα2,Real.zero_rpow hHalf,
    Real.zero_rpow hRest,mul_zero,add_zero]
  ring

theorem holderOnlyInteriorSupRate_zero (n : ℕ) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (Cφ CH M N r : ℝ) :
    holderOnlyInteriorSupRate n α Cφ CH M N r 0 = 0 := by
  have hα2 : α/2 ≠ 0 := ne_of_gt (by positivity)
  have hHalf : (1/2 : ℝ) ≠ 0 := by norm_num
  have hRest : (1-α)/2 ≠ 0 := ne_of_gt (by linarith)
  simp only [holderOnlyInteriorSupRate,Real.zero_rpow hα2,Real.zero_rpow hHalf,
    Real.zero_rpow hRest,mul_zero,add_zero]

theorem holderOnlyInteriorHolderRate_continuous (n : ℕ) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (Cφ CH M N r : ℝ) :
    Continuous (fun T => holderOnlyInteriorHolderRate n α Cφ CH M N r T) := by
  have hA : Continuous (fun T : ℝ => T^(α/2)) := Real.continuous_rpow_const (by positivity)
  have hB : Continuous (fun T : ℝ => T^(1/2 : ℝ)) := Real.continuous_rpow_const (by positivity)
  have hC : Continuous (fun T : ℝ => T^((1-α)/2)) := Real.continuous_rpow_const (by linarith)
  dsimp only [holderOnlyInteriorHolderRate]
  fun_prop

theorem holderOnlyInteriorSupRate_continuous (n : ℕ) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (Cφ CH M N r : ℝ) :
    Continuous (fun T => holderOnlyInteriorSupRate n α Cφ CH M N r T) := by
  have hA : Continuous (fun T : ℝ => T^(α/2)) := Real.continuous_rpow_const (by positivity)
  have hB : Continuous (fun T : ℝ => T^(1/2 : ℝ)) := Real.continuous_rpow_const (by positivity)
  have hC : Continuous (fun T : ℝ => T^((1-α)/2)) := Real.continuous_rpow_const (by linarith)
  dsimp only [holderOnlyInteriorSupRate]
  fun_prop

local instance {n : ℕ} (α : ℝ) (Q : Set (Point n)) : NormedAddCommGroup (holderGraph α Q) :=
  inferInstance
local instance {n : ℕ} (α : ℝ) (Q : Set (Point n)) : NormedSpace ℝ (holderGraph α Q) :=
  inferInstance

theorem holderGraph_square_norm_bound {n : ℕ} {α : ℝ} {Q : Set (Point n)}
    (R : holderGraph α Q →L[ℝ] holderGraph α Q) {ε A d : ℝ}
    (hε : 0 ≤ ε) (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hStrong : ∀ x, ‖R x‖ ≤ ε*‖x‖+A*‖x.val.1‖)
    (hSup : ∀ x, ‖(R x).val.1‖ ≤ d*‖x‖) :
    ‖R.comp R‖ ≤ ε*(ε+A)+A*d := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hProjection : ‖x.val.1‖ ≤ ‖x‖ := by
    change ‖x.val.1‖ ≤ max ‖x.val.1‖ ‖x.val.2‖
    exact le_max_left _ _
  have hR : ‖R x‖ ≤ (ε+A)*‖x‖ := by
    have h := (hStrong x).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hProjection hA))
    nlinarith
  have h := (hStrong (R x)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hR hε) (mul_le_mul_of_nonneg_left (hSup x) hA))
  simpa only [ContinuousLinearMap.comp_apply,mul_add,add_mul,mul_assoc] using h

theorem holderGraph_residual_correction_of_square {n : ℕ} {α : ℝ} {Q : Set (Point n)}
    (R : holderGraph α Q →L[ℝ] holderGraph α Q) (hR2 : ‖R.comp R‖ ≤ (1/2 : ℝ))
    (f : holderGraph α Q) :
    ∃ g : holderGraph α Q, g+R g = f ∧ ‖g‖ ≤ 2*(1+‖R‖)*‖f‖ := by
  obtain ⟨h,hCorrect,hh⟩ := holderGraph_residual_correction (-(R.comp R))
    (by simpa only [norm_neg] using hR2) f
  have hEq : h-R (R h) = f := by
    simpa only [neg_apply,ContinuousLinearMap.comp_apply,sub_eq_add_neg] using hCorrect
  refine ⟨h-R h,?_,?_⟩
  · rw [R.map_sub]
    convert! hEq using 1; abel
  · calc
      ‖h-R h‖ ≤ ‖h‖+‖R h‖ := norm_sub_le _ _
      _ ≤ ‖h‖+‖R‖*‖h‖ := add_le_add le_rfl (R.le_opNorm h)
      _ = (1+‖R‖)*‖h‖ := by ring
      _ ≤ (1+‖R‖)*(2*‖f‖) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring

/-- A correction in the existing Holder Banach space, using a weighted size only in
    the geometric-series estimates. The required estimates are explicit premises. -/
theorem holderGraph_residual_correction_weighted {n : ℕ} {α : ℝ} {Q : Set (Point n)}
    (R : holderGraph α Q →L[ℝ] holderGraph α Q) {B : ℝ} (hB : 0 ≤ B)
    (hContract : ∀ x, ‖R x‖+B*‖(R x).val.1‖ ≤
      (1/2 : ℝ)*(‖x‖+B*‖x.val.1‖)) (f : holderGraph α Q) :
    ∃ g : holderGraph α Q, g+R g = f ∧ ‖g‖ ≤ 2*(1+B)*‖f‖ := by
  let N : holderGraph α Q → ℝ := fun x => ‖x‖+B*‖x.val.1‖
  have hN (x : holderGraph α Q) : ‖x‖ ≤ N x := by
    dsimp only [N]
    exact le_add_of_nonneg_right (mul_nonneg hB (norm_nonneg _))
  have hNeg (x : holderGraph α Q) : N (-x) = N x := by
    simp only [N,norm_neg,Submodule.coe_neg,Prod.fst_neg]
  let v : ℕ → holderGraph α Q := fun k => (fun x => -R x)^[k] f
  have hv0 : v 0 = f := rfl
  have hvSucc (k : ℕ) : v (k+1) = -R (v k) :=
    Function.iterate_succ_apply' (fun x => -R x) k f
  have hvSize (k : ℕ) : N (v k) ≤ (1/2 : ℝ)^k*N f := by
    induction k with
    | zero => simp only [hv0,pow_zero,one_mul,le_refl]
    | succ k ih =>
      rw [hvSucc,hNeg]
      calc
        N (R (v k)) ≤ (1/2 : ℝ)*N (v k) := hContract _
        _ ≤ (1/2 : ℝ)*((1/2 : ℝ)^k*N f) := by gcongr
        _ = (1/2 : ℝ)^(k+1)*N f := by ring
  have hvBound (k : ℕ) : ‖v k‖ ≤ (1/2 : ℝ)^k*N f := (hN _).trans (hvSize k)
  have hGeom : Summable (fun k : ℕ => (1/2 : ℝ)^k*N f) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  have hvSum : Summable v := hGeom.of_norm_bounded hvBound
  refine ⟨∑' k, v k,?_,?_⟩
  · have hTail : (∑' k, v (k+1)) = -R (∑' k, v k) := by
      simp_rw [hvSucc]
      rw [tsum_neg,← R.map_tsum hvSum]
    have hSum := hvSum.tsum_eq_zero_add
    rw [hv0,hTail] at hSum
    exact eq_sub_iff_add_eq.mp hSum
  · have hBound : ‖∑' k, v k‖ ≤ 2*N f := by
      apply tsum_of_norm_bounded _ hvBound
      convert hGeom.hasSum using 1
      rw [tsum_mul_right,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    have hProjection : ‖f.val.1‖ ≤ ‖f‖ := by
      change ‖f.val.1‖ ≤ max ‖f.val.1‖ ‖f.val.2‖
      exact le_max_left _ _
    calc
      _ ≤ 2*N f := hBound
      _ ≤ 2*(1+B)*‖f‖ := by dsimp only [N]; nlinarith

/-- The large supremum coefficient is absorbed into a weight chosen after the
    cutoff radius; no smallness requirement on its product with ε is used. -/
theorem holderGraph_residual_correction_of_two_bounds {n : ℕ} {α : ℝ}
    {Q : Set (Point n)} (R : holderGraph α Q →L[ℝ] holderGraph α Q)
    {ε A d B : ℝ} (hB : 0 ≤ B) (hεd : ε+B*d ≤ (1/2 : ℝ))
    (hAB : A ≤ B/2)
    (hStrong : ∀ x, ‖R x‖ ≤ ε*‖x‖+A*‖x.val.1‖)
    (hSup : ∀ x, ‖(R x).val.1‖ ≤ d*‖x‖) (f : holderGraph α Q) :
    ∃ g : holderGraph α Q, g+R g = f ∧ ‖g‖ ≤ 2*(1+B)*‖f‖ := by
  apply holderGraph_residual_correction_weighted R hB _ f
  intro x
  have h := add_le_add (hStrong x) (mul_le_mul_of_nonneg_left (hSup x) hB)
  have h1 := mul_le_mul_of_nonneg_right hεd (norm_nonneg x)
  have h2 := mul_le_mul_of_nonneg_right hAB (norm_nonneg x.val.1)
  nlinarith

/-- Choose the weight after the potentially large supremum coefficient. -/
theorem holderGraph_residual_correction_of_small_two_bounds {n : ℕ} {α : ℝ}
    {Q : Set (Point n)} (R : holderGraph α Q →L[ℝ] holderGraph α Q)
    {ε A d : ℝ} (hε : ε ≤ (1/4 : ℝ)) (_hA : 0 ≤ A)
    (hd : d ≤ 1/(4*max 1 (4*A)))
    (hStrong : ∀ x, ‖R x‖ ≤ ε*‖x‖+A*‖x.val.1‖)
    (hSup : ∀ x, ‖(R x).val.1‖ ≤ d*‖x‖) (f : holderGraph α Q) :
    ∃ g : holderGraph α Q, g+R g = f ∧ ‖g‖ ≤ 2*(1+max 1 (4*A))*‖f‖ := by
  have hB : 0 < max 1 (4*A) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hBd := (le_div_iff₀ (by positivity : 0 < 4*max 1 (4*A))).mp hd
  have hAB : A ≤ max 1 (4*A)/2 := by linarith [le_max_right (1 : ℝ) (4*A)]
  exact holderGraph_residual_correction_of_two_bounds R hB.le
    (by nlinarith) hAB hStrong hSup f

end Yau.LeafProofs.L16Aux
