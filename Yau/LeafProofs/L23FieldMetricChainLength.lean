import Yau.LeafProofs.L23FieldMetricGeodesicChain

/-! Genuine path lengths add along finite chains and are invariant under affine parameter changes. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem fieldPathELength_congr (h : HermitianField M) (f g : ℝ → M.Carrier)
    (a b : ℝ) (heq : Set.EqOn f g (Set.Icc a b)) :
    fieldPathELength h f a b = fieldPathELength h g a b := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  exact Manifold.pathELength_congr heq

theorem fieldPathELength_nat_eq_sum (h : HermitianField M) (γ : ℝ → M.Carrier) (N : ℕ) :
    fieldPathELength h γ 0 N = ∑ i : Fin N, fieldPathELength h γ i.val (i.val+1) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  induction N with
  | zero => simp [fieldPathELength]
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [← ih]
    push_cast
    exact (Manifold.pathELength_add (show (0 : ℝ) ≤ N by positivity) (show (N : ℝ) ≤ N+1 by linarith)).symm

theorem fieldPathELength_comp_shift
    (h : HermitianField M) (γ : ℝ → M.Carrier) (a b k : ℝ) (hab : a ≤ b) :
    letI := manifold_realSmooth M
    MDifferentiableOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ (Set.Icc (a-k) (b-k)) →
      fieldPathELength h (fun u => γ (u-k)) a b = fieldPathELength h γ (a-k) (b-k) := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  intro hγ
  exact Manifold.pathELength_comp_of_monotoneOn hab
    (fun u hu v hv huv => sub_le_sub_right huv k) (differentiable_id.sub_const k).differentiableOn hγ

theorem fieldPathELength_comp_mul
    (h : HermitianField M) (γ : ℝ → M.Carrier) (a b k : ℝ) (hab : a ≤ b) (hk : 0 ≤ k) :
    letI := manifold_realSmooth M
    MDifferentiableOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ (Set.Icc (k*a) (k*b)) →
      fieldPathELength h (fun u => γ (k*u)) a b = fieldPathELength h γ (k*a) (k*b) := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  intro hγ
  exact Manifold.pathELength_comp_of_monotoneOn hab
    (fun u hu v hv huv => mul_le_mul_of_nonneg_left huv hk)
    (differentiable_id.const_mul k).differentiableOn hγ

theorem fieldPathELength_chain_eq_sum
    (h : HermitianField M) (N : ℕ) (Γ : ℝ → M.Carrier) (γ : Fin (N+1) → ℝ → M.Carrier)
    (heq : ∀ (i : Fin (N+1)) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
      Γ =ᶠ[𝓝 ((i.val : ℝ)+t)] (fun u => γ i (u-i.val))) :
    letI := manifold_realSmooth M
    (∀ i, MDifferentiableOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) (γ i) (Set.Icc (0 : ℝ) 1)) →
    fieldPathELength h Γ 0 (N+1 : ℕ) = ∑ i : Fin (N+1), fieldPathELength h (γ i) 0 1 := by
  letI := manifold_realSmooth M
  intro hγ
  rw [fieldPathELength_nat_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  have Hcurve : Set.EqOn Γ (fun u => γ i (u-i.val)) (Set.Icc (i.val : ℝ) (i.val+1)) := by
    intro u hu
    have ht : u-i.val ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have H := heq i (u-i.val) ht
    have hcenter : (i.val : ℝ)+(u-i.val) = u := by ring
    rw [hcenter] at H
    exact H.self_of_nhds
  rw [fieldPathELength_congr h Γ _ _ _ Hcurve]
  have HM : MDifferentiableOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) (γ i)
      (Set.Icc ((i.val : ℝ)-i.val) ((i.val+1 : ℝ)-i.val)) := by simpa using hγ i
  have H := fieldPathELength_comp_shift h (γ i) i.val (i.val+1) i.val (by linarith) HM
  simpa only [sub_self,add_sub_cancel_left] using H

end Yau.LeafProofs.L23Aux
