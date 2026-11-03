import Yau.Proofs.HeatSmoothExhaustionCharts

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.SmoothExhaustionAux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_affine_bump_at (p : M.Carrier) :
    ∃ (V : Set (ComplexVector n)) (v : M.Carrier → ComplexVector n) (w : M.Carrier → ℝ),
      IsOpen V ∧ chartPt p p ∈ V ∧ V ⊆ chartTarget p ∧
      (HasCompactSupport v ∧ ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞ v) ∧
      (HasCompactSupport w ∧ ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) ∞ w) ∧
      ∀ z ∈ V, v (chartInv p z)=z ∧ w (chartInv p z)=1 := by
  letI := realSmooth M
  let c := chartPt p p
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := ComplexModel n) p).mem_nhds (mem_extChartAt_target p))
  let b : ContDiffBump c :=
    { rIn := δ/4
      rOut := δ/2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hbs : tsupport b ⊆ chartTarget p := by
    rw [b.tsupport_eq]
    intro z hz
    apply hball
    apply Metric.mem_ball.mpr
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by dsimp only [b];linarith)
  let φ : ComplexVector n → ComplexVector n := fun z => b z • z
  have hφ : ContDiff ℝ ∞ φ := b.contDiff.smul contDiff_id
  have hcφ : HasCompactSupport φ := by
    exact b.hasCompactSupport.of_isClosed_subset (isClosed_tsupport φ)
      (tsupport_smul_subset_left (f := (b : ComplexVector n → ℝ)) (g := id))
  have hsφ : tsupport φ ⊆ chartTarget p :=
    (tsupport_smul_subset_left (f := (b : ComplexVector n → ℝ)) (g := id)).trans hbs
  have Hv := pushZero_properties p hφ hcφ hsφ
  have Hw := pushZero_properties p b.contDiff b.hasCompactSupport hbs
  let V := Metric.ball c (δ/4)
  have hVa : V ⊆ chartTarget p := by
    intro z hz
    apply hball
    exact Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans (by linarith))
  refine ⟨V,pushZero p φ,pushZero p b,Metric.isOpen_ball,Metric.mem_ball_self (by positivity),
    hVa,Hv,Hw,?_⟩
  intro z hz
  have hb1 : b z=1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
  rw [pushZero_chartInv p φ (hVa hz),pushZero_chartInv p b (hVa hz)]
  exact ⟨by simp only [φ,hb1,one_smul],hb1⟩

theorem finite_affine_bump_family {S : Set M.Carrier} (hS : IsCompact S) :
    ∃ (N : ℕ) (a : Fin N → M.Carrier) (V : Fin N → Set (ComplexVector n))
      (v : Fin N → M.Carrier → ComplexVector n) (w : Fin N → M.Carrier → ℝ) (C : ℝ),
      0 < C ∧ (∀ i, IsOpen (V i) ∧ V i ⊆ chartTarget (a i)) ∧
      (S ⊆ ⋃ i, chartInv (a i) '' V i) ∧
      (∀ i z, z ∈ V i → v i (chartInv (a i) z)=z ∧ w i (chartInv (a i) z)=1) ∧
      (∀ i b, ContDiffOn ℝ ∞ (fun z => v i (chartInv b z)) (chartTarget b)) ∧
      (∀ i, SmoothFn (w i)) ∧ ∀ i p, ‖v i p‖+|w i p| ≤ C := by
  classical
  letI := realSmooth M
  choose V v w H using exists_affine_bump_at (M := M)
  have hOpen (p : M.Carrier) : IsOpen (chartInv p '' V p) :=
    isOpen_chartInv_image p (H p).1 (H p).2.2.1
  have hCover : S ⊆ ⋃ p, chartInv p '' V p := by
    intro p hp
    refine mem_iUnion_of_mem p ⟨chartPt p p,(H p).2.1,?_⟩
    exact (extChartAt (ComplexModel n) p).left_inv (mem_extChartAt_source p)
  obtain ⟨s,hs⟩ := hS.elim_finite_subcover (fun p => chartInv p '' V p) hOpen hCover
  let e := Fintype.equivFin s
  let a : Fin (Fintype.card s) → M.Carrier := fun i => (e.symm i).val
  have hvb (i : Fin (Fintype.card s)) : ∃ B : ℝ, ∀ p, ‖v (a i) p‖ ≤ B :=
    (H (a i)).2.2.2.1.1.exists_bound_of_continuous (H (a i)).2.2.2.1.2.continuous
  have hwb (i : Fin (Fintype.card s)) : ∃ B : ℝ, ∀ p, ‖w (a i) p‖ ≤ B :=
    (H (a i)).2.2.2.2.1.1.exists_bound_of_continuous (H (a i)).2.2.2.2.1.2.continuous
  choose B hB using hvb
  choose D hD using hwb
  let C := 1+∑ i, (max 0 (B i)+max 0 (D i))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨Fintype.card s,a,fun i => V (a i),fun i => v (a i),fun i => w (a i),C,hC,
    fun i => ⟨(H (a i)).1,(H (a i)).2.2.1⟩,?_,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq⟩ := mem_iUnion.mp (hs hp)
    obtain ⟨hqs,hqp⟩ := mem_iUnion.mp hq
    refine mem_iUnion_of_mem (e ⟨q,hqs⟩) ?_
    simpa only [a,Equiv.symm_apply_apply] using hqp
  · intro i z hz
    exact (H (a i)).2.2.2.2.2 z hz
  · intro i b
    exact contDiffOn_inChart_of_contMDiff (H (a i)).2.2.2.1.2 b
  · intro i
    exact smoothFn_of_contMDiff (H (a i)).2.2.2.2.1.2
  · intro i p
    have HB := hB i p
    have HD : |w (a i) p| ≤ D i := by simpa only [Real.norm_eq_abs] using hD i p
    have Hsum : max 0 (B i)+max 0 (D i) ≤ ∑ j, (max 0 (B j)+max 0 (D j)) :=
      Finset.single_le_sum (fun j _ => add_nonneg (le_max_left _ _) (le_max_left _ _)) (Finset.mem_univ i)
    have HB' := le_max_right 0 (B i)
    have HD' := le_max_right 0 (D i)
    dsimp only [C]
    linarith

end Yau.Proofs.SmoothExhaustionAux
