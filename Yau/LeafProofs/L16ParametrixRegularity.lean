import Yau.LeafProofs.L16ResidualEstimates

/-! Full regularity of the actual finite frozen heat parametrix. -/

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

private theorem holderBound_pair_same {n : ℕ} {E G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup G] {α C : ℝ} {Q : Set (Point n)}
    {f : Point n → E} {g : Point n → G}
    (hf : HolderBound α Q f C) (hg : HolderBound α Q g C) :
    HolderBound α Q (fun p => (f p,g p)) C := by
  refine ⟨hf.1,fun p hp => max_le (hf.2.1 p hp) (hg.2.1 p hp),?_⟩
  intro p hp q hq
  exact max_le (hf.2.2 p hp q hq) (hg.2.2 p hp q hq)

private theorem holderBound_smul_simple {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {α C D : ℝ} {Q : Set (Point n)}
    {f : Point n → ℝ} {g : Point n → V}
    (hf : HolderBound α Q f C) (hg : HolderBound α Q g D) :
    HolderBound α Q (fun p => f p • g p) (2*C*D) := by
  convert holderBound_smul_refined hf hg hf.1 hg.1
    (fun p hp => by simpa only [Real.norm_eq_abs] using hf.2.1 p hp) hg.2.1 using 1 <;> ring

private theorem holderBound_tensor {n : ℕ} {α C D : ℝ} {Q : Set (Point n)}
    {f g : Point n → Space n →L[ℝ] ℝ}
    (hf : HolderBound α Q f C) (hg : HolderBound α Q g D) :
    HolderBound α Q (fun p => (f p).smulRight (g p)) (2*C*D) := by
  letI : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  refine ⟨mul_nonneg (mul_nonneg (by norm_num) hf.1) hg.1,?_,?_⟩
  · intro p hp
    rw [ContinuousLinearMap.norm_smulRight_apply]
    have h := mul_le_mul (hf.2.1 p hp) (hg.2.1 p hp) (norm_nonneg _) hf.1
    nlinarith [mul_nonneg hf.1 hg.1]
  · intro p hp q hq
    have hEq : (f p).smulRight (g p)-(f q).smulRight (g q) =
        (f p).smulRight (g p-g q)+(f p-f q).smulRight (g q) := by
      ext x y
      simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,sub_apply]
      ring
    rw [hEq]
    calc
      _ ≤ ‖(f p).smulRight (g p-g q)‖+‖(f p-f q).smulRight (g q)‖ := norm_add_le _ _
      _ = ‖f p‖*‖g p-g q‖+‖f p-f q‖*‖g q‖ := by
        rw [ContinuousLinearMap.norm_smulRight_apply,ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ C*(D*holderWeight α p q)+(C*holderWeight α p q)*D :=
        add_le_add (mul_le_mul (hf.2.1 p hp) (hg.2.2 p hp q hq) (norm_nonneg _) hf.1)
          (mul_le_mul (hf.2.2 p hp q hq) (hg.2.1 q hq) (norm_nonneg _)
            (mul_nonneg hf.1 (by dsimp [holderWeight]; positivity)))
      _ = _ := by ring

/-- Multiplying by a spatial cutoff controls every genuine jet needed below. -/
theorem cutoff_full_jet_holderBound {n : ℕ} {α E K : ℝ} {Q : Set (Point n)}
    {φ : Space n → ℝ} {v : Point n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hv : C2 Q v)
    (hφ0 : HolderBound α Q (fun p => φ p.1) E)
    (hφ1 : HolderBound α Q (fun p => fderiv ℝ φ p.1) E)
    (hφ2 : HolderBound α Q (fun p => fderiv ℝ (fderiv ℝ φ) p.1) E)
    (hv0 : HolderBound α Q v K) (hv1 : HolderBound α Q (spatialD v) K)
    (hv2 : HolderBound α Q (spatialDD v) K) (hvt : HolderBound α Q (timeD Q v) K) :
    C2 Q (fun p => φ p.1*v p) ∧
    HolderBound α Q (fun p => φ p.1*v p) (8*E*K) ∧
    HolderBound α Q (spatialD (fun p => φ p.1*v p)) (8*E*K) ∧
    HolderBound α Q (spatialDD (fun p => φ p.1*v p)) (8*E*K) ∧
    HolderBound α Q (timeD Q (fun p => φ p.1*v p)) (8*E*K) := by
  have hEK := mul_nonneg hφ0.1 hv0.1
  have h0 := holderBound_mul hφ0 hv0
  have h1 := holderBound_add (holderBound_smul_simple hφ0 hv1)
    (holderBound_smul_simple hv0 hφ1)
  have h2 := holderBound_add (holderBound_add
    (holderBound_add (holderBound_smul_simple hφ0 hv2) (holderBound_tensor hφ1 hv1))
      (holderBound_tensor hv1 hφ1)) (holderBound_smul_simple hv0 hφ2)
  have ht := holderBound_mul hφ0 hvt
  refine ⟨c2_spatial_mul hφ hv,holderBound_mono_const h0 (by nlinarith),?_,?_,?_⟩
  · apply holderBound_congr_on (holderBound_mono_const h1 (by nlinarith))
    intro p hp
    exact (fderiv_fun_mul (hφ.differentiable (by norm_num) p.1)
      ((hv.2.2.2.2.1 p hp).differentiableAt (by norm_num))).symm
  · apply holderBound_congr_on (holderBound_mono_const h2 (by ring_nf; rfl))
    intro p hp
    exact (secondFDeriv_mul hφ.contDiffAt (hv.2.2.2.2.1 p hp)).symm
  · apply holderBound_congr_on (holderBound_mono_const ht (by nlinarith))
    intro p hp
    exact (timeD_spatial_mul Q φ v p).symm

theorem full_jet_add {n : ℕ} {α C D : ℝ} {Q : Set (Point n)}
    {u v : Point n → ℝ} (hu : C2 Q u) (hv : C2 Q v)
    (hu0 : HolderBound α Q u C) (hv0 : HolderBound α Q v D)
    (hu1 : HolderBound α Q (spatialD u) C) (hv1 : HolderBound α Q (spatialD v) D)
    (hu2 : HolderBound α Q (spatialDD u) C) (hv2 : HolderBound α Q (spatialDD v) D)
    (hut : HolderBound α Q (timeD Q u) C) (hvt : HolderBound α Q (timeD Q v) D) :
    C2 Q (fun p => u p+v p) ∧
    HolderBound α Q (fun p => u p+v p) (C+D) ∧
    HolderBound α Q (spatialD (fun p => u p+v p)) (C+D) ∧
    HolderBound α Q (spatialDD (fun p => u p+v p)) (C+D) ∧
    HolderBound α Q (timeD Q (fun p => u p+v p)) (C+D) := by
  letI : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  have hz := c2_zero Q
  have hn := c2_sub hz hv
  have hD (p : Point n) (hp : p ∈ Q) : spatialD (fun q => u q+v q) p =
      spatialD u p+spatialD v p := by
    have h := spatialD_sub hu hn hp
    have hN := spatialD_sub hz hv hp
    simpa only [zero_sub,sub_neg_eq_add,spatialD_zero,Pi.zero_apply] using h.trans
      (by rw [show spatialD (fun p => 0-v p) p = -spatialD v p by simpa [spatialD_zero] using hN]; abel)
  have hH (p : Point n) (hp : p ∈ Q) : spatialDD (fun q => u q+v q) p =
      spatialDD u p+spatialDD v p := by
    have h := spatialDD_sub hu hn hp
    have hN := spatialDD_sub hz hv hp
    simpa only [zero_sub,sub_neg_eq_add,spatialDD_zero,Pi.zero_apply] using h.trans
      (by rw [show spatialDD (fun p => 0-v p) p = -spatialDD v p by simpa only [spatialDD_zero,Pi.zero_apply,zero_sub] using hN]; abel)
  have ht (p : Point n) (hp : p ∈ Q) : timeD Q (fun q => u q+v q) p =
      timeD Q u p+timeD Q v p :=
    derivWithin_fun_add (hu.2.2.2.2.2 p hp) (hv.2.2.2.2.2 p hp)
  exact ⟨c2_add hu hv,holderBound_add hu0 hv0,
    holderBound_congr_on (holderBound_add hu1 hv1) (fun p hp => (hD p hp).symm),
    holderBound_congr_on (holderBound_add hu2 hv2) (fun p hp => (hH p hp).symm),
    holderBound_congr_on (holderBound_add hut hvt) (fun p hp => (ht p hp).symm)⟩

/-- Finite sums preserve full jet budgets, with their actual derivatives. -/
theorem full_jet_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    {α : ℝ} {Q : Set (Point n)} {u : ι → Point n → ℝ} {C : ι → ℝ}
    (hu : ∀ i ∈ s, C2 Q (u i) ∧ HolderBound α Q (u i) (C i) ∧
      HolderBound α Q (spatialD (u i)) (C i) ∧
      HolderBound α Q (spatialDD (u i)) (C i) ∧
      HolderBound α Q (timeD Q (u i)) (C i)) :
    C2 Q (fun p => ∑ i ∈ s, u i p) ∧
    HolderBound α Q (fun p => ∑ i ∈ s, u i p) (∑ i ∈ s, C i) ∧
    HolderBound α Q (spatialD (fun p => ∑ i ∈ s, u i p)) (∑ i ∈ s, C i) ∧
    HolderBound α Q (spatialDD (fun p => ∑ i ∈ s, u i p)) (∑ i ∈ s, C i) ∧
    HolderBound α Q (timeD Q (fun p => ∑ i ∈ s, u i p)) (∑ i ∈ s, C i) := by
  classical
  revert hu
  induction s using Finset.induction_on with
  | empty =>
    intro hu
    simp only [Finset.sum_empty]
    have hz : HolderBound α Q (fun _ : Point n => (0 : ℝ)) 0 := by simp [HolderBound]
    have hS := schauderBound_zero (n := n) α Q
    refine ⟨hS.1,hz,?_,hS.2.2.2.1,hS.2.2.2.2⟩
    simp only [spatialD_zero]
    simpa using holderBound_const α Q (0 : Space n →L[ℝ] ℝ)
  | @insert i s hi ih =>
    intro hu
    have hI := hu i (Finset.mem_insert_self i s)
    have hS := ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using full_jet_add hI.1 hS.1 hI.2.1 hS.2.1
      hI.2.2.1 hS.2.2.1 hI.2.2.2.1 hS.2.2.2.1 hI.2.2.2.2 hS.2.2.2.2

/-- Full Schauder and first-jet Hölder estimates for an arbitrary finite family.
The constant depends only on the fixed family and cutoff budgets and is uniform
on all slabs of length at most one. -/
theorem finiteHeatParametrix_full_regularity {n : ℕ} {ι : Type*} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (φ ψ : ι → Space n → ℝ)
    {E P : ℝ} (hE : 0 < E) (hP : 0 < P)
    (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hφ0 : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 1) (fun p => φ i p.1) E)
    (hφ1 : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 1)
      (fun p => fderiv ℝ (φ i) p.1) E)
    (hφ2 : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 1)
      (fun p => fderiv ℝ (fderiv ℝ (φ i)) p.1) E)
    (hψ : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 1) (fun p => ψ i p.1) P) :
    ∃ C : ℝ, 0 < C ∧ ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 T) f F →
      SchauderBound α (cylinder Set.univ 0 T) (finiteHeatParametrix s B φ ψ f) (C*F) ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (finiteHeatParametrix s B φ ψ f p,
          spatialD (finiteHeatParametrix s B φ ψ f) p)) (C*F) := by
  classical
  obtain ⟨CS,hCS,hS⟩ := constantHeatDuhamel_schauderBound (n := n) hα hα1
  obtain ⟨CJ,hCJ,hJ⟩ := constantHeatDuhamel_first_jet_holderBound (n := n) hα hα1
  let L : ι → ℝ := fun i => (CS+2*CJ)*(2*P)*constantHeatNormFactor α (B i)
  let W : ι → ℝ := fun i => 8*E*L i
  have hFactor (i : ι) : 0 ≤ constantHeatNormFactor α (B i) := by
    dsimp [constantHeatNormFactor]
    positivity
  have hL (i : ι) : 0 ≤ L i := mul_nonneg (by positivity) (hFactor i)
  have hW (i : ι) : 0 ≤ W i := mul_nonneg (by positivity) (hL i)
  have hSumW : 0 ≤ ∑ i ∈ s, W i := Finset.sum_nonneg (fun i _ => hW i)
  refine ⟨1+∑ i ∈ s, W i,by linarith,?_⟩
  intro T F hT hT1 f hf
  let Q := cylinder (n := n) Set.univ 0 T
  let v : ι → Point n → ℝ := fun i => constantHeatDuhamel (B i) (fun p => ψ i p.1*f p)
  have hSub : Q ⊆ cylinder Set.univ 0 1 := cylinder_mono_time hT1
  have hv (i : ι) (hi : i ∈ s) : C2 Q (v i) ∧
      HolderBound α Q (v i) (L i*F) ∧
      HolderBound α Q (spatialD (v i)) (L i*F) ∧
      HolderBound α Q (spatialDD (v i)) (L i*F) ∧
      HolderBound α Q (timeD Q (v i)) (L i*F) := by
    have hSource := holderBound_mul (holderBound_mono (hψ i hi) hSub) hf
    have hSB := hS (B i) T (2*P*F) hT hT1 _ hSource
    have hJB := hJ (B i) T (2*P*F) hT hT1 _ hSource
    have hSle : CS*(2*P*F)*constantHeatNormFactor α (B i) ≤ L i*F := by
      calc
        _ ≤ (CS+2*CJ)*(2*P*F)*constantHeatNormFactor α (B i) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) hSource.1) (hFactor i)
        _ = _ := by dsimp [L]; ring
    have hJle : CJ*(2*P*F)*constantHeatNormFactor α (B i)*
        (T^(1/2:ℝ)+T^((1-α)/2)) ≤ L i*F := by
      have hPow1 : T^(1/2:ℝ) ≤ 1 := Real.rpow_le_one hT.le hT1 (by norm_num)
      have hPow2 : T^((1-α)/2) ≤ 1 := Real.rpow_le_one hT.le hT1 (by linarith)
      calc
        _ ≤ CJ*(2*P*F)*constantHeatNormFactor α (B i)*2 :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (mul_nonneg hCJ.le hSource.1) (hFactor i))
        _ = (2*CJ)*(2*P*F)*constantHeatNormFactor α (B i) := by ring
        _ ≤ (CS+2*CJ)*(2*P*F)*constantHeatNormFactor α (B i) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) hSource.1) (hFactor i)
        _ = _ := by dsimp [L]; ring
    have hLow := holderBound_mono_const hJB hJle
    have hHigh : HolderBound α Q (spatialDD (v i)) (L i*F) := by
      apply holderBound_mono_const hSB.2.2.2.1
      simpa only [constantHeatNormFactor,mul_assoc] using hSle
    have hTime : HolderBound α Q (timeD Q (v i)) (L i*F) := by
      apply holderBound_mono_const hSB.2.2.2.2
      simpa only [constantHeatNormFactor,mul_assoc] using hSle
    exact ⟨hSB.1,holderBound_fst hLow,holderBound_snd hLow,hHigh,hTime⟩
  have hPatch (i : ι) (hi : i ∈ s) : C2 Q (fun p => φ i p.1*v i p) ∧
      HolderBound α Q (fun p => φ i p.1*v i p) (W i*F) ∧
      HolderBound α Q (spatialD (fun p => φ i p.1*v i p)) (W i*F) ∧
      HolderBound α Q (spatialDD (fun p => φ i p.1*v i p)) (W i*F) ∧
      HolderBound α Q (timeD Q (fun p => φ i p.1*v i p)) (W i*F) := by
    have hV := hv i hi
    have h := cutoff_full_jet_holderBound (hφ i hi) hV.1
      (holderBound_mono (hφ0 i hi) hSub) (holderBound_mono (hφ1 i hi) hSub)
      (holderBound_mono (hφ2 i hi) hSub) hV.2.1 hV.2.2.1 hV.2.2.2.1 hV.2.2.2.2
    simpa only [W,mul_assoc] using h
  have hSum := full_jet_finset_sum s hPatch
  have hBudget : (∑ i ∈ s, W i*F) ≤ (1+∑ i ∈ s, W i)*F := by
    rw [← Finset.sum_mul]
    nlinarith [hf.1]
  have h0 := holderBound_mono_const hSum.2.1 hBudget
  have h1 := holderBound_mono_const hSum.2.2.1 hBudget
  have h2 := holderBound_mono_const hSum.2.2.2.1 hBudget
  have ht := holderBound_mono_const hSum.2.2.2.2 hBudget
  change SchauderBound α Q (fun p => ∑ i ∈ s, φ i p.1*v i p) _ ∧ _
  refine ⟨⟨hSum.1,h0.1,?_,h2,ht⟩,holderBound_pair_same h0 h1⟩
  intro p hp
  exact ⟨by simpa only [Real.norm_eq_abs] using h0.2.1 p hp,h1.2.1 p hp⟩

end Yau.LeafProofs.L16Aux
