import Yau.LeafProofs.L16HolderOnlyInverse

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- Multiplication by a Holder cutoff extends a locally Holder function.
    Its values outside the cutoff domain require no bound or regularity. -/
theorem holderBound_smul_cutoff_extension {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {α P M : ℝ}
    {U Q : Set (Point n)} {χ : Point n → ℝ} {f : Point n → V}
    (hχ : HolderBound α Q χ P) (hf : HolderBound α (U ∩ Q) f M)
    (hZero : ∀ p ∈ Q, p ∉ U → χ p = 0) :
    HolderBound α Q (fun p => χ p • f p) (2*P*M) := by
  have hP : 0 ≤ P := hχ.1
  have hM : 0 ≤ M := hf.1
  have hProdRaw := holderBound_smul_refined
    (holderBound_mono hχ Set.inter_subset_right) hf hP hM
    (fun p hp => by simpa only [Real.norm_eq_abs] using hχ.2.1 p hp.2) hf.2.1
  have hProd : HolderBound α (U ∩ Q) (fun p => χ p • f p) (2*P*M) := by
    convert hProdRaw using 1; ring
  have hOne (p : Point n) (hp : p ∈ Q) (hpU : p ∈ U)
      (q : Point n) (hq : q ∈ Q) (hqU : q ∉ U) :
      ‖χ p • f p-χ q • f q‖ ≤ (2*P*M)*holderWeight α p q := by
    have hqZero := hZero q hq hqU
    have hWeight : 0 ≤ holderWeight α p q := by dsimp only [holderWeight]; positivity
    have hχDiff : |χ p| ≤ P*holderWeight α p q := by
      simpa only [hqZero,sub_zero,Real.norm_eq_abs] using hχ.2.2 p hp q hq
    rw [hqZero,zero_smul,sub_zero,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (P*holderWeight α p q)*M :=
        mul_le_mul hχDiff (hf.2.1 p ⟨hpU,hp⟩) (norm_nonneg _) (mul_nonneg hP hWeight)
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hP hM) hWeight]
  refine ⟨by positivity,?_,?_⟩
  · intro p hp
    change ‖χ p • f p‖ ≤ _
    by_cases hpU : p ∈ U
    · exact hProd.2.1 p ⟨hpU,hp⟩
    · rw [hZero p hp hpU,zero_smul,norm_zero]
      positivity
  · intro p hp q hq
    change ‖χ p • f p-χ q • f q‖ ≤ _
    by_cases hpU : p ∈ U
    · by_cases hqU : q ∈ U
      · exact hProd.2.2 p ⟨hpU,hp⟩ q ⟨hqU,hq⟩
      · exact hOne p hp hpU q hq hqU
    · by_cases hqU : q ∈ U
      · have h := hOne q hq hqU p hp hpU
        simpa only [norm_sub_rev,holderWeight,abs_sub_comm] using h
      · simp only [hZero p hp hpU,hZero q hq hqU,zero_smul,sub_self,norm_zero]
        exact mul_nonneg (by positivity) (by dsimp only [holderWeight]; positivity)

def clampPointTime {n : ℕ} (a b : ℝ) (hab : a ≤ b) (p : Point n) : Point n :=
  (p.1,(Set.projIcc a b hab p.2 : ℝ))

theorem holderWeight_clampPointTime_le {n : ℕ} {α a b : ℝ}
    (hα : 0 ≤ α) (hab : a ≤ b) (p q : Point n) :
    holderWeight α (clampPointTime a b hab p) (clampPointTime a b hab q) ≤
      holderWeight α p q := by
  have hTime : |(Set.projIcc a b hab p.2 : ℝ)-(Set.projIcc a b hab q.2 : ℝ)| ≤
      |p.2-q.2| := by
    simpa only [Subtype.dist_eq,Real.dist_eq,NNReal.coe_one,one_mul] using
      (LipschitzWith.projIcc hab).dist_le_mul p.2 q.2
  apply add_le_add le_rfl
  exact Real.rpow_le_rpow (abs_nonneg _) hTime (by positivity)

theorem holderBound_clampPointTime {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α a b M : ℝ} (hα : 0 ≤ α) (hab : a ≤ b) (O : Set (Space n))
    {f : Point n → V} (hf : HolderBound α (cylinder O a b) f M) :
    HolderBound α (O ×ˢ Set.univ) (fun p => f (clampPointTime a b hab p)) M := by
  have hMap (p : Point n) (hp : p ∈ O ×ˢ Set.univ) :
      clampPointTime a b hab p ∈ cylinder O a b :=
    ⟨hp.1,(Set.projIcc a b hab p.2).property⟩
  refine ⟨hf.1,fun p hp => hf.2.1 _ (hMap p hp),?_⟩
  intro p hp q hq
  exact (hf.2.2 _ (hMap p hp) _ (hMap q hq)).trans
    (mul_le_mul_of_nonneg_left (holderWeight_clampPointTime_le hα hab p q) hf.1)

theorem spatial_bounded_lipschitz_holderBound_univ {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] {α L : ℝ} (hα : 0 < α) (hα1 : α < 1) (hL : 0 ≤ L)
    {f : Space n → V} (hSup : ∀ x, ‖f x‖ ≤ L)
    (hLip : ∀ x y, ‖f x-f y‖ ≤ L*‖x-y‖) :
    HolderBound α Set.univ (fun p : Point n => f p.1) (2*L) := by
  refine ⟨by positivity,fun p hp => (hSup p.1).trans (by linarith),?_⟩
  intro p hp q hq
  have hSmall : ‖f p.1-f q.1‖ ≤ 2*L*1 := by
    have h := (norm_sub_le _ _).trans (add_le_add (hSup p.1) (hSup q.1))
    nlinarith
  have h := small_lipschitz_holder_scale (r := 1) (by norm_num)
    (norm_nonneg (p.1-q.1)) hL hα hα1.le hSmall (hLip p.1 q.1)
  simp only [Real.one_rpow,mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)) (by positivity))

theorem innerPatchBump_global_holderBound {n : ℕ} {α r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r) (c : Space n) :
    ∃ P : ℝ, 0 < P ∧ HolderBound α Set.univ
      (fun p : Point n => innerPatchBump r hr c p.1) P := by
  obtain ⟨A,hA,hLip⟩ := smooth_compact_lipschitz
    (innerPatchBump_contDiff hr c) (innerPatchBump r hr c).hasCompactSupport
  let L : ℝ := max 1 A
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨2*L,by positivity,?_⟩
  apply spatial_bounded_lipschitz_holderBound_univ hα hα1 hL.le
  · intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (innerPatchBump r hr c).nonneg]
    exact (innerPatchBump r hr c).le_one.trans (le_max_left _ _)
  · intro x y
    exact (hLip x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

theorem outerPatchBump_global_holderBound {n : ℕ} {α r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r) (c : Space n) :
    ∃ P : ℝ, 0 < P ∧ HolderBound α Set.univ
      (fun p : Point n => outerPatchBump r hr c p.1) P := by
  obtain ⟨A,hA,hLip⟩ := smooth_compact_lipschitz
    (outerPatchBump_contDiff hr c) (outerPatchBump r hr c).hasCompactSupport
  let L : ℝ := max 1 A
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨2*L,by positivity,?_⟩
  apply spatial_bounded_lipschitz_holderBound_univ hα hα1 hL.le
  · intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (outerPatchBump r hr c).nonneg]
    exact (outerPatchBump r hr c).le_one.trans (le_max_left _ _)
  · intro x y
    exact (hLip x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

theorem quadratic_sum_cutoff_identity {n : ℕ} (A : Mat n) (χ : ℝ)
    (v : Yau.RIdx n → ℝ) :
    (∑ i, ∑ j, (χ • A+(1-χ) • (1 : Mat n)) i j*v i*v j) =
      χ*(∑ i, ∑ j, A i j*v i*v j)+(1-χ)*(∑ i, (v i)^2) := by
  have hEach (i j : Yau.RIdx n) :
      (χ • A+(1-χ) • (1 : Mat n)) i j*v i*v j =
        χ*(A i j*v i*v j)+(1-χ)*((1 : Mat n) i j*v i*v j) := by
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  simp_rw [hEach]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  congr 1
  simp [Matrix.one_apply,pow_two]

/-- A cutoff convex combination with the identity preserves quantitative
    ellipticity, even where the original coefficient values are uncontrolled. -/
theorem elliptic_cutoff_extension {n : ℕ} {Q U : Set (Point n)}
    {a : Point n → Mat n} {χ : Point n → ℝ} {φ : Point n → Point n}
    {lam upper : ℝ} (ha : Elliptic U a lam upper)
    (hχ : ∀ p ∈ Q, χ p ∈ Set.Icc (0 : ℝ) 1)
    (hMap : ∀ p ∈ Q, χ p ≠ 0 → φ p ∈ U) :
    Elliptic Q (fun p => χ p • a (φ p)+(1-χ p) • (1 : Mat n))
      (min lam 1) (max upper 1) := by
  have hLam : 0 < min lam (1 : ℝ) := lt_min ha.1 (by norm_num)
  refine ⟨hLam,(min_le_left _ _).trans (ha.2.1.trans (le_max_left _ _)),?_⟩
  intro p hp
  have hχ0 := (hχ p hp).1
  have hχ1 := (hχ p hp).2
  by_cases hZero : χ p = 0
  · simp only [hZero,zero_smul,sub_zero,one_smul,zero_add]
    refine ⟨Matrix.isSymm_one,?_⟩
    intro v
    have hSum : 0 ≤ ∑ i : Yau.RIdx n, (v i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hIdentity : (∑ i, ∑ j, (1 : Mat n) i j*v i*v j) = ∑ i, (v i)^2 := by
      simp [Matrix.one_apply,pow_two]
    rw [hIdentity]
    exact ⟨by nlinarith [mul_le_mul_of_nonneg_right (min_le_right lam (1 : ℝ)) hSum],
      by nlinarith [mul_le_mul_of_nonneg_right (le_max_right upper (1 : ℝ)) hSum]⟩
  · have hAp := ha.2.2 (φ p) (hMap p hp hZero)
    refine ⟨(hAp.1.smul (χ p)).add (Matrix.isSymm_one.smul (1-χ p)),?_⟩
    intro v
    rw [quadratic_sum_cutoff_identity]
    have hSum : 0 ≤ ∑ i : Yau.RIdx n, (v i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hLo := mul_le_mul_of_nonneg_left (hAp.2 v).1 hχ0
    have hHi := mul_le_mul_of_nonneg_left (hAp.2 v).2 hχ0
    have hLamMin := mul_le_mul_of_nonneg_right (min_le_left lam (1 : ℝ)) hSum
    have hOneMin := mul_le_mul_of_nonneg_right (min_le_right lam (1 : ℝ)) hSum
    have hUpperMax := mul_le_mul_of_nonneg_right (le_max_left upper (1 : ℝ)) hSum
    have hOneMax := mul_le_mul_of_nonneg_right (le_max_right upper (1 : ℝ)) hSum
    constructor
    · have h1 := mul_le_mul_of_nonneg_left hLamMin hχ0
      have h2 := mul_le_mul_of_nonneg_left hOneMin (sub_nonneg.mpr hχ1)
      nlinarith
    · have h1 := mul_le_mul_of_nonneg_left hUpperMax hχ0
      have h2 := mul_le_mul_of_nonneg_left hOneMax (sub_nonneg.mpr hχ1)
      nlinarith

def interiorCoefficientCutoff {n : ℕ} (x : Space n) : ℝ :=
  outerPatchBump 1 zero_lt_one (0 : Space n) x

def interiorHolderCoefficientExtension {n : ℕ} (a : Point n → Mat n) (p : Point n) : Mat n :=
  interiorCoefficientCutoff p.1 • a (clampPointTime (-3) 0 (by norm_num) p)+
    (1-interiorCoefficientCutoff p.1) • (1 : Mat n)

def interiorHolderDriftExtension {n : ℕ} (b : Point n → Yau.RIdx n → ℝ)
    (p : Point n) (i : Yau.RIdx n) : ℝ :=
  interiorCoefficientCutoff p.1*b (clampPointTime (-3) 0 (by norm_num) p) i

/-- Uniform concrete extensions for the frozen interior cylinder. They are
    Holder on all space-time and preserve ellipticity by convex combination. -/
theorem exists_uniform_backward_coefficient_extension {n : ℕ} {α M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) :
    ∃ (M' : ℝ) (K : Set (Space n)), 0 < M' ∧ IsCompact K ∧
      ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (lam upper : ℝ),
      HolderBound α (backward 2) a M →
      (∀ i, HolderBound α (backward 2) (fun p => b p i) M) →
      Elliptic (backward 2) a lam upper →
      HolderBound α Set.univ (interiorHolderCoefficientExtension a) M' ∧
      (∀ i, HolderBound α Set.univ (fun p => interiorHolderDriftExtension b p i) M') ∧
      Elliptic Set.univ (interiorHolderCoefficientExtension a) (min lam 1) (max upper 1) ∧
      (∀ p ∈ cylinder (Metric.closedBall 0 (3/2)) (-3) 0,
        interiorHolderCoefficientExtension a p = a p ∧
          ∀ i, interiorHolderDriftExtension b p i = b p i) ∧
      (∀ p : Point n, p.1 ∉ K →
        interiorHolderCoefficientExtension a p = 1 ∧
          ∀ i, interiorHolderDriftExtension b p i = 0) := by
  obtain ⟨P,hP,hCut⟩ := outerPatchBump_global_holderBound (n := n) hα hα1
    zero_lt_one (0 : Space n)
  let χ : Space n → ℝ := interiorCoefficientCutoff
  have hχ : HolderBound α Set.univ (fun p : Point n => χ p.1) P := hCut
  let M' : ℝ := 1+2*P*M+2*(1+P)*‖(1 : Mat n)‖
  let K : Set (Space n) := tsupport χ
  have hM' : 0 < M' := by dsimp only [M']; positivity
  have hK : IsCompact K := (outerPatchBump 1 zero_lt_one (0 : Space n)).hasCompactSupport
  refine ⟨M',K,hM',hK,?_⟩
  intro a b lam upper ha hb hEll
  let U : Set (Point n) := Metric.ball 0 2 ×ˢ Set.univ
  have hSlab : cylinder (Metric.ball (0 : Space n) 2) (-3) 0 ⊆ backward 2 := by
    intro p hp
    exact ⟨hp.1,by norm_num at hp ⊢; exact ⟨by linarith [hp.2.1],hp.2.2⟩⟩
  have hClampA := holderBound_clampPointTime hα.le (by norm_num : (-3 : ℝ) ≤ 0)
    (Metric.ball (0 : Space n) 2) (holderBound_mono ha hSlab)
  have hClampB (i : Yau.RIdx n) := holderBound_clampPointTime hα.le
    (by norm_num : (-3 : ℝ) ≤ 0) (Metric.ball (0 : Space n) 2) (holderBound_mono (hb i) hSlab)
  have hChiSpace {x : Space n} (hx : χ x ≠ 0) : x ∈ Metric.ball 0 2 := by
    have h := outerPatchBump_nonzero_norm_lt (r := (1 : ℝ)) zero_lt_one hx
    simp only [sub_zero] at h
    rw [Metric.mem_ball,dist_zero_right]
    linarith
  have hZero (p : Point n) (hp : p ∈ (Set.univ : Set (Point n))) (hpU : p ∉ U) : χ p.1 = 0 := by
    by_contra hNonzero
    exact hpU ⟨hChiSpace hNonzero,Set.mem_univ _⟩
  have hProductA := holderBound_smul_cutoff_extension hχ
    (holderBound_mono hClampA (show U ∩ Set.univ ⊆ Metric.ball 0 2 ×ˢ Set.univ from Set.inter_subset_left))
    hZero
  have hProductB (i : Yau.RIdx n) := holderBound_smul_cutoff_extension hχ
    (holderBound_mono (hClampB i) (show U ∩ Set.univ ⊆ Metric.ball 0 2 ×ˢ Set.univ from Set.inter_subset_left))
    hZero
  have hOne := holderBound_const (n := n) α (Set.univ : Set (Point n)) (1 : ℝ)
  have hOneChi : HolderBound α Set.univ (fun p : Point n => 1-χ p.1) (1+P) := by
    simpa only [Real.norm_eq_abs,abs_one] using holderBound_sub hOne hχ
  have hIdentity := holderBound_smul_refined hOneChi
    (holderBound_const (n := n) α (Set.univ : Set (Point n)) (1 : Mat n))
    hOneChi.1 (norm_nonneg (1 : Mat n))
    (fun p hp => by simpa only [Real.norm_eq_abs] using hOneChi.2.1 p hp)
    (fun p hp => le_rfl)
  have hIdentityBound : HolderBound α Set.univ
      (fun p : Point n => (1-χ p.1) • (1 : Mat n)) (2*(1+P)*‖(1 : Mat n)‖) := by
    convert hIdentity using 1; ring
  refine ⟨holderBound_mono_const (holderBound_add hProductA hIdentityBound) (by
    dsimp only [M']; linarith),?_,?_,?_,?_⟩
  · intro i
    apply holderBound_mono_const (hProductB i)
    dsimp only [M']
    have hNonneg : 0 ≤ 2*(1+P)*‖(1 : Mat n)‖ := by positivity
    linarith
  · apply elliptic_cutoff_extension hEll
    · intro p hp
      exact ⟨(outerPatchBump 1 zero_lt_one (0 : Space n)).nonneg,
        (outerPatchBump 1 zero_lt_one (0 : Space n)).le_one⟩
    · intro p hp hNonzero
      exact hSlab ⟨hChiSpace hNonzero,(Set.projIcc (-3) 0 (by norm_num) p.2).property⟩
  · intro p hp
    have hChiOne : χ p.1 = 1 := by
      apply (outerPatchBump 1 zero_lt_one (0 : Space n)).one_of_mem_closedBall
      simpa only [outerPatchBump,mul_one] using hp.1
    have hTime : clampPointTime (-3) 0 (by norm_num) p = p := by
      apply Prod.ext
      · rfl
      · exact congrArg Subtype.val (Set.projIcc_of_mem (by norm_num : (-3 : ℝ) ≤ 0) hp.2)
    change χ p.1 • a (clampPointTime (-3) 0 (by norm_num) p)+(1-χ p.1) • (1 : Mat n) = a p ∧ _
    simp only [hChiOne,hTime,one_smul,sub_self,zero_smul,add_zero,true_and]
    intro i
    change χ p.1*b (clampPointTime (-3) 0 (by norm_num) p) i = b p i
    rw [hChiOne,hTime,one_mul]
  · intro p hp
    have hChiZero : χ p.1 = 0 := image_eq_zero_of_notMem_tsupport hp
    change χ p.1 • a (clampPointTime (-3) 0 (by norm_num) p)+(1-χ p.1) • (1 : Mat n) = 1 ∧ _
    simp only [hChiZero,zero_smul,sub_zero,one_smul,zero_add,true_and]
    intro i
    change χ p.1*b (clampPointTime (-3) 0 (by norm_num) p) i = 0
    rw [hChiZero,zero_mul]

end Yau.LeafProofs.L16Aux
