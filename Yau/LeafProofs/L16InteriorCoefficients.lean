import Yau.LeafProofs.L16Caccioppoli

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem compact_smul_extension {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {Q : Set (Point n)} (hQ : IsOpen Q)
    {χ : Point n → ℝ} (hχ : Test Q χ) {g : Point n → V} (hg : ContDiffOn ℝ ∞ g Q) :
    ContDiff ℝ ∞ (fun p => χ p • g p) ∧ HasCompactSupport (fun p => χ p • g p) := by
  have hSmooth : ContDiff ℝ ∞ (fun p => χ p • g p) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p ∈ tsupport χ
    · exact hχ.1.contDiffAt.smul ((hg p (hχ.2.2 hp)).contDiffAt (hQ.mem_nhds (hχ.2.2 hp)))
    · apply (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
      have hZero : χ =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hp
      filter_upwards [hZero] with q hq
      simp only [Pi.zero_apply] at hq
      simp only [hq,zero_smul]
  exact ⟨hSmooth,hχ.2.1.smul_right⟩

theorem smooth_compact_global_bounds {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {g : Point n → V}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ (∀ p, ‖g p‖ ≤ C) ∧ (∀ p, ‖fderiv ℝ g p‖ ≤ C) ∧
      ∀ p q, ‖g p-g q‖ ≤ C*‖p-q‖ := by
  obtain ⟨A,hA⟩ := hcg.exists_bound_of_continuous hg.continuous
  obtain ⟨D,hD⟩ := (hcg.fderiv ℝ).exists_bound_of_continuous
    (hg.fderiv_right (m := ∞) (by simp)).continuous
  let C : ℝ := 1+|A|+|D|
  have hC : 0 < C := by dsimp only [C]; positivity
  have hAC : A ≤ C := by dsimp only [C]; linarith [le_abs_self A,abs_nonneg D]
  have hDC : D ≤ C := by dsimp only [C]; linarith [abs_nonneg A,le_abs_self D]
  have hValue (p : Point n) : ‖g p‖ ≤ C := (hA p).trans hAC
  have hDeriv (p : Point n) : ‖fderiv ℝ g p‖ ≤ C := (hD p).trans hDC
  have hLip : LipschitzWith ⟨C,hC.le⟩ g :=
    lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable (by simp)) (fun p => by
      exact_mod_cast hDeriv p)
  exact ⟨C,hC,hValue,hDeriv,fun p q => hLip.norm_sub_le p q⟩

theorem spatialDifferenceQuotient_norm_le_of_lipschitz {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {g : Point n → V} {L : ℝ}
    (hL : 0 ≤ L) (hLip : ∀ p q, ‖g p-g q‖ ≤ L*‖p-q‖)
    (e : Space n) (h : ℝ) (p : Point n) :
    ‖spatialDifferenceQuotient g e h p‖ ≤ L*‖e‖ := by
  by_cases hh : h = 0
  · simp only [spatialDifferenceQuotient,hh,inv_zero,zero_smul,norm_zero]
    positivity
  have hDist : ‖((p.1+h • e,p.2) : Point n)-p‖ = |h| * ‖e‖ := by
    simp only [Prod.sub_def,add_sub_cancel_left,sub_self,Prod.norm_def,norm_smul,
      Real.norm_eq_abs,norm_zero,max_eq_left (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
  have hScale : |h⁻¹| * |h| = 1 := by
    rw [← abs_mul,inv_mul_cancel₀ hh,abs_one]
  calc
    ‖spatialDifferenceQuotient g e h p‖ = |h⁻¹| * ‖g (p.1+h • e,p.2)-g p‖ := by
      simp only [spatialDifferenceQuotient,norm_smul,Real.norm_eq_abs]
    _ ≤ |h⁻¹| * (L*‖((p.1+h • e,p.2) : Point n)-p‖) :=
      mul_le_mul_of_nonneg_left (hLip _ _) (abs_nonneg _)
    _ = (|h⁻¹| * |h|)*(L*‖e‖) := by rw [hDist]; ring
    _ = L*‖e‖ := by rw [hScale,one_mul]

theorem smooth_compact_spatialDifferenceQuotient_common_bound {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {g : Point n → V}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ (∀ p, ‖g p‖ ≤ C) ∧
      ∀ (i : Yau.RIdx n) (h : ℝ) (p : Point n), ‖spatialDifferenceQuotient g (Yau.realVec i) h p‖ ≤ C := by
  obtain ⟨C,hC,hVal,_hDeriv,hLip⟩ := smooth_compact_global_bounds hg hcg
  refine ⟨C,hC,hVal,?_⟩
  intro i h p
  simpa only [realVec_norm,mul_one] using spatialDifferenceQuotient_norm_le_of_lipschitz hC.le hLip (Yau.realVec i) h p

theorem exists_compact_coefficient_extensions {n : ℕ} {Q K : Set (Point n)}
    (hQ : IsOpen Q) (hK : IsCompact K) (hKQ : K ⊆ Q)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients Q a b) :
    ∃ (a' : Point n → Mat n) (c' : Point n → Yau.RIdx n → ℝ) (C : ℝ),
      0 < C ∧ ContDiff ℝ ∞ a' ∧ HasCompactSupport a' ∧
      (∀ j, ContDiff ℝ ∞ (fun p => c' p j) ∧ HasCompactSupport (fun p => c' p j)) ∧
      (∀ p ∈ K, a' =ᶠ[𝓝 p] a ∧ ∀ j, (fun q => c' q j) =ᶠ[𝓝 p] (fun q => energyDrift a b q j)) ∧
      (∀ p, ‖a' p‖ ≤ C) ∧
      (∀ i h p, ‖spatialDifferenceQuotient a' (Yau.realVec i) h p‖ ≤ C) ∧
      (∀ j p, |c' p j| ≤ C) ∧
      ∀ j i h p, |spatialDifferenceQuotient (fun q => c' q j) (Yau.realVec i) h p| ≤ C := by
  obtain ⟨χ,hχ,hNear⟩ := exists_test_eq_one_near_compact hQ hK hKQ
  let a' : Point n → Mat n := fun p => χ p • a p
  let c' : Point n → Yau.RIdx n → ℝ := fun p j => χ p*energyDrift a b p j
  obtain ⟨ha',hca'⟩ := compact_smul_extension hQ hχ hSmooth.1
  have hc' (j : Yau.RIdx n) : Test Q (fun p => c' p j) :=
    test_mul_contDiffOn hQ hχ (energyDrift_smooth hQ hSmooth j)
  obtain ⟨A,hA,hAv,hADq⟩ := smooth_compact_spatialDifferenceQuotient_common_bound ha' hca'
  have hEach (j : Yau.RIdx n) : ∃ D : ℝ, 0 < D ∧ (∀ p, ‖c' p j‖ ≤ D) ∧
      ∀ i h p, ‖spatialDifferenceQuotient (fun q => c' q j) (Yau.realVec i) h p‖ ≤ D :=
    smooth_compact_spatialDifferenceQuotient_common_bound (hc' j).1 (hc' j).2.1
  choose D hD hDv hDDq using hEach
  let C : ℝ := 1+A+∑ j, D j
  have hSum : 0 ≤ ∑ j, D j := Finset.sum_nonneg (fun j _ => (hD j).le)
  have hC : 0 < C := by dsimp only [C]; linarith
  have hAC : A ≤ C := by dsimp only [C]; linarith
  have hDC (j : Yau.RIdx n) : D j ≤ C := by
    have hj := Finset.single_le_sum (s := Finset.univ) (f := D)
      (fun k _ => (hD k).le) (Finset.mem_univ j)
    dsimp only [C]
    linarith
  refine ⟨a',c',C,hC,ha',hca',fun j => ⟨(hc' j).1,(hc' j).2.1⟩,?_,
    fun p => (hAv p).trans hAC,fun i h p => (hADq i h p).trans hAC,?_,?_⟩
  · intro p hp
    constructor
    · filter_upwards [hNear p hp] with q hq
      simp only [a',hq,one_smul]
    · intro j
      filter_upwards [hNear p hp] with q hq
      simp only [c',hq,one_mul]
  · intro j p
    simpa only [Real.norm_eq_abs] using (hDv j p).trans (hDC j)
  · intro j i h p
    simpa only [Real.norm_eq_abs] using (hDDq j i h p).trans (hDC j)

theorem contDiff_spatialDifferenceQuotient {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {g : Point n → V}
    (hg : ContDiff ℝ ∞ g) (e : Space n) (h : ℝ) :
    ContDiff ℝ ∞ (spatialDifferenceQuotient g e h) := by
  have hMap : ContDiff ℝ ∞ (fun p : Point n => (p.1+h • e,p.2)) :=
    (contDiff_fst.add contDiff_const).prodMk contDiff_snd
  exact contDiff_const.smul ((hg.comp hMap).sub hg)

theorem exists_bounded_test_eq_one_near_compact {n : ℕ} {Q K : Set (Point n)}
    (hQ : IsOpen Q) (hK : IsCompact K) (hKQ : K ⊆ Q) :
    ∃ η : Point n → ℝ, Test Q η ∧ (∀ p, η p ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p ∈ K, η =ᶠ[𝓝 p] (fun _ => 1) := by
  obtain ⟨V,hV,hKV,hVQ,hVC⟩ := exists_open_between_and_isCompact_closure hK hQ hKQ
  obtain ⟨W,hW,hVW,hWQ,hWC⟩ := exists_open_between_and_isCompact_closure hVC hQ hVQ
  obtain ⟨η,hη,hRange,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hW (isClosed_closure : IsClosed (closure V)) hVW
  have hcη : HasCompactSupport η := by
    change IsCompact (tsupport η)
    simpa only [tsupport,hSupport] using hWC
  have hηQ : tsupport η ⊆ Q := by simpa only [tsupport,hSupport] using hWQ
  refine ⟨η,⟨hη,hcη,hηQ⟩,fun p => hRange (Set.mem_range_self p),?_⟩
  intro p hp
  filter_upwards [hV.mem_nhds (hKV hp)] with q hq
  exact (hOne q).mp (subset_closure hq)

end Yau.LeafProofs.L16Aux
