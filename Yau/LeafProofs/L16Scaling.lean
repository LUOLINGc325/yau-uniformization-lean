import Yau.LeafProofs.L16Localization

/-! Radius-dependent jet and Holder estimates for the L16 spatial parametrix cutoffs. -/

open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L16Aux

open Yau.Parabolic

local instance {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (Space n →L[ℝ] F) := inferInstance
local instance {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (Space n →L[ℝ] F) := inferInstance
local instance {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] F) := inferInstance
local instance {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] F) := inferInstance

def rescaleSpatial {n : ℕ} {F : Type*} (r : ℝ) (c : Space n) (g : Space n → F)
    (x : Space n) : F := g (r⁻¹ • (x-c))

theorem rescaleSpatial_fderiv {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (r : ℝ) (c : Space n) {g : Space n → F}
    (hg : Differentiable ℝ g) :
    fderiv ℝ (rescaleSpatial r c g) = r⁻¹ • rescaleSpatial r c (fderiv ℝ g) := by
  funext x
  change fderiv ℝ (fun y : Space n => g (r⁻¹ • (y-c))) x =
    r⁻¹ • fderiv ℝ g (r⁻¹ • (x-c))
  have hArg : HasFDerivAt (fun y : Space n => r⁻¹ • (y-c))
      (r⁻¹ • ContinuousLinearMap.id ℝ (Space n)) x :=
    ((hasFDerivAt_id x).sub_const c).const_smul r⁻¹
  have h := ((hg (r⁻¹ • (x-c))).hasFDerivAt.comp x hArg).fderiv
  simpa only [rescaleSpatial, Function.comp_def, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_id, Pi.smul_apply] using h

theorem rescaleSpatial_secondFDeriv {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (r : ℝ) (c : Space n) {g : Space n → F}
    (hg : ContDiff ℝ ∞ g) :
    fderiv ℝ (fderiv ℝ (rescaleSpatial r c g)) =
      (r⁻¹)^2 • rescaleSpatial r c (fderiv ℝ (fderiv ℝ g)) := by
  have hgD : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  rw [rescaleSpatial_fderiv r c (hg.differentiable (by simp)),
    fderiv_const_smul_field (𝕜 := ℝ) (f := rescaleSpatial r c (fderiv ℝ g)),
    rescaleSpatial_fderiv r c (hgD.differentiable (by simp)), smul_smul, ← pow_two]

theorem rescaleSpatial_thirdFDeriv {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (r : ℝ) (c : Space n) {g : Space n → F}
    (hg : ContDiff ℝ ∞ g) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (rescaleSpatial r c g))) =
      (r⁻¹)^3 • rescaleSpatial r c (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) := by
  have hgD : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have hgDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ g)) := hgD.fderiv_right (by simp)
  rw [rescaleSpatial_secondFDeriv r c hg,
    fderiv_const_smul_field (𝕜 := ℝ) (f := rescaleSpatial r c (fderiv ℝ (fderiv ℝ g))),
    rescaleSpatial_fderiv r c (hgDD.differentiable (by simp)), smul_smul, ← pow_succ]

theorem smooth_compact_three_jets_bound {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : Space n → F} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x,
      ‖fderiv ℝ g x‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x‖ ≤ C := by
  have hgD : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have hgDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ g)) := hgD.fderiv_right (by simp)
  have hgDDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) :=
    hgDD.fderiv_right (by simp)
  obtain ⟨A,hA⟩ := (hcg.fderiv ℝ).exists_bound_of_continuous hgD.continuous
  obtain ⟨B,hB⟩ := ((hcg.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous hgDD.continuous
  obtain ⟨D,hD⟩ := (((hcg.fderiv ℝ).fderiv ℝ).fderiv ℝ).exists_bound_of_continuous
    hgDDD.continuous
  let C : ℝ := 1+|A|+|B|+|D|
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro x
  have hAC : A ≤ C := by dsimp [C]; linarith [le_abs_self A, abs_nonneg B, abs_nonneg D]
  have hBC : B ≤ C := by dsimp [C]; linarith [abs_nonneg A, le_abs_self B, abs_nonneg D]
  have hDC : D ≤ C := by dsimp [C]; linarith [abs_nonneg A, abs_nonneg B, le_abs_self D]
  exact ⟨(hA x).trans hAC,(hB x).trans hBC,(hD x).trans hDC⟩

theorem rescaleSpatial_three_jets_bound {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {r C : ℝ} (hr : 0 < r) (c : Space n) {g : Space n → F}
    (hg : ContDiff ℝ ∞ g)
    (hC : ∀ x, ‖fderiv ℝ g x‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x‖ ≤ C) (x : Space n) :
    ‖fderiv ℝ (rescaleSpatial r c g) x‖ ≤ r⁻¹*C ∧
      ‖fderiv ℝ (fderiv ℝ (rescaleSpatial r c g)) x‖ ≤ (r⁻¹)^2*C ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (rescaleSpatial r c g))) x‖ ≤ (r⁻¹)^3*C := by
  have hrI : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  constructor
  · rw [rescaleSpatial_fderiv r c (hg.differentiable (by simp))]
    simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hrI]
    exact mul_le_mul_of_nonneg_left (hC _).1 hrI
  constructor
  · rw [rescaleSpatial_secondFDeriv r c hg]
    simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hrI 2)]
    exact mul_le_mul_of_nonneg_left (hC _).2.1 (pow_nonneg hrI 2)
  · rw [rescaleSpatial_thirdFDeriv r c hg]
    simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hrI 3)]
    exact mul_le_mul_of_nonneg_left (hC _).2.2 (pow_nonneg hrI 3)

theorem patchBumps_uniform_three_jets_bound {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (hr : 0 < r) (c x : Space n),
      (‖fderiv ℝ (innerPatchBump r hr c) x‖ ≤ r⁻¹*C ∧
        ‖fderiv ℝ (fderiv ℝ (innerPatchBump r hr c)) x‖ ≤ (r⁻¹)^2*C ∧
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (innerPatchBump r hr c))) x‖ ≤ (r⁻¹)^3*C) ∧
      (‖fderiv ℝ (outerPatchBump r hr c) x‖ ≤ r⁻¹*C ∧
        ‖fderiv ℝ (fderiv ℝ (outerPatchBump r hr c)) x‖ ≤ (r⁻¹)^2*C ∧
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (outerPatchBump r hr c))) x‖ ≤ (r⁻¹)^3*C) := by
  obtain ⟨A,hA,hInner⟩ := smooth_compact_three_jets_bound
    (innerPatchBump_contDiff zero_lt_one (0 : Space n))
    (patchBumps_compactSupport zero_lt_one (0 : Space n)).1
  obtain ⟨B,hB,hOuter⟩ := smooth_compact_three_jets_bound
    (outerPatchBump_contDiff zero_lt_one (0 : Space n))
    (patchBumps_compactSupport zero_lt_one (0 : Space n)).2
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro r hr c x
  have hAC : A ≤ A+B := by linarith
  have hBC : B ≤ A+B := by linarith
  have hrI : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  have hInFun : (innerPatchBump r hr c : Space n → ℝ) =
      rescaleSpatial r c (innerPatchBump 1 zero_lt_one (0 : Space n)) := by
    funext y
    exact innerPatchBump_scaling hr c y
  have hOutFun : (outerPatchBump r hr c : Space n → ℝ) =
      rescaleSpatial r c (outerPatchBump 1 zero_lt_one (0 : Space n)) := by
    funext y
    exact outerPatchBump_scaling hr c y
  have hIn := rescaleSpatial_three_jets_bound hr c
    (innerPatchBump_contDiff zero_lt_one (0 : Space n)) hInner x
  have hOut := rescaleSpatial_three_jets_bound hr c
    (outerPatchBump_contDiff zero_lt_one (0 : Space n)) hOuter x
  rw [hInFun,hOutFun]
  exact ⟨⟨hIn.1.trans (mul_le_mul_of_nonneg_left hAC hrI),
    hIn.2.1.trans (mul_le_mul_of_nonneg_left hAC (pow_nonneg hrI 2)),
    hIn.2.2.trans (mul_le_mul_of_nonneg_left hAC (pow_nonneg hrI 3))⟩,
    ⟨hOut.1.trans (mul_le_mul_of_nonneg_left hBC hrI),
    hOut.2.1.trans (mul_le_mul_of_nonneg_left hBC (pow_nonneg hrI 2)),
    hOut.2.2.trans (mul_le_mul_of_nonneg_left hBC (pow_nonneg hrI 3))⟩⟩

theorem outerPatchBump_jets_zero_of_norm_gt {n : ℕ} {r : ℝ} (hr : 0 < r)
    {c x : Space n} (hx : 2*r < ‖x-c‖) :
    outerPatchBump r hr c x = 0 ∧ fderiv ℝ (outerPatchBump r hr c) x = 0 ∧
      fderiv ℝ (fderiv ℝ (outerPatchBump r hr c)) x = 0 := by
  have hnot : x ∉ tsupport (outerPatchBump r hr c) := by
    rw [(outerPatchBump r hr c).tsupport_eq]
    simpa only [Metric.mem_closedBall,dist_eq_norm,outerPatchBump,not_le] using hx
  refine ⟨image_eq_zero_of_notMem_tsupport hnot,fderiv_of_notMem_tsupport ℝ hnot,?_⟩
  exact fderiv_of_notMem_tsupport ℝ (fun h => hnot (tsupport_fderiv_subset ℝ h))

theorem exteriorCutoff_eventually_zero {n : ℕ} (s : Finset (Space n)) {r : ℝ}
    (hr : 0 < r) {x : Space n} (hx : 1 ≤ patchSum s r hr x) :
    exteriorCutoff s r hr =ᶠ[𝓝 x] 0 := by
  have hSum : ∀ᶠ y in 𝓝 x, (3/4 : ℝ) < patchSum s r hr y :=
    (patchSum_contDiff s hr).continuous.continuousAt.eventually
      (lt_mem_nhds (by linarith))
  filter_upwards [hSum] with y hy
  exact exteriorPatchFactor_eq_zero hy.le

theorem exteriorCutoff_jets_zero {n : ℕ} (s : Finset (Space n)) {r : ℝ}
    (hr : 0 < r) {x : Space n} (hx : 1 ≤ patchSum s r hr x) :
    exteriorCutoff s r hr x = 0 ∧ fderiv ℝ (exteriorCutoff s r hr) x = 0 ∧
      fderiv ℝ (fderiv ℝ (exteriorCutoff s r hr)) x = 0 := by
  have hZero := exteriorCutoff_eventually_zero s hr hx
  refine ⟨hZero.eq_of_nhds,?_,?_⟩
  · simpa only [fderiv_zero,Pi.zero_apply] using hZero.fderiv_eq (𝕜 := ℝ)
  · simpa only [fderiv_zero,Pi.zero_apply] using
      (hZero.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)

theorem holderBound_spatial_of_bound_fderiv {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {α r L T : ℝ} {g : Space n → V}
    (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hr1 : r ≤ 1) (hL : 0 ≤ L)
    (hg : Differentiable ℝ g) (hgBound : ∀ x, ‖g x‖ ≤ L*r)
    (hgD : ∀ x, ‖fderiv ℝ g x‖ ≤ L) :
    HolderBound α (cylinder Set.univ 0 T) (fun p => g p.1) (2*L*r^(1-α)) := by
  apply holderBound_of_small_lipschitz hα hα1 hr hr1 hL
  · intro p _
    exact hgBound p.1
  · intro x y t _
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
      (fun z _ => hg z) (fun z _ => hgD z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  · intro x s t _ _
    simp only [sub_self,norm_zero]
    exact mul_nonneg hL (abs_nonneg _)

theorem spatial_three_holderBounds {n : ℕ} {α r C T : ℝ} {g : Space n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (hg : ContDiff ℝ ∞ g) (hBound : ∀ x, ‖g x‖ ≤ C)
    (hJets : ∀ x, ‖fderiv ℝ g x‖ ≤ r⁻¹*C ∧
      ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ (r⁻¹)^2*C ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x‖ ≤ (r⁻¹)^3*C) :
    HolderBound α (cylinder Set.univ 0 T) (fun p => g p.1)
      (2*(r⁻¹*C)*r^(1-α)) ∧
    HolderBound α (cylinder Set.univ 0 T) (fun p => fderiv ℝ g p.1)
      (2*((r⁻¹)^2*C)*r^(1-α)) ∧
    HolderBound α (cylinder Set.univ 0 T) (fun p => fderiv ℝ (fderiv ℝ g) p.1)
      (2*((r⁻¹)^3*C)*r^(1-α)) := by
  have hrI : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  have hgD : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have hgDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ g)) := hgD.fderiv_right (by simp)
  have hScale0 : (r⁻¹*C)*r = C := by field_simp
  have hScale1 : ((r⁻¹)^2*C)*r = r⁻¹*C := by field_simp
  have hScale2 : ((r⁻¹)^3*C)*r = (r⁻¹)^2*C := by field_simp
  refine ⟨holderBound_spatial_of_bound_fderiv hα hα1 hr hr1
    (mul_nonneg hrI hC) (hg.differentiable (by simp)) ?_ (fun x => (hJets x).1),?_,?_⟩
  · simpa only [hScale0] using hBound
  · apply holderBound_spatial_of_bound_fderiv hα hα1 hr hr1
      (mul_nonneg (pow_nonneg hrI 2) hC) (hgD.differentiable (by simp))
      (fun x => ?_) (fun x => (hJets x).2.1)
    simpa only [hScale1] using (hJets x).1
  · apply holderBound_spatial_of_bound_fderiv hα hα1 hr hr1
      (mul_nonneg (pow_nonneg hrI 3) hC) (hgDD.differentiable (by simp))
      (fun x => ?_) (fun x => (hJets x).2.2)
    simpa only [hScale2] using (hJets x).2.1

theorem patchBumps_uniform_three_holderBounds {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 → ∀ (T : ℝ) (c : Space n)
      (g : Space n → ℝ),
      (g = innerPatchBump r hr c ∨ g = outerPatchBump r hr c) →
      HolderBound α (cylinder Set.univ 0 T) (fun p => g p.1)
        (2*(r⁻¹*C)*r^(1-α)) ∧
      HolderBound α (cylinder Set.univ 0 T) (fun p => fderiv ℝ g p.1)
        (2*((r⁻¹)^2*C)*r^(1-α)) ∧
      HolderBound α (cylinder Set.univ 0 T) (fun p => fderiv ℝ (fderiv ℝ g) p.1)
        (2*((r⁻¹)^3*C)*r^(1-α)) := by
  obtain ⟨A,hA,hJets⟩ := patchBumps_uniform_three_jets_bound (n := n)
  let C : ℝ := 1+A
  have hC : 0 < C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  have h1C : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro r hr hr1 T c g hG
  have hg : ContDiff ℝ ∞ g := by
    rcases hG with rfl | rfl
    · exact innerPatchBump_contDiff hr _
    · exact outerPatchBump_contDiff hr _
  have hBound : ∀ x, ‖g x‖ ≤ C := by
    intro x
    rcases hG with rfl | rfl
    · rw [Real.norm_eq_abs,abs_of_nonneg (innerPatchBump r hr c).nonneg]
      exact (innerPatchBump r hr c).le_one.trans h1C
    · rw [Real.norm_eq_abs,abs_of_nonneg (outerPatchBump r hr c).nonneg]
      exact (outerPatchBump r hr c).le_one.trans h1C
  apply spatial_three_holderBounds hα hα1 hr hr1 hC.le hg hBound
  intro x
  have hRaw : ‖fderiv ℝ g x‖ ≤ r⁻¹*A ∧
      ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ (r⁻¹)^2*A ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x‖ ≤ (r⁻¹)^3*A := by
    rcases hG with rfl | rfl
    · exact (hJets r hr c x).1
    · exact (hJets r hr c x).2
  have hrI : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  exact ⟨hRaw.1.trans (mul_le_mul_of_nonneg_left hAC hrI),
    hRaw.2.1.trans (mul_le_mul_of_nonneg_left hAC (pow_nonneg hrI 2)),
    hRaw.2.2.trans (mul_le_mul_of_nonneg_left hAC (pow_nonneg hrI 3))⟩

theorem innerPatchBump_overlap_bound {n : ℕ} {r : ℝ} (hr : 0 < r)
    (s : Finset (Space n))
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) (x : Space n) :
    (s.filter (fun c => innerPatchBump r hr c x ≠ 0)).card ≤
      5^(Module.finrank ℝ (Space n)) := by
  classical
  apply (Finset.card_le_card (show
    s.filter (fun c => innerPatchBump r hr c x ≠ 0) ⊆
      s.filter (fun c => ‖c-x‖ ≤ 2*r) from ?_)).trans
    (separated_centers_overlap_bound hr s hSep x)
  intro c hc
  obtain ⟨hcs,hcx⟩ := Finset.mem_filter.mp hc
  refine Finset.mem_filter.mpr ⟨hcs,?_⟩
  have hNorm := innerPatchBump_nonzero_norm_lt hr hcx
  rw [norm_sub_rev]
  linarith

theorem patchSum_le_overlap_bound {n : ℕ} {r : ℝ} (hr : 0 < r)
    (s : Finset (Space n))
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) (x : Space n) :
    patchSum s r hr x ≤ (5^(Module.finrank ℝ (Space n)) : ℕ) := by
  classical
  let t : Finset (Space n) := s.filter (fun c => innerPatchBump r hr c x ≠ 0)
  have heq : (∑ c ∈ t, innerPatchBump r hr c x) = patchSum s r hr x :=
    Finset.sum_filter_ne_zero s
  have hCard : (t.card : ℝ) ≤ (5^(Module.finrank ℝ (Space n)) : ℕ) := by
    exact_mod_cast innerPatchBump_overlap_bound hr s hSep x
  calc
    _ = ∑ c ∈ t, innerPatchBump r hr c x := heq.symm
    _ ≤ ∑ _c ∈ t, (1 : ℝ) :=
      Finset.sum_le_sum (fun c _ => (innerPatchBump r hr c).le_one)
    _ = (t.card : ℝ) := by simp
    _ ≤ _ := hCard

theorem patchSum_uniform_holderBound {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) → ∀ T : ℝ,
      HolderBound α (cylinder Set.univ 0 T) (fun p => patchSum s r hr p.1)
        (C*r⁻¹*r^(1-α)) := by
  obtain ⟨A,hA,hHolder⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  let M : ℕ := 5^(Module.finrank ℝ (Space n))
  let C : ℝ := 4*(M : ℝ)*A
  have hC : 0 < C := by dsimp [C,M]; positivity
  refine ⟨C,hC,?_⟩
  intro s r hr hr1 hSep T
  have hBudget : 0 ≤ 2*(r⁻¹*A)*r^(1-α) := by positivity
  have hEach : ∀ c ∈ s, HolderBound α (cylinder Set.univ 0 T)
      (fun p => innerPatchBump r hr c p.1) (2*(r⁻¹*A)*r^(1-α)) := by
    intro c _
    exact (hHolder r hr hr1 T c _ (Or.inl rfl)).1
  have hOverlap : ∀ p ∈ cylinder Set.univ 0 T,
      (s.filter (fun c => innerPatchBump r hr c p.1 ≠ 0)).card ≤ M := by
    intro p _
    exact innerPatchBump_overlap_bound hr s hSep p.1
  have h := holderBound_sum_boundedOverlap s hBudget hEach hOverlap
  have hScale : 2*(M : ℝ)*(2*(r⁻¹*A)*r^(1-α)) = C*r⁻¹*r^(1-α) := by
    dsimp [C]
    ring
  simpa only [patchSum,hScale] using h

end Yau.LeafProofs.L16Aux
