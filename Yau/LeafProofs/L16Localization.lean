import spec.CHAIN.ParabolicCandidates
import Mathlib.Analysis.Calculus.MeanValue

/-! Smooth spatial cutoffs used only by the L16 parabolic parametrix. -/

open MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L16Aux

open Yau.Parabolic

def innerPatchBump {n : ℕ} (r : ℝ) (hr : 0 < r) (c : Space n) : ContDiffBump c :=
  ⟨r, 3*r/2, hr, by linarith⟩

def outerPatchBump {n : ℕ} (r : ℝ) (hr : 0 < r) (c : Space n) : ContDiffBump c :=
  ⟨3*r/2, 2*r, by positivity, by linarith⟩

theorem innerPatchBump_contDiff {n : ℕ} {r : ℝ} (hr : 0 < r) (c : Space n) :
    ContDiff ℝ ∞ (innerPatchBump r hr c : Space n → ℝ) :=
  (innerPatchBump r hr c).contDiff

theorem outerPatchBump_contDiff {n : ℕ} {r : ℝ} (hr : 0 < r) (c : Space n) :
    ContDiff ℝ ∞ (outerPatchBump r hr c : Space n → ℝ) :=
  (outerPatchBump r hr c).contDiff

theorem innerPatchBump_eq_one {n : ℕ} {r : ℝ} (hr : 0 < r) {c x : Space n}
    (hx : ‖x-c‖ ≤ r) : innerPatchBump r hr c x = 1 :=
  (innerPatchBump r hr c).one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_eq_norm, innerPatchBump] using hx)

theorem outerPatchBump_mul_innerPatchBump {n : ℕ} {r : ℝ} (hr : 0 < r)
    (c x : Space n) : outerPatchBump r hr c x*innerPatchBump r hr c x =
      innerPatchBump r hr c x := by
  by_cases hη : innerPatchBump r hr c x = 0
  · simp only [hη, mul_zero]
  have hx : x ∈ Metric.ball c (3*r/2) := by
    change x ∈ Metric.ball c (innerPatchBump r hr c).rOut
    rw [← (innerPatchBump r hr c).support_eq]
    exact hη
  have hφ : outerPatchBump r hr c x = 1 :=
    (outerPatchBump r hr c).one_of_mem_closedBall (by
      exact Metric.ball_subset_closedBall hx)
  rw [hφ, one_mul]

theorem innerPatchBump_nonzero_norm_lt {n : ℕ} {r : ℝ} (hr : 0 < r)
    {c x : Space n} (hx : innerPatchBump r hr c x ≠ 0) : ‖x-c‖ < 3*r/2 := by
  have hmem : x ∈ Function.support (innerPatchBump r hr c) := hx
  rw [(innerPatchBump r hr c).support_eq] at hmem
  simpa only [Metric.mem_ball, dist_eq_norm, innerPatchBump] using hmem

theorem outerPatchBump_nonzero_norm_lt {n : ℕ} {r : ℝ} (hr : 0 < r)
    {c x : Space n} (hx : outerPatchBump r hr c x ≠ 0) : ‖x-c‖ < 2*r := by
  have hmem : x ∈ Function.support (outerPatchBump r hr c) := hx
  rw [(outerPatchBump r hr c).support_eq] at hmem
  simpa only [Metric.mem_ball, dist_eq_norm, outerPatchBump] using hmem

theorem patchBumps_compactSupport {n : ℕ} {r : ℝ} (hr : 0 < r) (c : Space n) :
    HasCompactSupport (innerPatchBump r hr c : Space n → ℝ) ∧
      HasCompactSupport (outerPatchBump r hr c : Space n → ℝ) :=
  ⟨(innerPatchBump r hr c).hasCompactSupport, (outerPatchBump r hr c).hasCompactSupport⟩


open scoped Classical in
theorem separated_centers_overlap_bound {n : ℕ} {r : ℝ} (hr : 0 < r)
    (s : Finset (Space n))
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) (x : Space n) :
    (s.filter (fun c => ‖c-x‖ ≤ 2*r)).card ≤ 5^(Module.finrank ℝ (Space n)) := by
  classical
  let t : Finset (Space n) := s.filter (fun c => ‖c-x‖ ≤ 2*r)
  let F : Space n → Space n := fun c => r⁻¹ • (c-x)
  have hF : Function.Injective F := by
    intro c d h
    simpa [F,smul_smul,hr.ne'] using congrArg (fun z : Space n => r • z+x) h
  have hFN (c : Space n) : ‖F c‖ = ‖c-x‖/r := by
    dsimp [F]
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
    ring
  have hFD (c d : Space n) : ‖F c-F d‖ = ‖c-d‖/r := by
    have heq : F c-F d = r⁻¹ • (c-d) := by
      dsimp [F]
      rw [← smul_sub]
      congr 1
      abel
    rw [heq,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
    ring
  have hCard := Besicovitch.card_le_of_separated (t.image F) (by
    intro y hy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    rw [hFN]
    exact (div_le_iff₀ hr).mpr (Finset.mem_filter.mp hc).2) (by
    intro y hy z hz hyz
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hz
    rw [hFD]
    apply (le_div_iff₀ hr).mpr
    simpa only [one_mul] using hSep c (Finset.mem_filter.mp hc).1 d
      (Finset.mem_filter.mp hd).1 (fun h => hyz (congrArg F h)))
  simpa only [Finset.card_image_of_injective t hF] using hCard

theorem compact_separated_finite_cover {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) :
    ∃ s : Finset (Space n), (∀ c ∈ s, c ∈ K) ∧
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) ∧
      ∀ x ∈ K, ∃ c ∈ s, ‖x-c‖ ≤ r := by
  classical
  let ε : NNReal := ⟨r,hr.le⟩
  have hεpos : 0 < ε := by exact_mod_cast hr
  have hε : ε ≠ 0 := hεpos.ne'
  obtain ⟨N,hNK,hNfin,hN⟩ := Metric.exists_finite_isCover_of_isCompact
    (ε := ε/2) (by positivity : ε/2 ≠ 0) hK
  have hPN : Metric.packingNumber ε K ≠ ⊤ := by
    have hBound : Metric.packingNumber ε K ≤ N.encard := by
      calc
        _ = Metric.packingNumber (2*(ε/2)) K := by congr 1; ring
        _ ≤ Metric.externalCoveringNumber (ε/2) K :=
          Metric.packingNumber_two_mul_le_externalCoveringNumber (ε/2) K
        _ ≤ N.encard := hN.externalCoveringNumber_le_encard
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hNfin) hBound
  let C := Metric.maximalSeparatedSet ε K
  have hCfin : C.Finite := by
    apply Set.encard_ne_top_iff.mp
    change (Metric.maximalSeparatedSet ε K).encard ≠ ⊤
    rw [Metric.encard_maximalSeparatedSet hPN]
    exact hPN
  have hCS : Metric.IsSeparated ε C := Metric.isSeparated_maximalSeparatedSet
  have hCover : Metric.IsCover ε K C := Metric.isCover_maximalSeparatedSet hPN
  refine ⟨hCfin.toFinset,?_,?_,?_⟩
  · intro c hc
    exact Metric.maximalSeparatedSet_subset (hCfin.mem_toFinset.mp hc)
  · intro c hc d hd hcd
    have h := hCS (hCfin.mem_toFinset.mp hc) (hCfin.mem_toFinset.mp hd) hcd
    have hdN : ε < nndist c d := by
      simpa only [edist_nndist,ENNReal.coe_lt_coe] using h
    have hdR : r < dist c d := by exact_mod_cast hdN
    simpa only [dist_eq_norm] using hdR.le
  · intro x hx
    obtain ⟨c,hc,hd⟩ := hCover hx
    refine ⟨c,hCfin.mem_toFinset.mpr hc,?_⟩
    change edist x c ≤ (ε : ENNReal) at hd
    have hdN : nndist x c ≤ ε := by
      simpa only [edist_nndist,ENNReal.coe_le_coe] using hd
    have hdR : dist x c ≤ r := by exact_mod_cast hdN
    simpa only [dist_eq_norm] using hdR


theorem holderBound_smul_refined {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {α A B C D : ℝ} {Q : Set (Point n)} {q : Point n → ℝ} {H : Point n → V}
    (hq : HolderBound α Q q B) (hH : HolderBound α Q H C) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hqSup : ∀ p ∈ Q, |q p| ≤ A) (hHSup : ∀ p ∈ Q, ‖H p‖ ≤ D) :
    HolderBound α Q (fun p => q p • H p) (A*C+B*D) := by
  refine ⟨add_nonneg (mul_nonneg hA hH.1) (mul_nonneg hq.1 hD),?_,?_⟩
  · intro p hp
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (hqSup p hp) (hH.2.1 p hp) (norm_nonneg _) hA).trans
      (le_add_of_nonneg_right (mul_nonneg hq.1 hD))
  · intro p hp r hr
    have hW : 0 ≤ holderWeight α p r := by dsimp [holderWeight]; positivity
    have heq : q p • H p-q r • H r =
        q p • (H p-H r)+(q p-q r) • H r := by
      rw [smul_sub,sub_smul]
      abel
    rw [heq]
    calc
      _ ≤ ‖q p • (H p-H r)‖+‖(q p-q r) • H r‖ := norm_add_le _ _
      _ = |q p| *‖H p-H r‖+‖q p-q r‖*‖H r‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs (q p)]
      _ ≤ A*(C*holderWeight α p r)+(B*holderWeight α p r)*D :=
        add_le_add
          (mul_le_mul (hqSup p hp) (hH.2.2 p hp r hr) (norm_nonneg _) hA)
          (mul_le_mul (hq.2.2 p hp r hr) (hHSup r hr) (norm_nonneg _)
            (mul_nonneg hq.1 hW))
      _ = _ := by ring

theorem small_lipschitz_holder_scale {A L d r γ : ℝ} (hr : 0 < r) (hd : 0 ≤ d)
    (hL : 0 ≤ L) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hSmall : A ≤ 2*L*r) (hLip : A ≤ L*d) : A ≤ 2*L*r^(1-γ)*d^γ := by
  by_cases hd0 : d = 0
  · subst d
    simpa only [mul_zero,Real.zero_rpow hγ.ne'] using hLip
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  have hPower (z : ℝ) (hz : 0 < z) : z^(1-γ)*z^γ = z := by
    rw [← Real.rpow_add hz]
    have hExp : (1-γ)+γ = 1 := by ring
    rw [hExp,Real.rpow_one]
  rcases le_total d r with hdr | hrd
  · have hMono := Real.rpow_le_rpow hd hdr (by linarith : 0 ≤ 1-γ)
    have hD : d ≤ r^(1-γ)*d^γ := by
      calc
        _ = d^(1-γ)*d^γ := (hPower d hdpos).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hMono (Real.rpow_nonneg hd _)
    have hR : 0 ≤ L*r^(1-γ)*d^γ := by positivity
    calc
      A ≤ L*d := hLip
      _ ≤ L*(r^(1-γ)*d^γ) := mul_le_mul_of_nonneg_left hD hL
      _ ≤ _ := by nlinarith
  · have hMono := Real.rpow_le_rpow hr.le hrd hγ.le
    have hR : r ≤ r^(1-γ)*d^γ := by
      calc
        _ = r^(1-γ)*r^γ := (hPower r hr).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hMono (Real.rpow_nonneg hr.le _)
    exact hSmall.trans (by
      calc
        _ ≤ (2*L)*(r^(1-γ)*d^γ) := mul_le_mul_of_nonneg_left hR (by positivity)
        _ = _ := by ring)

theorem holderBound_of_small_lipschitz {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α r L T : ℝ} {f : Point n → V} (hα : 0 < α) (hα1 : α < 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hL : 0 ≤ L)
    (hBound : ∀ p ∈ cylinder Set.univ 0 T, ‖f p‖ ≤ L*r)
    (hSpace : ∀ (x y : Space n) (t : ℝ), t ∈ Set.Icc 0 T →
      ‖f (x,t)-f (y,t)‖ ≤ L*‖x-y‖)
    (hTime : ∀ (x : Space n) (s t : ℝ), s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      ‖f (x,s)-f (x,t)‖ ≤ L*|s-t|) :
    HolderBound α (cylinder Set.univ 0 T) f (2*L*r^(1-α)) := by
  have hBudget0 : 0 ≤ 2*L*r^(1-α) := by positivity
  have hrPow : r ≤ r^(1-α) := Real.self_le_rpow_of_le_one hr.le hr1 (by linarith)
  have hAmp : L*r ≤ 2*L*r^(1-α) := by
    have h1 := mul_le_mul_of_nonneg_left hrPow hL
    have h2 : 0 ≤ L*r^(1-α) := by positivity
    nlinarith
  refine ⟨hBudget0,fun p hp => (hBound p hp).trans hAmp,?_⟩
  intro p hp q hq
  let m : Point n := (q.1,p.2)
  have hm : m ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,hp.2⟩
  have h1Small : ‖f p-f m‖ ≤ 2*L*r :=
    (norm_sub_le _ _).trans ((add_le_add (hBound p hp) (hBound m hm)).trans_eq (by ring))
  have h2Small : ‖f m-f q‖ ≤ 2*L*r :=
    (norm_sub_le _ _).trans ((add_le_add (hBound m hm) (hBound q hq)).trans_eq (by ring))
  have h1 := small_lipschitz_holder_scale hr (norm_nonneg (p.1-q.1)) hL hα hα1.le
    h1Small (hSpace p.1 q.1 p.2 hp.2)
  have h2 := small_lipschitz_holder_scale hr (abs_nonneg (p.2-q.2)) hL
    (by positivity : 0 < α/2) (by linarith : α/2 ≤ 1) h2Small (hTime q.1 p.2 q.2 hp.2 hq.2)
  have hPow : r^(1-α/2) ≤ r^(1-α) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  calc
    _ ≤ ‖f p-f m‖+‖f m-f q‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2*L*r^(1-α)*‖p.1-q.1‖^α+2*L*r^(1-α/2)*|p.2-q.2|^(α/2) := add_le_add h1 h2
    _ ≤ 2*L*r^(1-α)*‖p.1-q.1‖^α+2*L*r^(1-α)*|p.2-q.2|^(α/2) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPow (by positivity : 0 ≤ 2*L))
        (Real.rpow_nonneg (abs_nonneg _) _))
    _ = _ := by dsimp [holderWeight]; ring


def patchDenominator (z : ℝ) : ℝ := z+1-Real.smoothTransition (4*z-1)

def exteriorPatchFactor (z : ℝ) : ℝ := 1-Real.smoothTransition (4*z-2)

theorem patchDenominator_lower {z : ℝ} (hz : 0 ≤ z) : (1/4 : ℝ) ≤ patchDenominator z := by
  by_cases hz1 : z ≤ 1/4
  · have hχ : Real.smoothTransition (4*z-1) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    dsimp [patchDenominator]
    rw [hχ]
    linarith
  · have hχ := Real.smoothTransition.le_one (4*z-1)
    dsimp [patchDenominator]
    linarith

theorem patchDenominator_eq_self {z : ℝ} (hz : (1/2 : ℝ) ≤ z) : patchDenominator z = z := by
  have hχ : Real.smoothTransition (4*z-1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  simp only [patchDenominator,hχ,add_sub_cancel_right]

theorem exteriorPatchFactor_eq_one {z : ℝ} (hz : z ≤ (1/2 : ℝ)) :
    exteriorPatchFactor z = 1 := by
  have hχ : Real.smoothTransition (4*z-2) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  simp only [exteriorPatchFactor,hχ,sub_zero]

theorem exteriorPatchFactor_eq_zero {z : ℝ} (hz : (3/4 : ℝ) ≤ z) :
    exteriorPatchFactor z = 0 := by
  have hχ : Real.smoothTransition (4*z-2) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  simp only [exteriorPatchFactor,hχ,sub_self]

theorem exteriorPatchFactor_residual {z : ℝ} (hz : 0 ≤ z) :
    exteriorPatchFactor z*(1-z/patchDenominator z) = 1-z/patchDenominator z := by
  rcases le_total z (1/2 : ℝ) with h | h
  · rw [exteriorPatchFactor_eq_one h,one_mul]
  · rw [patchDenominator_eq_self h,div_self (by linarith : z ≠ 0),sub_self,mul_zero]

theorem finite_normalized_partition {n : ℕ} {ι : Type*} (s : Finset ι)
    (η φ : ι → Space n → ℝ) (hη : ∀ i ∈ s, ∀ x, 0 ≤ η i x)
    (hφη : ∀ i ∈ s, ∀ x, φ i x*η i x = η i x) (x : Space n) :
    (∑ i ∈ s, φ i x*(η i x/patchDenominator (∑ j ∈ s, η j x)))+
      exteriorPatchFactor (∑ j ∈ s, η j x)*
        (1-(∑ j ∈ s, η j x)/patchDenominator (∑ j ∈ s, η j x)) = 1 := by
  have hZ : 0 ≤ ∑ j ∈ s, η j x := Finset.sum_nonneg (fun j hj => hη j hj x)
  have hTerm (i : ι) (hi : i ∈ s) :
      φ i x*(η i x/patchDenominator (∑ j ∈ s, η j x)) =
        η i x/patchDenominator (∑ j ∈ s, η j x) := by
    rw [← mul_div_assoc,hφη i hi x]
  rw [Finset.sum_congr rfl hTerm,← Finset.sum_div,exteriorPatchFactor_residual hZ]
  ring

theorem patchDenominator_contDiff : ContDiff ℝ ∞ patchDenominator := by
  unfold patchDenominator
  fun_prop

theorem exteriorPatchFactor_contDiff : ContDiff ℝ ∞ exteriorPatchFactor := by
  unfold exteriorPatchFactor
  fun_prop

theorem finite_normalized_cutoff_contDiff {n : ℕ} {ι : Type*} (s : Finset ι)
    (η : ι → Space n → ℝ) (hη : ∀ i ∈ s, ∀ x, 0 ≤ η i x)
    (hSmooth : ∀ i ∈ s, ContDiff ℝ ∞ (η i)) {i : ι} (hi : i ∈ s) :
    ContDiff ℝ ∞ (fun x => η i x/patchDenominator (∑ j ∈ s, η j x)) := by
  have hSum : ContDiff ℝ ∞ (fun x => ∑ j ∈ s, η j x) := ContDiff.sum hSmooth
  apply (hSmooth i hi).div (patchDenominator_contDiff.comp hSum)
  intro x
  have hZ : 0 ≤ ∑ j ∈ s, η j x := Finset.sum_nonneg (fun j hj => hη j hj x)
  exact (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/4) (patchDenominator_lower hZ)).ne'


def patchSum {n : ℕ} (s : Finset (Space n)) (r : ℝ) (hr : 0 < r) (x : Space n) : ℝ :=
  ∑ c ∈ s, innerPatchBump r hr c x

def normalizedPatchCutoff {n : ℕ} (s : Finset (Space n)) (r : ℝ) (hr : 0 < r)
    (c x : Space n) : ℝ := innerPatchBump r hr c x/patchDenominator (patchSum s r hr x)

def exteriorCutoff {n : ℕ} (s : Finset (Space n)) (r : ℝ) (hr : 0 < r)
    (x : Space n) : ℝ := exteriorPatchFactor (patchSum s r hr x)

def exteriorSourceCutoff {n : ℕ} (s : Finset (Space n)) (r : ℝ) (hr : 0 < r)
    (x : Space n) : ℝ := 1-patchSum s r hr x/patchDenominator (patchSum s r hr x)

theorem patchSum_nonneg {n : ℕ} (s : Finset (Space n)) {r : ℝ} (hr : 0 < r)
    (x : Space n) : 0 ≤ patchSum s r hr x :=
  Finset.sum_nonneg (fun c _ => (innerPatchBump r hr c).nonneg)

theorem patchSum_contDiff {n : ℕ} (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (patchSum s r hr) :=
  ContDiff.sum (fun c _ => innerPatchBump_contDiff hr c)

theorem normalizedPatchCutoff_contDiff {n : ℕ} (s : Finset (Space n)) {r : ℝ}
    (hr : 0 < r) {c : Space n} (hc : c ∈ s) :
    ContDiff ℝ ∞ (normalizedPatchCutoff s r hr c) :=
  finite_normalized_cutoff_contDiff s (fun c => innerPatchBump r hr c)
    (fun c _ _ => (innerPatchBump r hr c).nonneg)
    (fun c _ => innerPatchBump_contDiff hr c) hc

theorem exteriorCutoff_contDiff {n : ℕ} (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (exteriorCutoff s r hr) :=
  exteriorPatchFactor_contDiff.comp (patchSum_contDiff s hr)

theorem patchDenominator_ge {z : ℝ} : z ≤ patchDenominator z := by
  have hχ := Real.smoothTransition.le_one (4*z-1)
  dsimp only [patchDenominator]
  linarith

theorem patchDenominator_pos {z : ℝ} (hz : 0 ≤ z) : 0 < patchDenominator z :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/4) (patchDenominator_lower hz)

theorem exteriorSourceCutoff_contDiff {n : ℕ} (s : Finset (Space n)) {r : ℝ}
    (hr : 0 < r) : ContDiff ℝ ∞ (exteriorSourceCutoff s r hr) := by
  apply contDiff_const.sub
  exact (patchSum_contDiff s hr).div
    (patchDenominator_contDiff.comp (patchSum_contDiff s hr))
    (fun x => (patchDenominator_pos (patchSum_nonneg s hr x)).ne')

theorem exteriorSourceCutoff_mem_Icc {n : ℕ} (s : Finset (Space n)) {r : ℝ}
    (hr : 0 < r) (x : Space n) : exteriorSourceCutoff s r hr x ∈ Set.Icc 0 1 := by
  have hZ := patchSum_nonneg s hr x
  have hD := patchDenominator_pos hZ
  have hquot0 := div_nonneg hZ hD.le
  have hquot1 : patchSum s r hr x/patchDenominator (patchSum s r hr x) ≤ 1 :=
    (div_le_one hD).mpr patchDenominator_ge
  change 0 ≤ 1-_ ∧ 1-_ ≤ 1
  constructor <;> linarith

theorem normalizedPatchCutoff_nonneg {n : ℕ} (s : Finset (Space n)) {r : ℝ}
    (hr : 0 < r) (c x : Space n) : 0 ≤ normalizedPatchCutoff s r hr c x :=
  div_nonneg (innerPatchBump r hr c).nonneg
    (patchDenominator_pos (patchSum_nonneg s hr x)).le

theorem normalizedPatchCutoff_le_one {n : ℕ} (s : Finset (Space n)) {r : ℝ}
    (hr : 0 < r) {c : Space n} (hc : c ∈ s) (x : Space n) :
    normalizedPatchCutoff s r hr c x ≤ 1 := by
  apply (div_le_one (patchDenominator_pos (patchSum_nonneg s hr x))).mpr
  exact (Finset.single_le_sum (fun d _ => (innerPatchBump r hr d).nonneg) hc).trans
    patchDenominator_ge

theorem normalizedPatchCutoff_zero_of_norm_ge {n : ℕ} (s : Finset (Space n))
    {r : ℝ} (hr : 0 < r) {c x : Space n} (hx : 3*r/2 ≤ ‖x-c‖) :
    normalizedPatchCutoff s r hr c x = 0 := by
  have hη : innerPatchBump r hr c x = 0 :=
    (innerPatchBump r hr c).zero_of_le_dist (by
      simpa only [dist_eq_norm, innerPatchBump] using hx)
  simp only [normalizedPatchCutoff, hη, zero_div]

theorem exteriorCutoffs_zero_of_patchSum_ge_one {n : ℕ} (s : Finset (Space n))
    {r : ℝ} (hr : 0 < r) {x : Space n} (hx : 1 ≤ patchSum s r hr x) :
    exteriorCutoff s r hr x = 0 ∧ exteriorSourceCutoff s r hr x = 0 := by
  constructor
  · exact exteriorPatchFactor_eq_zero (by linarith)
  · dsimp only [exteriorSourceCutoff]
    rw [patchDenominator_eq_self (by linarith), div_self (by linarith), sub_self]

theorem patchCutoffs_partition {n : ℕ} (s : Finset (Space n)) {r : ℝ} (hr : 0 < r)
    (x : Space n) :
    (∑ c ∈ s, outerPatchBump r hr c x*normalizedPatchCutoff s r hr c x)+
      exteriorCutoff s r hr x*exteriorSourceCutoff s r hr x = 1 :=
  finite_normalized_partition s (fun c => innerPatchBump r hr c)
    (fun c => outerPatchBump r hr c) (fun c _ _ => (innerPatchBump r hr c).nonneg)
    (fun c _ x => outerPatchBump_mul_innerPatchBump hr c x) x

/-- A finite spatial localization whose overlap depends only on the dimension.
The extra exterior patch vanishes on the prescribed compact set. -/
theorem compact_separated_patch_partition {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) :
    ∃ s : Finset (Space n), (∀ c ∈ s, c ∈ K) ∧
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) ∧
      (∀ x ∈ K, 1 ≤ patchSum s r hr x) ∧
      (∀ x ∈ K, exteriorCutoff s r hr x = 0 ∧ exteriorSourceCutoff s r hr x = 0) ∧
      ∀ x : Space n,
        (s.filter (fun c => outerPatchBump r hr c x ≠ 0)).card ≤
          5^(Module.finrank ℝ (Space n)) := by
  classical
  obtain ⟨s,hsK,hSep,hCover⟩ := compact_separated_finite_cover hK hr
  have hSum : ∀ x ∈ K, 1 ≤ patchSum s r hr x := by
    intro x hx
    obtain ⟨c,hc,hxc⟩ := hCover x hx
    have hη : innerPatchBump r hr c x = 1 := innerPatchBump_eq_one hr hxc
    change 1 ≤ ∑ d ∈ s, innerPatchBump r hr d x
    rw [← hη]
    exact Finset.single_le_sum (fun d _ => (innerPatchBump r hr d).nonneg) hc
  refine ⟨s,hsK,hSep,hSum,?_,?_⟩
  · intro x hx
    exact exteriorCutoffs_zero_of_patchSum_ge_one s hr (hSum x hx)
  · intro x
    apply (Finset.card_le_card (show
      s.filter (fun c => outerPatchBump r hr c x ≠ 0) ⊆
        s.filter (fun c => ‖c-x‖ ≤ 2*r) from ?_)).trans
      (separated_centers_overlap_bound hr s hSep x)
    intro c hc
    obtain ⟨hcs,hcx⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨hcs,?_⟩
    rw [norm_sub_rev]
    exact (outerPatchBump_nonzero_norm_lt hr hcx).le

theorem innerPatchBump_scaling {n : ℕ} {r : ℝ} (hr : 0 < r) (c x : Space n) :
    innerPatchBump r hr c x = innerPatchBump 1 zero_lt_one (0 : Space n)
      (r⁻¹ • (x-c)) := by
  simp only [innerPatchBump, ContDiffBump.toFun, Function.comp_apply,
    inv_one, one_smul, sub_zero]
  congr 1
  field_simp

theorem outerPatchBump_scaling {n : ℕ} {r : ℝ} (hr : 0 < r) (c x : Space n) :
    outerPatchBump r hr c x = outerPatchBump 1 zero_lt_one (0 : Space n)
      (r⁻¹ • (x-c)) := by
  simp only [outerPatchBump, ContDiffBump.toFun, Function.comp_apply, sub_zero]
  have hRatio : (2*r)/(3*r/2) = (2*1)/(3*1/2) := by
    field_simp
  rw [hRatio, smul_smul]
  congr 1
  congr 1
  field_simp

theorem smooth_compact_lipschitz {n : ℕ} {g : Space n → ℝ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y, ‖g x-g y‖ ≤ C*‖x-y‖ := by
  have hgD : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  obtain ⟨A,hA⟩ := (hcg.fderiv ℝ).exists_bound_of_continuous hgD.continuous
  let C : ℝ := 1+|A|
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro x y
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
    (fun z _ => hg.differentiable (by simp) z) (fun z _ => ?_)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  exact (hA z).trans (by dsimp [C]; linarith [le_abs_self A])

/-- All translated and rescaled cutoffs have one Lipschitz constant after
multiplication by the radius. The constant does not count the patches. -/
theorem patchBumps_uniform_lipschitz {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (hr : 0 < r) (c x y : Space n),
      ‖innerPatchBump r hr c x-innerPatchBump r hr c y‖ ≤ C/r*‖x-y‖ ∧
      ‖outerPatchBump r hr c x-outerPatchBump r hr c y‖ ≤ C/r*‖x-y‖ := by
  obtain ⟨A,hA,hInner⟩ := smooth_compact_lipschitz
    (innerPatchBump_contDiff zero_lt_one (0 : Space n))
    (patchBumps_compactSupport zero_lt_one (0 : Space n)).1
  obtain ⟨B,hB,hOuter⟩ := smooth_compact_lipschitz
    (outerPatchBump_contDiff zero_lt_one (0 : Space n))
    (patchBumps_compactSupport zero_lt_one (0 : Space n)).2
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro r hr c x y
  have hArg : r⁻¹ • (x-c)-r⁻¹ • (y-c) = r⁻¹ • (x-y) := by
    rw [← smul_sub]
    congr 1
    abel
  have hNorm : ‖r⁻¹ • (x-c)-r⁻¹ • (y-c)‖ = ‖x-y‖/r := by
    rw [hArg,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
    ring
  constructor
  · rw [innerPatchBump_scaling hr c x,innerPatchBump_scaling hr c y]
    exact (hInner _ _).trans (by
      rw [hNorm]
      have hAC : A ≤ A+B := by linarith
      calc
        A*(‖x-y‖/r) ≤ (A+B)*(‖x-y‖/r) :=
          mul_le_mul_of_nonneg_right hAC (div_nonneg (norm_nonneg _) hr.le)
        _ = _ := by ring)
  · rw [outerPatchBump_scaling hr c x,outerPatchBump_scaling hr c y]
    exact (hOuter _ _).trans (by
      rw [hNorm]
      have hBC : B ≤ A+B := by linarith
      calc
        B*(‖x-y‖/r) ≤ (A+B)*(‖x-y‖/r) :=
          mul_le_mul_of_nonneg_right hBC (div_nonneg (norm_nonneg _) hr.le)
        _ = _ := by ring)


open scoped Classical in
theorem holderBound_sum_boundedOverlap {n : ℕ} {ι V : Type*} [NormedAddCommGroup V]
    (s : Finset ι) {α C : ℝ} {Q : Set (Point n)} {f : ι → Point n → V} {M : ℕ}
    (hC : 0 ≤ C) (hf : ∀ i ∈ s, HolderBound α Q (f i) C)
    (hOverlap : ∀ p ∈ Q, (s.filter (fun i => f i p ≠ 0)).card ≤ M) :
    HolderBound α Q (fun p => ∑ i ∈ s, f i p) (2*(M : ℝ)*C) := by
  classical
  refine ⟨by positivity,?_,?_⟩
  · intro p hp
    let sp : Finset ι := s.filter (fun i => f i p ≠ 0)
    have heq : (∑ i ∈ sp, f i p) = ∑ i ∈ s, f i p := Finset.sum_filter_ne_zero s
    have hcard : (sp.card : ℝ) ≤ M := by exact_mod_cast hOverlap p hp
    calc
      _ = ‖∑ i ∈ sp, f i p‖ := congrArg norm heq.symm
      _ ≤ ∑ i ∈ sp, ‖f i p‖ := norm_sum_le sp _
      _ ≤ ∑ _i ∈ sp, C := Finset.sum_le_sum (fun i hi =>
        (hf i (Finset.mem_filter.mp hi).1).2.1 p hp)
      _ = (sp.card : ℝ)*C := by simp
      _ ≤ (M : ℝ)*C := mul_le_mul_of_nonneg_right hcard hC
      _ ≤ 2*(M : ℝ)*C := by
        have hMC : 0 ≤ (M : ℝ)*C := mul_nonneg (Nat.cast_nonneg M) hC
        nlinarith
  · intro p hp q hq
    let sp : Finset ι := s.filter (fun i => f i p ≠ 0)
    let sq : Finset ι := s.filter (fun i => f i q ≠ 0)
    let su : Finset ι := sp ∪ sq
    have hus : su ⊆ s := by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact (Finset.mem_filter.mp hi).1
      · exact (Finset.mem_filter.mp hi).1
    have heq : (∑ i ∈ su, (f i p-f i q)) = ∑ i ∈ s, (f i p-f i q) := by
      apply Finset.sum_subset hus
      intro i hi hnot
      have hp0 : f i p = 0 := by
        by_contra hn
        exact hnot (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hi,hn⟩)))
      have hq0 : f i q = 0 := by
        by_contra hn
        exact hnot (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hi,hn⟩)))
      simp only [hp0,hq0,sub_self]
    have hcardN : su.card ≤ M+M :=
      (Finset.card_union_le sp sq).trans (Nat.add_le_add (hOverlap p hp) (hOverlap q hq))
    have hcard : (su.card : ℝ) ≤ 2*(M : ℝ) := by
      have h : su.card ≤ 2*M := by omega
      exact_mod_cast h
    have hW : 0 ≤ holderWeight α p q := by dsimp [holderWeight]; positivity
    calc
      _ = ‖∑ i ∈ su, (f i p-f i q)‖ := by rw [heq,Finset.sum_sub_distrib]
      _ ≤ ∑ i ∈ su, ‖f i p-f i q‖ := norm_sum_le su _
      _ ≤ ∑ _i ∈ su, C*holderWeight α p q :=
        Finset.sum_le_sum (fun i hi => (hf i (hus hi)).2.2 p hp q hq)
      _ = (su.card : ℝ)*(C*holderWeight α p q) := by simp
      _ ≤ (2*(M : ℝ))*(C*holderWeight α p q) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hC hW)
      _ = _ := by ring


end Yau.LeafProofs.L16Aux
