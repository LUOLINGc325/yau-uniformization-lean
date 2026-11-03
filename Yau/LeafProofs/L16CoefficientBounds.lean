import Yau.LeafProofs.L16

/-! Closed-slab coefficient bounds and genuine spatial jets for the L16 Cauchy construction. -/

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section

namespace Yau.LeafProofs.L16Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem smooth_cylinder_compact_perturbation_bounds {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T : ℝ} (hT : 0 < T)
    {K : Set (Space n)} (hK : IsCompact K) {g : Point n → V} {c : V}
    (hg : ContDiffOn ℝ ∞ g (cylinder Set.univ 0 T))
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T, g (x,t) = c) :
    ∃ C : ℝ, 0 < C ∧
      (∀ p ∈ cylinder Set.univ 0 T, ‖g p‖ ≤ C) ∧
      (∀ p ∈ cylinder Set.univ 0 T,
        ‖fderivWithin ℝ g (cylinder Set.univ 0 T) p‖ ≤ C) ∧
      ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T,
        ‖g p-g q‖ ≤ C*‖p-q‖ := by
  let Q : Set (Point n) := cylinder Set.univ 0 T
  have hUnique : UniqueDiffOn ℝ Q := uniqueDiffOn_univ.prod (uniqueDiffOn_Icc hT)
  have hDCont : ContinuousOn (fderivWithin ℝ g Q) Q :=
    hg.continuousOn_fderivWithin hUnique (by simp)
  let S : Set (Point n) := K ×ˢ Set.Icc 0 T
  have hS : IsCompact S := hK.prod isCompact_Icc
  have hSQ : S ⊆ Q := by
    intro p hp
    exact ⟨Set.mem_univ _,hp.2⟩
  obtain ⟨A,hA⟩ := hS.exists_bound_of_continuousOn (hg.continuousOn.mono hSQ)
  obtain ⟨D,hD⟩ := hS.exists_bound_of_continuousOn (hDCont.mono hSQ)
  let C : ℝ := 1+|A|+|D|+‖c‖
  have hC : 0 < C := by dsimp only [C]; positivity
  have hAC : A ≤ C := by dsimp only [C]; linarith [le_abs_self A,abs_nonneg D,norm_nonneg c]
  have hDC : D ≤ C := by dsimp only [C]; linarith [abs_nonneg A,le_abs_self D,norm_nonneg c]
  have hcC : ‖c‖ ≤ C := by dsimp only [C]; linarith [abs_nonneg A,abs_nonneg D]
  have hValue : ∀ p ∈ Q, ‖g p‖ ≤ C := by
    intro p hp
    by_cases hx : p.1 ∈ K
    · exact (hA p ⟨hx,hp.2⟩).trans hAC
    · rw [hExterior p.1 hx p.2 hp.2]
      exact hcC
  have hOutside : ∀ p ∈ Q, p.1 ∉ K → fderivWithin ℝ g Q p = 0 := by
    intro p hp hx
    have hOut : ∀ᶠ q : Point n in 𝓝 p, q.1 ∉ K :=
      continuous_fst.continuousAt.preimage_mem_nhds (hK.isClosed.isOpen_compl.mem_nhds hx)
    have hEq : g =ᶠ[𝓝[Q] p] (fun _ => c) := by
      filter_upwards [hOut.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with q hqx hq
      exact hExterior q.1 hqx q.2 hq.2
    simpa only [fderivWithin_fun_const,Pi.zero_apply] using
      hEq.fderivWithin_eq (hExterior p.1 hx p.2 hp.2)
  have hDeriv : ∀ p ∈ Q, ‖fderivWithin ℝ g Q p‖ ≤ C := by
    intro p hp
    by_cases hx : p.1 ∈ K
    · exact (hD p ⟨hx,hp.2⟩).trans hDC
    · rw [hOutside p hp hx,norm_zero]
      exact hC.le
  refine ⟨C,hC,hValue,hDeriv,?_⟩
  intro p hp q hq
  exact Convex.norm_image_sub_le_of_norm_fderivWithin_le
    (hg.differentiableOn (by simp)) hDeriv (convex_univ.prod (convex_Icc _ _)) hq hp

theorem smooth_cylinder_compact_perturbation_holder {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T α : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1)
    {K : Set (Space n)} (hK : IsCompact K) {g : Point n → V} {c : V}
    (hg : ContDiffOn ℝ ∞ g (cylinder Set.univ 0 T))
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T, g (x,t) = c) :
    ∃ F : ℝ, 0 < F ∧ HolderBound α (cylinder Set.univ 0 T) g F := by
  obtain ⟨C,hC,hValue,hDeriv,hLip⟩ := smooth_cylinder_compact_perturbation_bounds hT hK hg hExterior
  refine ⟨2*C,by positivity,?_⟩
  have h := holderBound_of_small_lipschitz hα hα1 (r := 1) zero_lt_one le_rfl hC.le
    (fun p hp => by simpa only [mul_one] using hValue p hp) (by
      intro x y t ht
      simpa [Prod.norm_def] using hLip (x,t) ⟨Set.mem_univ _,ht⟩ (y,t) ⟨Set.mem_univ _,ht⟩) (by
      intro x s t hs ht
      simpa [Prod.norm_def,Real.norm_eq_abs] using
        hLip (x,s) ⟨Set.mem_univ _,hs⟩ (x,t) ⟨Set.mem_univ _,ht⟩)
  simpa only [Real.one_rpow,mul_one] using h

theorem frobenius_entry_abs_le {n : ℕ} (A : Mat n) (i j : Yau.RIdx n) :
    |A i j| ≤ ‖A‖ := by
  have hRow := PiLp.norm_apply_le (WithLp.toLp 2 (fun k : Yau.RIdx n => A i k)) j
  have hMatrix := PiLp.norm_apply_le
    (WithLp.toLp 2 (fun l : Yau.RIdx n => WithLp.toLp 2 (fun k : Yau.RIdx n => A l k))) i
  change |A i j| ≤
    ‖WithLp.toLp 2 (fun l : Yau.RIdx n => WithLp.toLp 2 (fun k : Yau.RIdx n => A l k))‖
  simpa only [Real.norm_eq_abs] using hRow.trans hMatrix

theorem holderBound_matrix_entry {n : ℕ} {α M : ℝ} {Q : Set (Point n)}
    {a : Point n → Mat n} (ha : HolderBound α Q a M) (i j : Yau.RIdx n) :
    HolderBound α Q (fun p => a p i j) M := by
  refine ⟨ha.1,?_,?_⟩
  · intro p hp
    simpa only [Real.norm_eq_abs] using (frobenius_entry_abs_le (a p) i j).trans (ha.2.1 p hp)
  · intro p hp q hq
    simpa only [Real.norm_eq_abs,Matrix.sub_apply] using
      (frobenius_entry_abs_le (a p-a q) i j).trans (ha.2.2 p hp q hq)

/-- The leading frozen-coefficient error has a small sup bound on each
patch. The Holder estimate will use this separately from its seminorm. -/
theorem frozen_patch_coefficient_sup_bound {n : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {L r ε τ : ℝ} (hL : 0 ≤ L) (hr : 0 < r)
    (hLip : ∀ p ∈ Q, ∀ q ∈ Q, ‖a p-a q‖ ≤ L*‖p-q‖)
    (c : Space n) (hFrozen : (c,τ) ∈ Q) {p : Point n} (hp : p ∈ Q)
    (hTime : |p.2-τ| ≤ ε) (i j : Yau.RIdx n) :
    |outerPatchBump r hr c p.1*(a (c,τ) i j-a p i j)| ≤ L*(2*r+ε) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hTime
  by_cases hφ : outerPatchBump r hr c p.1 = 0
  · rw [hφ,zero_mul,abs_zero]
    exact mul_nonneg hL (add_nonneg (by positivity) hε)
  have hSpace := outerPatchBump_nonzero_norm_lt hr hφ
  have hDistance : ‖(c,τ)-p‖ ≤ 2*r+ε := by
    change max ‖c-p.1‖ ‖τ-p.2‖ ≤ 2*r+ε
    apply max_le
    · rw [norm_sub_rev]
      linarith
    · rw [Real.norm_eq_abs,abs_sub_comm]
      linarith
  have hEntry : |a (c,τ) i j-a p i j| ≤ L*(2*r+ε) := by
    have h := (frobenius_entry_abs_le (a (c,τ)-a p) i j).trans
      ((hLip (c,τ) hFrozen p hp).trans (mul_le_mul_of_nonneg_left hDistance hL))
    simpa only [Matrix.sub_apply] using h
  rw [abs_mul,abs_of_nonneg (outerPatchBump r hr c).nonneg]
  exact (mul_le_mul (outerPatchBump r hr c).le_one hEntry (abs_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)

def spatialPartial {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : Point n → V) (v : Space n) (p : Point n) : V :=
  fderiv ℝ (fun x => g (x,p.2)) p.1 v

theorem spatialPartial_eq_fderivWithin {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T : ℝ}
    {g : Point n → V} (hg : ContDiffOn ℝ ∞ g (cylinder Set.univ 0 T))
    (v : Space n) {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) :
    spatialPartial g v p = fderivWithin ℝ g (cylinder Set.univ 0 T) p (v,0) := by
  have hArg : HasFDerivAt (fun x : Space n => (x,p.2))
      ((ContinuousLinearMap.id ℝ (Space n)).prod (0 : Space n →L[ℝ] ℝ)) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have hWithin := (hg.differentiableOn (by simp) p hp).hasFDerivWithinAt
  have hSlice := hWithin.comp_hasFDerivAt p.1 hArg (Filter.Eventually.of_forall
    (fun x : Space n => show (x,p.2) ∈ cylinder Set.univ 0 T from ⟨Set.mem_univ _,hp.2⟩))
  have h := congrArg (fun L : Space n →L[ℝ] V => L v) hSlice.fderiv
  simpa only [spatialPartial,Function.comp_def,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,zero_apply] using h

theorem smooth_cylinder_spatialPartial {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T : ℝ} (hT : 0 < T)
    {g : Point n → V} (hg : ContDiffOn ℝ ∞ g (cylinder Set.univ 0 T)) (v : Space n) :
    ContDiffOn ℝ ∞ (spatialPartial g v) (cylinder Set.univ 0 T) := by
  have hUnique : UniqueDiffOn ℝ (cylinder (Set.univ : Set (Space n)) 0 T) :=
    uniqueDiffOn_univ.prod (uniqueDiffOn_Icc hT)
  have hDeriv : ContDiffOn ℝ ∞ (fderivWithin ℝ g (cylinder Set.univ 0 T))
      (cylinder Set.univ 0 T) := hg.fderivWithin hUnique (by simp)
  have hEval := hDeriv.clm_apply (contDiffOn_const (c := (v,(0 : ℝ))))
  exact hEval.congr (fun p hp => spatialPartial_eq_fderivWithin hg v hp)

theorem spatialPartial_eq_zero_of_exterior {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T : ℝ} {K : Set (Space n)}
    (hK : IsCompact K) {g : Point n → V} {c : V}
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T, g (x,t) = c)
    (v : Space n) {p : Point n} (hp : p.2 ∈ Set.Icc 0 T) (hx : p.1 ∉ K) :
    spatialPartial g v p = 0 := by
  have hEq : (fun x : Space n => g (x,p.2)) =ᶠ[𝓝 p.1] (fun _ => c) := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with x hxx
    exact hExterior x hxx p.2 hp
  have h := congrArg (fun L : Space n →L[ℝ] V => L v) (hEq.fderiv_eq (𝕜 := ℝ))
  simpa only [spatialPartial,fderiv_fun_const,Pi.zero_apply,zero_apply] using h

def spatialWordDerivative {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List (Space n) → (Point n → V) → Point n → V
  | [],g => g
  | v :: vs,g => spatialPartial (spatialWordDerivative vs g) v

def spatialWordExteriorValue {n : ℕ} {V : Type*} [Zero V] (c : V) : List (Space n) → V
  | [] => c
  | _ :: _ => 0

theorem smooth_cylinder_spatialWordDerivative {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T : ℝ} (hT : 0 < T)
    {K : Set (Space n)} (hK : IsCompact K) {g : Point n → V} {c : V}
    (hg : ContDiffOn ℝ ∞ g (cylinder Set.univ 0 T))
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T, g (x,t) = c)
    (vs : List (Space n)) :
    ContDiffOn ℝ ∞ (spatialWordDerivative vs g) (cylinder Set.univ 0 T) ∧
      ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T,
        spatialWordDerivative vs g (x,t) = spatialWordExteriorValue c vs := by
  induction vs with
  | nil => exact ⟨hg,hExterior⟩
  | cons v vs ih =>
    refine ⟨smooth_cylinder_spatialPartial hT ih.1 v,?_⟩
    intro x hx t ht
    exact spatialPartial_eq_zero_of_exterior hK ih.2 v ht hx

theorem smooth_cylinder_spatialWordDerivative_holder {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T α : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1)
    {K : Set (Space n)} (hK : IsCompact K) {g : Point n → V} {c : V}
    (hg : ContDiffOn ℝ ∞ g (cylinder Set.univ 0 T))
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T, g (x,t) = c)
    (vs : List (Space n)) :
    ∃ F : ℝ, 0 < F ∧
      HolderBound α (cylinder Set.univ 0 T) (spatialWordDerivative vs g) F := by
  have h := smooth_cylinder_spatialWordDerivative hT hK hg hExterior vs
  exact smooth_cylinder_compact_perturbation_holder hT hα hα1 hK h.1 h.2

end Yau.LeafProofs.L16Aux
