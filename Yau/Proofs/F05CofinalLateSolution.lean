import Yau.Proofs.F05ReflectedEncodedEquation
import Yau.Proofs.F05ActualSchauderCompactness
import Yau.Proofs.F05CofinalNonlinearLimit
import Yau.Proofs.F05TranslatedClosedSlab

/-! Actual cofinal compact solutions and their common proved positive-time
estimate produce an actual solution on the late closed slab. All four
limiting jets, the manifold realization and the terminal PDE are built
inside this theorem. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_cofinal_late_solution {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ) {T s b r γ C : ℝ}
    (hT : 0 < T) (hs : 0 < s) (hb : 0 < b) (hb1 : b ≤ 1)
    (hsr : s < r) (hbr : b/2 ≤ r-s) (hγ : 0 < γ) (hγ1 : γ < 1) (hC : 0 ≤ C)
    (hh : MetricFamilySmooth h (Icc 0 T)) (hp : SmoothSpaceTime p (Icc 0 T))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 T))
    (τ : ℕ → ℝ) (w : ℕ → M.Carrier → ℝ → ℝ) (hτConv : Tendsto τ atTop (𝓝 T))
    (hτr : ∀ k, r < τ k) (hτT : ∀ k, τ k < T)
    (hBack : ∀ k, 0 ≤ 3*(τ k-s)-2*(T-s))
    (hw : ∀ k, F05CompactDirichletSolution O A h p (τ k) (w k))
    (hRelative : ∀ k i, F05RelSchauder γ (F05D A i) (Icc s (τ k)) (pull A i (w k)) C) :
    ∃ (φ : ℕ → ℕ) (W : M.Carrier → ℝ → ℝ) (K : ℝ), StrictMono φ ∧ 0 < K ∧
      (∀ i, SchauderBound (γ/2) (cylinder (F05D A i) r T) (pull A i W) K) ∧
      ContinuousOn (fun z : M.Carrier × ℝ => W z.1 z.2) (closure O ×ˢ Icc r T) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc r T, W x t = p x t) ∧
      (∀ x ∈ closure O, ∀ t ∈ Icc r T,
        derivWithin (W x) (Icc r T) t = Real.exp (-W x t)*laplacian (h t) (fun y => W y t) x+
          (1-Real.exp (-W x t))*scalarCurvature (h t) x) ∧
      ∀ x ∈ closure O, ∀ t ∈ Ico r T, Tendsto (fun k => w (φ k) x t) atTop (𝓝 (W x t)) := by
  have hrT : r < T := (hτr 0).trans (hτT 0)
  have hsT : s < T := hsr.trans hrT
  have hδ : 0 < T-s := sub_pos.mpr hsT
  have hτs (k : ℕ) : s < τ k := hsr.trans (hτr k)
  obtain ⟨B,hB,hFixed⟩ := F05_reflected_zero_family hA h p hT hs hb hb1 hγ hγ1 hC hp
    τ w hτs hτT hBack hw hRelative
  let F : ℕ → M.Carrier → ℝ → ℝ := fun k => F05ReflectedZeroField s b (τ k) p (w k)
  have hFC2 (k : ℕ) (i : Fin A.count) : C2 (F05Q A i (T-s)) (pull A i (F k)) := (hFixed k).1 i
  obtain ⟨φ,u,uLim,hφ,hLim,hEval⟩ := F05_actual_schauder_compact_subsequence hA hγ hδ.le F hFC2
    (fun k i => (hFixed k).2.1 i) (fun k x hx => (hFixed k).2.2.1 x hx)
    (fun k i z hz => (hFixed k).2.2.2.1 i z hz)
    (fun k x hx t ht => (hFixed k).2.2.2.2 x hx t ht)
  have hτφConv := hτConv.comp hφ.tendsto_atTop
  have hMapT : MapsTo (fun t : ℝ => t+s) (Icc 0 (T-s)) (Icc 0 T) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  let hShift := fun t => h (t+s)
  let pShift := F05ManifoldTimeShift s p
  have hhShift := F05_smooth_metric_time_shift s hMapT h hh
  have hpShift := F05_smooth_spacetime_time_shift s hMapT p hp
  have hRRaw := F05_smooth_spacetime_time_shift s hMapT (fun x t => scalarCurvature (h t) x) hR
  have hRShift : SmoothSpaceTime (fun x t => scalarCurvature (hShift t) x) (Icc 0 (T-s)) := hRRaw
  have hHalf : 0 < γ/2 := by positivity
  have hHalf1 : γ/2 < 1 := by linarith
  have ha : 0 ≤ r-s := sub_nonneg.mpr hsr.le
  have haδ : r-s < T-s := sub_lt_sub_right hrT s
  obtain ⟨V,L,hL,hVSch,hVCont,hV0,hVBoundary,hVEquation,hVConv⟩ :=
    F05_cofinal_nonlinear_limit hA hχ hShift pShift hδ hHalf hHalf1 ha haδ
      hhShift hpShift hRShift (fun k => u (φ k)) uLim hLim (by
        intro i z hz
        have hNear : Ioi (z.val.2+s) ∈ 𝓝 T := Ioi_mem_nhds (by linarith [hz.2])
        filter_upwards [hτφConv.eventually hNear] with k hk
        change z.val.2+s < τ (φ k) at hk
        exact F05_reflected_zero_encoded_equation hA h p (w (φ k)) hδ hs.le hb hsr
          (hτr (φ k)) (hτT (φ k)) hbr hp (hw (φ k)) (hFC2 (φ k)) (u (φ k)) (hEval (φ k))
          i z ⟨hz.1,by linarith⟩)
  have hVLate (i : Fin A.count) :
      SchauderBound (γ/2) (cylinder (F05D A i) (r-s) (T-s)) (pull A i V) L :=
    F05_schauder_restrict_interval haδ ha le_rfl (hVSch i)
  have hVContLate := hVCont.mono (prod_mono subset_rfl (Icc_subset_Icc ha le_rfl))
  have hMapBack : MapsTo (fun t : ℝ => t-s) (Icc r T) (Icc (r-s) (T-s)) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  let W := F05ShiftedRestart s V
  have hWSch := F05_translated_closed_slab_schauder (s := s) A hrT hMapBack V hVLate
  have hWCont := F05_translated_closed_slab_continuous (s := s) hMapBack V hVContLate
  have hWEquation := F05_translated_closed_slab_equation (s := s) hA h hrT hMapBack V
    (fun i => (hVLate i).1) hVEquation
  refine ⟨φ,W,4*L,hφ,by positivity,hWSch,hWCont,?_,hWEquation,?_⟩
  · intro x hx t ht
    have htShift : t-s ∈ Icc 0 (T-s) := ⟨ha.trans (hMapBack ht).1,(hMapBack ht).2⟩
    have hBoundary := hVBoundary x hx (t-s) htShift
    simpa only [W,F05ShiftedRestart,pShift,F05ManifoldTimeShift,sub_add_cancel] using hBoundary
  · intro x hx t ht
    obtain ⟨i,y,hy,hyx⟩ := F05_cover hA hx
    have hq : (y,t-s) ∈ F05Q A i (T-s) :=
      ⟨hy,by linarith [ht.1],by linarith [ht.2]⟩
    let q : F05Q A i (T-s) := ⟨(y,t-s),hq⟩
    let f : ℕ → ℝ := fun k => pull A i pShift q.val+((u (φ k)).val i).val.1 q
    have hNative := hVConv i q
    change Tendsto f atTop (𝓝 (V (lift A i y) (t-s))) at hNative
    rw [hyx] at hNative
    have hNear : Ioi t ∈ 𝓝 T := Ioi_mem_nhds ht.2
    have hEqSeq : f =ᶠ[atTop] fun k => w (φ k) x t := by
      filter_upwards [hτφConv.eventually hNear] with k hk
      have hValue := (hEval (φ k) i q).1
      have hReconstruct := F05_reflected_zero_reconstruct (s := s) (τ := τ (φ k)) (t := t) hb
        hk.le (hbr.trans (sub_le_sub_right ht.1 s)) p (w (φ k)) x
      calc
        f k = p x t+F (φ k) x (t-s) := by
          dsimp only [f]
          rw [hValue]
          simp only [q,pShift,pull,F05ManifoldTimeShift,hyx,sub_add_cancel]
        _ = w (φ k) x t := hReconstruct
    change Tendsto (fun k => w (φ k) x t) atTop (𝓝 (V x (t-s)))
    exact hNative.congr' hEqSeq

end Yau.Proofs.F05Aux
