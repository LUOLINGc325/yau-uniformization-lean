import Yau.Proofs.F05BootstrapUniformPatch
import Yau.Proofs.F05BootstrapBufferedCoefficients
import Yau.Proofs.F05BootstrapTranslatedEquation
import Yau.Proofs.F05BootstrapRelativeRestriction

/-! Original-equation patches with independent spatial and temporal buffers.
One coefficient cutoff is fixed before every nested radius and candidate. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_uniform_buffered_original_physical_patches (ν : Option (RIdx n))
    (χ : ContDiffBump (0 : Space n)) {Rbase : ℝ} (hχ : χ.rOut ≤ Rbase) {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) :
    ∃ δ A : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < A ∧
      ∀ (s0 T0 : ℝ) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
        (f u : Point n → ℝ) (F : ℝ),
      Elliptic (region ν Rbase ×ˢ Icc s0 T0) a lam upper →
      HolderBound α (region ν Rbase ×ˢ Icc s0 T0) a M →
      (∀ j, HolderBound α (region ν Rbase ×ˢ Icc s0 T0) (fun z => b z j) M) →
      HolderBound α (region ν Rbase ×ˢ Icc s0 T0) f F → F05RelC2 (region ν Rbase) (Icc s0 T0) u →
      (∀ j, ν = some j → ∀ x ∈ region ν Rbase, realCoord x j = 0 →
        ∀ t ∈ Icc s0 T0, u (x,t) = 0) →
      (∀ z ∈ region ν Rbase ×ˢ Icc s0 T0, F05RelOp (region ν Rbase) (Icc s0 T0) a b u z = f z) →
      ∀ (r R t0 τ : ℝ) (c : Space n) (L : ℝ),
      0 ≤ r → (hrR : r < R) → R ≤ χ.rIn → R-r ≤ 1 → s0 ≤ t0 →
      τ ∈ Icc (t0+localSchauderTime δ (R-r)) T0 → ‖c‖ ≤ r →
      HolderBound α (region ν (r+3*(R-r)/4) ×ˢ Icc t0 T0)
        (fun z => (u z,F05RelD (region ν Rbase) u z)) L →
      F05RelSchauder α (closure (F05FlatOpen ν)) (Icc 0 (localSchauderTime δ (R-r)))
        (classicalInteriorPatch δ (R-r) (τ-localSchauderTime δ (R-r)) (sub_pos.mpr hrR) c u)
        (A*((R-r)⁻¹)^8*(F+L)) := by
  have hRbase : 0 < Rbase := χ.rOut_pos.trans_le hχ
  let H : Set (Space n) := closure (F05FlatOpen ν)
  have hRegion (r : ℝ) : H ∩ Metric.closedBall (0 : Space n) r = region ν r := by
    ext x
    cases ν <;> simp [H,F05FlatOpen_closure,region,Metric.mem_closedBall,dist_zero_right,and_comm]
  have hKH : region ν Rbase ⊆ H := by rw [← hRegion]; exact inter_subset_left
  obtain ⟨J,hJ,hExt⟩ := F05_buffered_coefficient_extension_budget χ hχ hα hα1
  obtain ⟨δ,A,hδ,hδ1,hA,hPatch⟩ :=
    F05_uniform_relative_physical_patch (M := J*(M+1)) (lam := min lam 1)
      (upper := max upper 1) ν hα hα1 (by positivity) (F05_region_isCompact ν Rbase) hKH
  refine ⟨δ,A,hδ,hδ1,hA,?_⟩
  intro s0 T0 a b f u F hEll ha hb hf hu hFace hEq r R t0 τ c L hr hrR hR hh1 ht0 hτ hc hLow
  let h : ℝ := R-r
  let S : ℝ := r+3*h/4
  let T : ℝ := localSchauderTime δ h
  let σ : ℝ := τ-T
  let V : Set (Space n) := Metric.ball 0 S
  let ae := F05BufferedPrincipal χ a
  let be := F05BufferedDrift χ b
  let as := timeTranslate σ ae
  let bs := timeTranslate σ be
  let us := timeTranslate σ u
  let fs := timeTranslate σ f
  have hh : 0 < h := sub_pos.mpr hrR
  have hR0 : 0 < R := by linarith
  have hR2 : R ≤ Rbase := hR.trans (χ.rIn_lt_rOut.le.trans hχ)
  have hS : S < R := by dsimp only [S,h]; linarith
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hEnd : T+σ = τ := by dsimp only [σ]; ring
  have hTauStart : t0+T ≤ τ := hτ.1
  have hStart : t0 ≤ σ := by dsimp only [σ]; linarith
  have hStart0 : s0 ≤ σ := ht0.trans hStart
  have hEnd0 : T+σ ≤ T0 := hEnd ▸ hτ.2
  have hI : Icc (0+σ) (T+σ) ⊆ Icc s0 T0 := by
    intro t ht
    exact ⟨by linarith [ht.1],ht.2.trans hEnd0⟩
  have hX := F05_region_uniqueDiffOn ν hRbase
  have hY := F05_region_uniqueDiffOn ν hR0
  have hTime := uniqueDiffOn_Icc (show 0+σ < T+σ by linarith)
  have hSpace : region ν R ⊆ region ν Rbase := F05_region_mono hR2
  have huLocal : F05RelC2 (region ν R) (Icc (0+σ) (T+σ)) u :=
    F05_relative_c2_restrict hX hY hTime hSpace hI hu
  have hJets (z : Point n) (hz : z ∈ region ν R ×ˢ Icc (0+σ) (T+σ)) :=
    F05_relative_restriction_jets hX hY hTime hSpace hI hu hz
  have hSourceSub : region ν R ×ˢ Icc (0+σ) (T+σ) ⊆ region ν Rbase ×ˢ Icc s0 T0 := by
    intro z hz
    exact ⟨hSpace hz.1,hI hz.2⟩
  have hVX : H ∩ V ⊆ region ν R := by
    intro x hx
    rw [← hRegion]
    exact ⟨hx.1,by
      have hxN : ‖x‖ < S := by simpa only [V,Metric.mem_ball,dist_zero_right] using hx.2
      simpa only [Metric.mem_closedBall,dist_zero_right] using (hxN.trans hS).le⟩
  have hExtEll : Elliptic (H ×ˢ Icc s0 T0) ae (min lam 1) (max upper 1) ∧
      HolderBound α (H ×ˢ Icc s0 T0) ae (J*(M+1)) ∧
      ∀ j, HolderBound α (H ×ˢ Icc s0 T0) (fun z => be z j) (J*(M+1)) := by
    apply hExt H (Icc s0 T0) lam upper M a b hM
    · simpa only [hRegion] using hEll
    · simpa only [hRegion] using ha
    · intro j
      simpa only [hRegion] using hb j
  have hCoeffSub : H ×ˢ Icc (0+σ) (T+σ) ⊆ H ×ˢ Icc s0 T0 := prod_mono Subset.rfl hI
  have haShift : HolderBound α (H ×ˢ Icc 0 T) as (J*(M+1)) :=
    holderBound_timeTranslate_on_space (holderBound_mono hExtEll.2.1 hCoeffSub)
  have hbShift (j : RIdx n) : HolderBound α (H ×ˢ Icc 0 T) (fun z => bs z j) (J*(M+1)) :=
    holderBound_timeTranslate_on_space (holderBound_mono (hExtEll.2.2 j) hCoeffSub)
  have hEllShift : Elliptic (H ×ˢ Icc 0 T) as (min lam 1) (max upper 1) :=
    ⟨hExtEll.1.1,hExtEll.1.2.1,fun z hz =>
      hExtEll.1.2.2 (timeTranslatePoint σ z) (hCoeffSub ⟨hz.1,add_le_add hz.2.1 le_rfl,add_le_add hz.2.2 le_rfl⟩)⟩
  have hExterior : ∀ z ∈ H ×ˢ Icc 0 T, z.1 ∉ region ν Rbase → as z = 1 := by
    intro z hz hzK
    have hN : Rbase < ‖z.1‖ := by
      by_contra hn
      apply hzK
      rw [← hRegion]
      exact ⟨hz.1,by simpa only [Metric.mem_closedBall,dist_zero_right] using le_of_not_gt hn⟩
    exact (F05_buffered_coefficient_exterior χ (a := a) (b := b) (by dsimp only [timeTranslatePoint]; linarith :
      χ.rOut ≤ ‖(timeTranslatePoint σ z).1‖)).1
  have huShift : F05RelC2 (region ν R) (Icc 0 T) us := F05_relative_c2_timeTranslate hT huLocal
  have hEqLocal : ∀ z ∈ region ν R ×ˢ Icc (0+σ) (T+σ),
      F05RelOp (region ν R) (Icc (0+σ) (T+σ)) ae be u z = f z := by
    intro z hz
    have hA := F05_buffered_coefficient_exact χ (a := a) (b := b)
      (show ‖z.1‖ ≤ χ.rIn from hz.1.1.trans hR)
    have hAeq : ae z = a z := hA.1
    have hB : be z = b z := funext hA.2
    have hJet := hJets z hz
    simpa only [F05RelOp,hJet.1,hJet.2.1,hJet.2.2,hAeq,hB] using hEq z (hSourceSub hz)
  have hEqShift : ∀ z ∈ region ν R ×ˢ Icc 0 T,
      F05RelOp (region ν R) (Icc 0 T) as bs us z = fs z :=
    F05_translated_relative_equation hT huLocal ae be f hEqLocal
  have hFaceShift : ∀ j, ν = some j → ∀ x ∈ region ν R, realCoord x j = 0 →
      ∀ t ∈ Icc 0 T, us (x,t) = 0 := by
    intro j hj x hx hx0 t ht
    exact hFace j hj x (hSpace hx) hx0 (t+σ)
      (hI ⟨add_le_add ht.1 le_rfl,add_le_add ht.2 le_rfl⟩)
  have hfShift : HolderBound α ((H ∩ V) ×ˢ Icc 0 T) fs F := by
    apply holderBound_timeTranslate_on_space
    exact holderBound_mono hf (fun z hz => hSourceSub ⟨hVX hz.1,hz.2⟩)
  have hLowSource : HolderBound α ((H ∩ V) ×ˢ Icc (0+σ) (T+σ))
      (fun z => (u z,F05RelD (region ν R) u z)) L := by
    apply holderBound_congr_on (holderBound_mono hLow ?_)
    · intro z hz
      change (u z,F05RelD (region ν Rbase) u z) = (u z,F05RelD (region ν R) u z)
      rw [(hJets z ⟨hVX hz.1,hz.2⟩).1]
    · intro z hz
      refine ⟨?_,by linarith [hz.2.1],hz.2.2.trans hEnd0⟩
      rw [← hRegion]
      exact ⟨hz.1.1,Metric.ball_subset_closedBall hz.1.2⟩
  have hLowShift : HolderBound α ((H ∩ V) ×ˢ Icc 0 T)
      (fun z => (us z,F05RelD (region ν R) us z)) L :=
    holderBound_timeTranslate_on_space hLowSource
  have hSupport : tsupport (innerPatchBump (h/8) (by positivity) c : Space n → ℝ) ⊆ V := by
    intro y hy
    change y ∈ closure (Function.support (innerPatchBump (h/8) (by positivity) c : Space n → ℝ)) at hy
    rw [(innerPatchBump (h/8) (by positivity) c).support_eq] at hy
    have hyClosed := Metric.closure_ball_subset_closedBall hy
    have hyNorm : ‖y-c‖ ≤ 3*(h/8)/2 := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,innerPatchBump] using hyClosed
    rw [show V = Metric.ball 0 S from rfl,Metric.mem_ball,dist_zero_right]
    have hTri := norm_add_le (y-c) c
    rw [sub_add_cancel] at hTri
    dsimp only [S]
    linarith
  exact hPatch h hh hh1 c (region ν R) V as bs fs us F L hY Metric.isOpen_ball hVX hSupport
    haShift hbShift hEllShift hExterior huShift hFaceShift hEqShift hLowShift hfShift

end Yau.Proofs.F05Aux
