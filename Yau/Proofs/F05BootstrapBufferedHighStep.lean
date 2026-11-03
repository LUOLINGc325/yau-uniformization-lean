import Yau.Proofs.F05BootstrapBufferedPatches
import Yau.Proofs.F05BootstrapRelativePlateau
import Yau.Proofs.F05BootstrapFlatGeometry
import Yau.Proofs.F05BootstrapLocalJets
import Yau.Proofs.F05BootstrapLowInterpolation

/-! The one-step high estimate with independent spatial and temporal
buffers. Its constants precede all receiving caps and all candidates. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05RelHigh (X : Set (Space n)) (I : Set ℝ) (u : Point n → ℝ) (z : Point n) : ℝ :=
  max ‖F05RelDD X u z‖ |F05RelT I u z|

theorem F05_uniform_buffered_physical_high_step (ν : Option (RIdx n))
    (χ : ContDiffBump (0 : Space n)) {Rbase : ℝ} (hχ : χ.rOut ≤ Rbase) {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) :
    ∃ δ A : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < A ∧
      ∀ (s0 T0 : ℝ) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
        (f u : Point n → ℝ) (F B : ℝ),
      Elliptic (region ν Rbase ×ˢ Icc s0 T0) a lam upper →
      HolderBound α (region ν Rbase ×ˢ Icc s0 T0) a M →
      (∀ j, HolderBound α (region ν Rbase ×ˢ Icc s0 T0) (fun z => b z j) M) →
      HolderBound α (region ν Rbase ×ˢ Icc s0 T0) f F → F05RelC2 (region ν Rbase) (Icc s0 T0) u →
      (∀ z ∈ region ν Rbase ×ˢ Icc s0 T0, |u z| ≤ B) →
      (∀ j, ν = some j → ∀ x ∈ region ν Rbase, realCoord x j = 0 →
        ∀ t ∈ Icc s0 T0, u (x,t) = 0) →
      (∀ z ∈ region ν Rbase ×ˢ Icc s0 T0, F05RelOp (region ν Rbase) (Icc s0 T0) a b u z = f z) →
      ∀ r R t0 t1 ρ K : ℝ, 0 ≤ r → r < R → R ≤ χ.rIn → R-r ≤ 1 →
      s0 ≤ t0 → t0 < T0 → localSchauderTime δ (R-r) ≤ t1-t0 →
      0 < ρ → ρ ≤ 1 → ρ ≤ (R-r)/4 → 0 ≤ K →
      (∀ z ∈ region ν R ×ˢ Icc t0 T0, F05RelHigh (region ν Rbase) (Icc s0 T0) u z ≤ K) →
      ∀ z ∈ region ν r ×ˢ Icc t1 T0,
        F05RelHigh (region ν Rbase) (Icc s0 T0) u z ≤
          A*((R-r)⁻¹)^8*(F+8*(ρ^(1-α)*K+ρ^(-1-α)*B)) := by
  have hRbase : 0 < Rbase := χ.rOut_pos.trans_le hχ
  obtain ⟨δ,A,hδ,hδ1,hA,hPatches⟩ :=
    F05_uniform_buffered_original_physical_patches (M := M) (lam := lam) (upper := upper)
      ν χ hχ hα hα1 hM
  refine ⟨δ,A,hδ,hδ1,hA,?_⟩
  intro s0 T0 a b f u F B hEll ha hb hf hu hB hFace hEq r R t0 t1 ρ K
    hr hrR hR hh1 ht0 ht0T0 hGap hρ hρ1 hρMargin hK hHigh
  let h : ℝ := R-r
  let S : ℝ := r+3*h/4
  have hh : 0 < h := sub_pos.mpr hrR
  have hR0 : 0 < R := by linarith
  have hR2 : R ≤ Rbase := hR.trans (χ.rIn_lt_rOut.le.trans hχ)
  have hX := F05_region_uniqueDiffOn ν hRbase
  have hY := F05_region_uniqueDiffOn ν hR0
  have hTime := uniqueDiffOn_Icc ht0T0
  have hSpace : region ν R ⊆ region ν Rbase := F05_region_mono hR2
  have hI : Icc t0 T0 ⊆ Icc s0 T0 := fun t ht => ⟨ht0.trans ht.1,ht.2⟩
  have hSub : region ν R ×ˢ Icc t0 T0 ⊆ region ν Rbase ×ˢ Icc s0 T0 := prod_mono hSpace hI
  have huClosed := F05_relative_c2_restrict hX hY hTime hSpace hI hu
  have hJets (z : Point n) (hz : z ∈ region ν R ×ˢ Icc t0 T0) :=
    F05_relative_restriction_jets hX hY hTime hSpace hI hu hz
  have hB0 : 0 ≤ B := by
    have hZero : ((0,t0) : Point n) ∈ region ν Rbase ×ˢ Icc s0 T0 := by
      refine ⟨?_,ht0,ht0T0.le⟩
      cases ν <;> simpa [region,realCoord] using hRbase.le
    exact (abs_nonneg _).trans (hB (0,t0) hZero)
  have hRaw : ∀ z ∈ region ν R ×ˢ Icc t0 T0,
      ‖F05RelDD (region ν R) u z‖ ≤ K ∧ |F05RelT (Icc t0 T0) u z| ≤ K := by
    intro z hz
    rw [(hJets z hz).2.1,(hJets z hz).2.2]
    exact ⟨(le_max_left _ _).trans (hHigh z hz),(le_max_right _ _).trans (hHigh z hz)⟩
  let L : ℝ := 8*(ρ^(1-α)*K+ρ^(-1-α)*B)
  have hLowRaw := F05_relative_cap_low_interpolation ν hα hα1 hR0 hρ hρ1
    (show S+ρ ≤ R by dsimp only [S,h]; linarith) hB0 hK huClosed
    (fun z hz => hB z (hSub hz)) hRaw
  have hLow : HolderBound α (region ν S ×ˢ Icc t0 T0)
      (fun z => (u z,F05RelD (region ν Rbase) u z)) L := by
    apply holderBound_congr_on hLowRaw
    intro z hz
    change (u z,F05RelD (region ν R) u z) = (u z,F05RelD (region ν Rbase) u z)
    rw [(hJets z ⟨F05_region_mono (by dsimp only [S,h]; linarith) hz.1,hz.2⟩).1]
  intro p hp
  let T : ℝ := localSchauderTime δ h
  let σ : ℝ := p.2-T
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hEnd : T+σ = p.2 := by dsimp only [σ]; ring
  have hStart : t0 ≤ σ := by dsimp only [σ]; linarith [hp.2.1]
  have hStart0 : s0 ≤ 0+σ := by linarith
  have hEnd0 : T+σ ≤ T0 := hEnd ▸ hp.2.2
  have hc2 : ‖p.1‖ < Rbase := hp.1.1.trans_lt (hrR.trans_le (hR.trans (χ.rIn_lt_rOut.le.trans hχ)))
  have hpBase : p ∈ region ν Rbase ×ˢ Icc s0 T0 :=
    ⟨F05_region_mono (hrR.le.trans hR2) hp.1,by linarith [hp.2.1],hp.2.2⟩
  have hPatch := hPatches s0 T0 a b f u F hEll ha hb hf hu hFace hEq r R t0 p.2 p.1 L
    hr hrR hR hh1 ht0 ⟨by linarith [hp.2.1],hp.2.2⟩ hp.1.1 hLow
  have hpTop : ((p.1,T) : Point n) ∈ closure (F05FlatOpen ν) ×ˢ Icc 0 T :=
    ⟨F05_region_mem_flat hp.1,hT.le,le_rfl⟩
  have hHess := hPatch.2.2.1.2.1 (p.1,T) hpTop
  have hTimeBound := hPatch.2.2.2.2.1 (p.1,T) hpTop
  have hPlateau := F05_relative_interiorPatch_jets_at_top
    (X := closure (F05FlatOpen ν)) (I := Icc 0 T) (σ := σ) hδ hh p.1 u
  rw [hPlateau.2.1,hEnd] at hHess
  rw [hPlateau.2.2] at hTimeBound
  have hDomain := F05_relative_local_domain_jets (F05_flat_closure_uniqueDiffOn ν) hX
    Metric.isOpen_ball (V := Metric.ball 0 Rbase)
    (fun x hx => by rw [F05_region_eq_flat_inter_ball]; exact ⟨hx.1,Metric.ball_subset_closedBall hx.2⟩)
    hu (z := p) ⟨⟨F05_region_mem_flat hp.1,by simpa only [Metric.mem_ball,dist_zero_right] using hc2⟩,hpBase.2⟩
  rw [hDomain.2] at hHess
  have hLocalI : Icc (0+σ) (T+σ) ⊆ Icc s0 T0 := fun t ht => ⟨hStart0.trans ht.1,ht.2.trans hEnd0⟩
  have hLocalTime := uniqueDiffOn_Icc (show 0+σ < T+σ by linarith)
  have huTime := F05_relative_c2_restrict hX hX hLocalTime Subset.rfl hLocalI hu
  have hShift := F05_relative_timeTranslate_time_jet hT huTime
    (z := (p.1,T)) ⟨hpBase.1,hT.le,le_rfl⟩
  have hRestrict := F05_relative_restriction_jets hX hX hLocalTime Subset.rfl hLocalI hu
    (z := (p.1,T+σ)) ⟨hpBase.1,by linarith,le_rfl⟩
  rw [hShift] at hTimeBound
  change ‖F05RelT (Icc (0+σ) (T+σ)) u (p.1,T+σ)‖ ≤ _ at hTimeBound
  rw [hRestrict.2.2,hEnd] at hTimeBound
  exact max_le (by simpa only [Prod.eta] using hHess)
    (by simpa only [Real.norm_eq_abs,Prod.eta] using hTimeBound)

end Yau.Proofs.F05Aux
