import Yau.Proofs.F05BootstrapBufferedHighHolder

/-! The full relative local Schauder estimate on arbitrary receiving caps
and later time slabs. All jets are actual within derivatives, including the
true physical plane, terminal face and their intersection. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_buffered_physical_local_schauder (ν : Option (RIdx n))
    (χ : ContDiffBump (0 : Space n)) {Rbase : ℝ} (hχ : χ.rOut ≤ Rbase)
    {α M lam upper r s0 s : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hr : 0 < r) (hrχ : r < χ.rIn) (hs : s0 < s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T0 : ℝ) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
        (f u : Point n → ℝ) (F B : ℝ), s < T0 →
      Elliptic (region ν Rbase ×ˢ Icc s0 T0) a lam upper →
      HolderBound α (region ν Rbase ×ˢ Icc s0 T0) a M →
      (∀ j, HolderBound α (region ν Rbase ×ˢ Icc s0 T0) (fun z => b z j) M) →
      HolderBound α (region ν Rbase ×ˢ Icc s0 T0) f F → F05RelC2 (region ν Rbase) (Icc s0 T0) u →
      (∀ z ∈ region ν Rbase ×ˢ Icc s0 T0, |u z| ≤ B) →
      (∀ j, ν = some j → ∀ x ∈ region ν Rbase, realCoord x j = 0 →
        ∀ t ∈ Icc s0 T0, u (x,t) = 0) →
      (∀ z ∈ region ν Rbase ×ˢ Icc s0 T0, F05RelOp (region ν Rbase) (Icc s0 T0) a b u z = f z) →
      F05RelSchauder α (region ν r) (Icc s T0) u (C*(B+F)) := by
  have hRbase : 0 < Rbase := χ.rOut_pos.trans_le hχ
  obtain ⟨d,hd,sL,δ,CL,hd1,hdRadius,hs0L,hsLs,hδ,hδ1,hCL,hGap,hFamily⟩ :=
    F05_buffered_physical_schauder_family (M := M) (lam := lam) (upper := upper) ν χ hχ hα hα1 hM hr hrχ hs
  obtain ⟨CH,hCH,hHolder⟩ := F05_buffered_physical_high_holder
    (M := M) (lam := lam) (upper := upper) ν χ hχ hα hα1 hM hr hrχ hs
  let C := 1+CL+CH
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCLC : CL ≤ C := by dsimp only [C]; linarith
  have hCHC : CH ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro T0 a b f u F B hsT hEll ha hb hf hu hB hFace hEq
  have hB0 : 0 ≤ B := by
    have hZero : ((0,s) : Point n) ∈ region ν Rbase ×ˢ Icc s0 T0 := by
      refine ⟨?_,hs.le,hsT.le⟩
      cases ν <;> simpa [region,realCoord] using hRbase.le
    exact (abs_nonneg _).trans (hB (0,s) hZero)
  have hD : 0 ≤ B+F := add_nonneg hB0 hf.1
  obtain ⟨hLow,hRaw,hPatches⟩ := hFamily T0 a b f u F B hsT hEll ha hb hf hu hB hFace hEq
  have hHigh := hHolder T0 a b f u F B hsT hEll ha hb hf hu hB hFace hEq
  have hX := F05_region_uniqueDiffOn ν hRbase
  have hY := F05_region_uniqueDiffOn ν hr
  have hTime := uniqueDiffOn_Icc hsT
  have hSpace : region ν r ⊆ region ν Rbase := F05_region_mono (hrχ.le.trans (χ.rIn_lt_rOut.le.trans hχ))
  have hI : Icc s T0 ⊆ Icc s0 T0 := fun t ht => ⟨hs.le.trans ht.1,ht.2⟩
  have hJets (z : Point n) (hz : z ∈ region ν r ×ˢ Icc s T0) :=
    F05_relative_restriction_jets hX hY hTime hSpace hI hu hz
  have hLowSub : region ν r ×ˢ Icc s T0 ⊆ region ν (r+3*d/4) ×ˢ Icc sL T0 :=
    fun z hz => ⟨F05_region_mono (by linarith) hz.1,hsLs.le.trans hz.2.1,hz.2.2⟩
  have hLowActual : HolderBound α (region ν r ×ˢ Icc s T0)
      (fun z => (u z,F05RelD (region ν r) u z)) (CL*(B+F)) := by
    apply holderBound_congr_on (holderBound_mono hLow hLowSub)
    intro z hz
    change (u z,F05RelD (region ν Rbase) u z) = (u z,F05RelD (region ν r) u z)
    rw [(hJets z hz).1]
  have hHessActual : HolderBound α (region ν r ×ˢ Icc s T0) (F05RelDD (region ν r) u) (CH*(B+F)) :=
    holderBound_congr_on (holderBound_fst hHigh) (fun z hz => (hJets z hz).2.1.symm)
  have hTimeActual : HolderBound α (region ν r ×ˢ Icc s T0) (F05RelT (Icc s T0) u) (CH*(B+F)) :=
    holderBound_congr_on (holderBound_snd hHigh) (fun z hz => (hJets z hz).2.2.symm)
  exact ⟨F05_relative_c2_restrict hX hY hTime hSpace hI hu,
    holderBound_mono_const hLowActual (mul_le_mul_of_nonneg_right hCLC hD),
    holderBound_mono_const hHessActual (mul_le_mul_of_nonneg_right hCHC hD),
    holderBound_mono_const hTimeActual (mul_le_mul_of_nonneg_right hCHC hD)⟩

end Yau.Proofs.F05Aux
