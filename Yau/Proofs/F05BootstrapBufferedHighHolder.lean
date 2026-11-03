import Yau.Proofs.F05BootstrapBufferedFamily
import Yau.Proofs.F05BootstrapBufferedPlateau
import Yau.LeafProofs.L16NearPairHolder

/-! A uniform near-pair estimate for the actual high jets on any buffered
physical cap. Far pairs use the constructed raw bound. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_buffered_physical_high_holder (ν : Option (RIdx n))
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
      HolderBound α (region ν r ×ˢ Icc s T0)
        (fun z => (F05RelDD (region ν Rbase) u z,F05RelT (Icc s0 T0) u z)) (C*(B+F)) := by
  have hRbase : 0 < Rbase := χ.rOut_pos.trans_le hχ
  obtain ⟨d,hd,sL,δ,C0,hd1,hdRadius,hs0L,hsLs,hδ,hδ1,hC0,hGap,hFamily⟩ :=
    F05_buffered_physical_schauder_family (M := M) (lam := lam) (upper := upper) ν χ hχ hα hα1 hM hr hrχ hs
  let T := localSchauderTime δ d
  let εx := d/16
  let εt := T/4
  let CH := 2*C0+2*C0*εx^(-α)+2*C0*εt^(-α/2)
  have hT : 0 < T := by dsimp only [T,localSchauderTime]; positivity
  have hεx : 0 < εx := by dsimp only [εx]; positivity
  have hεt : 0 < εt := by dsimp only [εt]; positivity
  have hCH : 0 < CH := by dsimp only [CH]; positivity
  refine ⟨CH,hCH,?_⟩
  intro T0 a b f u F B hsT hEll ha hb hf hu hB hFace hEq
  obtain ⟨hLow,hRaw,hPatches⟩ := hFamily T0 a b f u F B hsT hEll ha hb hf hu hB hFace hEq
  let D := B+F
  let Q := region ν r ×ˢ Icc s T0
  let H : Point n → (Space n →L[ℝ] Space n →L[ℝ] ℝ) × ℝ :=
    fun z => (F05RelDD (region ν Rbase) u z,F05RelT (Icc s0 T0) u z)
  have hB0 : 0 ≤ B := by
    have hZero : ((0,s) : Point n) ∈ region ν Rbase ×ˢ Icc s0 T0 := by
      refine ⟨?_,hs.le,hsT.le⟩
      cases ν <;> simpa [region,realCoord] using hRbase.le
    exact (abs_nonneg _).trans (hB (0,s) hZero)
  have hD : 0 ≤ D := add_nonneg hB0 hf.1
  have hSup : ∀ z ∈ Q, ‖H z‖ ≤ C0*D := by
    intro z hz
    exact hRaw z ⟨F05_region_mono (by linarith) hz.1,hsLs.le.trans hz.2.1,hz.2.2⟩
  have hNear : ∀ p ∈ Q, ∀ q ∈ Q, ‖p.1-q.1‖ ≤ εx → |p.2-q.2| ≤ εt →
      ‖H p-H q‖ ≤ (C0*D)*holderWeight α p q := by
    intro p hp q hq hSpace hTime
    let τ := max p.2 q.2
    let σ := τ-T
    let w := classicalInteriorPatch δ d σ hd p.1 u
    have hτ : τ ∈ Icc s T0 := ⟨hp.2.1.trans (le_max_left _ _),max_le hp.2.2 hq.2.2⟩
    have hPatch : F05RelSchauder α (closure (F05FlatOpen ν)) (Icc 0 T) w (C0*D) := hPatches τ p.1 hτ hp.1.1
    have hpτ : p.2 ≤ τ := le_max_left _ _
    have hqτ : q.2 ≤ τ := le_max_right _ _
    have hPMinusQ : p.2-q.2 ≤ T/4 := (le_abs_self _).trans hTime
    have hQMinusP : q.2-p.2 ≤ T/4 := (le_abs_self _).trans (by simpa only [abs_sub_comm] using hTime)
    have hτP : τ ≤ p.2+T/4 := max_le (by linarith) (by linarith)
    have hτQ : τ ≤ q.2+T/4 := max_le (by linarith) (by linarith)
    have hpNormalized : p.2-σ ∈ Icc 0 T := by constructor <;> dsimp only [σ] <;> linarith
    have hqNormalized : q.2-σ ∈ Icc 0 T := by constructor <;> dsimp only [σ] <;> linarith
    have hpPlateau : T/2 < p.2-σ := by dsimp only [σ]; linarith
    have hqPlateau : T/2 < q.2-σ := by dsimp only [σ]; linarith
    have hσ : s0 ≤ σ := by dsimp only [σ]; linarith [hτ.1]
    have hEnd : T+σ ≤ T0 := by dsimp only [σ]; linarith [hτ.2]
    have hpSpace : ‖p.1-p.1‖ < d/8 := by simp; positivity
    have hqSpace : ‖q.1-p.1‖ < d/8 := by
      have hBound : ‖q.1-p.1‖ ≤ d/16 := by simpa only [norm_sub_rev] using hSpace
      linarith
    have hRecover (z : Point n) (hz : z ∈ Q)
        (hzTime : z.2-σ ∈ Icc 0 T) (hzPlateau : T/2 < z.2-σ) (hzSpace : ‖z.1-p.1‖ < d/8) :
        (F05RelDD (closure (F05FlatOpen ν)) w (z.1,z.2-σ),F05RelT (Icc 0 T) w (z.1,z.2-σ)) = H z := by
      have hRecover := F05_buffered_interiorPatch_high_on_plateau ν hRbase hδ hd p.1 u hu hσ hEnd
        hzTime hzPlateau hzSpace (F05_region_mem_flat hz.1)
        (hz.1.1.trans_lt (hrχ.trans (χ.rIn_lt_rOut.trans_le hχ)))
      simpa only [sub_add_cancel,Prod.eta] using hRecover
    have hHighPatch : HolderBound α (closure (F05FlatOpen ν) ×ˢ Icc 0 T)
        (fun z => (F05RelDD (closure (F05FlatOpen ν)) w z,F05RelT (Icc 0 T) w z)) (C0*D) := by
      refine ⟨mul_nonneg hC0.le hD,?_,?_⟩
      · intro z hz
        exact max_le (hPatch.2.2.1.2.1 z hz) (hPatch.2.2.2.2.1 z hz)
      · intro z hz v hv
        exact max_le (hPatch.2.2.1.2.2 z hz v hv) (hPatch.2.2.2.2.2 z hz v hv)
    have hBound := hHighPatch.2.2 (p.1,p.2-σ) ⟨F05_region_mem_flat hp.1,hpNormalized⟩
      (q.1,q.2-σ) ⟨F05_region_mem_flat hq.1,hqNormalized⟩
    change ‖(F05RelDD (closure (F05FlatOpen ν)) w (p.1,p.2-σ),F05RelT (Icc 0 T) w (p.1,p.2-σ))-
      (F05RelDD (closure (F05FlatOpen ν)) w (q.1,q.2-σ),F05RelT (Icc 0 T) w (q.1,q.2-σ))‖ ≤ _ at hBound
    rw [hRecover p hp hpNormalized hpPlateau hpSpace,hRecover q hq hqNormalized hqPlateau hqSpace] at hBound
    have hDiff : (p.2-σ)-(q.2-σ) = p.2-q.2 := by ring
    simpa only [holderWeight,hDiff] using hBound
  have hPair := holderBound_of_near_pairs (f := H) (Q := Q) hα.le
    (mul_nonneg hC0.le hD) (mul_nonneg hC0.le hD) hεx hεt hSup hNear
  have hBudget : C0*D+C0*D+2*(C0*D)*εx^(-α)+2*(C0*D)*εt^(-α/2) = CH*D := by dsimp only [CH]; ring
  rwa [hBudget] at hPair

end Yau.Proofs.F05Aux
