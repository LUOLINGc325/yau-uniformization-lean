import Yau.Proofs.F05HolderLogControl
import Yau.Proofs.F05HolderFaceBarrier

/-! The two actual cap comparisons give the simultaneous time/physical-face
error modulus. Exponentiation uses only the fixed value interval. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_buffered_error_of_log_control (k : Option (RIdx n))
    {ν upper A₀ b₀ H W₀ E : ℝ} (hν : 0 < ν) (hA₀ : 0 ≤ A₀) (hb₀ : 0 ≤ b₀)
    (hH : 0 < H) (hW₀ : 0 < W₀) (hE : 0 < E) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : ℝ), 0 < T →
      ∀ (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (u q G : Point n → ℝ),
      F05BufferedLogControl k T ν upper A₀ b₀ H W₀ a b u →
      (∀ z ∈ cylinder (region k 2) 0 T, |q z-G z| ≤ E*|u z|) →
      ∀ z ∈ cylinder (region k (7/4)) 0 T,
        |q z-G z| ≤ K*min z.2 (F05FaceGauge k z.1) := by
  obtain ⟨Ht,hHt,hInitial⟩ := F05_buffered_initial_error k hA₀ hb₀ hH hW₀
  have hFaceExists : ∃ Kb : ℝ, 0 < Kb ∧ ∀ (T : ℝ), 0 < T →
      ∀ (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (u : Point n → ℝ),
      F05BufferedLogControl k T ν upper A₀ b₀ H W₀ a b u →
      ∀ x ∈ region k (7/4), ∀ t ∈ Icc 0 T,
        |u (x,t)| ≤ Kb*F05FaceGauge k x := by
    cases k with
    | none =>
      refine ⟨W₀+1,by positivity,?_⟩
      intro T hT a b u hControl x hx t htm
      obtain ⟨hc,hs,ht,he,ha,hb,hi,hl,hsup,hop⟩ := hControl
      have hh := hsup (x,t) ⟨F05_region_mono (by norm_num) hx,htm⟩
      simp only [F05FaceGauge,mul_one]
      linarith
    | some j =>
      obtain ⟨Kb,hKb,hFace⟩ := F05_buffered_face_error j hν hA₀ hb₀ hH hW₀
      refine ⟨Kb,hKb,?_⟩
      intro T hT a b u hControl
      obtain ⟨hc,hs,ht,he,ha,hb,hi,hl,hsup,hop⟩ := hControl
      exact hFace T hT a b u hc hs ht he ha hb hi hl hsup hop
  obtain ⟨Kb,hKb,hFace⟩ := hFaceExists
  let K := 1+E*(Ht+Kb)
  have hK : 0 < K := by dsimp [K]; positivity
  have hHtK : E*Ht ≤ K := by dsimp [K]; nlinarith [mul_pos hE hKb]
  have hKbK : E*Kb ≤ K := by dsimp [K]; nlinarith [mul_pos hE hHt]
  refine ⟨K,hK,?_⟩
  intro T hT a b u q G hControl hTransfer z hz
  have hFaceAt := hFace T hT a b u hControl z.1 hz.1 z.2 hz.2
  obtain ⟨hc,hs,ht,he,ha,hb,hi,hl,hsup,hop⟩ := hControl
  have hInitialAt := hInitial T hT a b u hc hs ht he ha hb hi hl hsup hop z.1 hz.1 z.2 hz.2
  have hz2 : z ∈ cylinder (region k 2) 0 T := ⟨F05_region_mono (by norm_num) hz.1,hz.2⟩
  have hGauge : 0 ≤ F05FaceGauge k z.1 := by
    apply F05FaceGauge_nonneg
    rw [F05FlatOpen_closure]
    cases k <;> exact hz.1.2
  by_cases hMin : z.2 ≤ F05FaceGauge k z.1
  · rw [min_eq_left hMin]
    calc
      _ ≤ E*|u z| := hTransfer z hz2
      _ ≤ E*(Ht*z.2) := mul_le_mul_of_nonneg_left hInitialAt hE.le
      _ = (E*Ht)*z.2 := by ring
      _ ≤ K*z.2 := mul_le_mul_of_nonneg_right hHtK hz.2.1
  · rw [min_eq_right (le_of_not_ge hMin)]
    calc
      _ ≤ E*|u z| := hTransfer z hz2
      _ ≤ E*(Kb*F05FaceGauge k z.1) := mul_le_mul_of_nonneg_left hFaceAt hE.le
      _ = (E*Kb)*F05FaceGauge k z.1 := by ring
      _ ≤ K*F05FaceGauge k z.1 := mul_le_mul_of_nonneg_right hKbK hGauge

end Yau.Proofs.F05Aux
