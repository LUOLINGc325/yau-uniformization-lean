import Yau.LeafProofs.L21FiniteWeakJets

/-! Cutting off a finite local jet gives an actual global compact L² weak
jet, with one common compact support and the literal cutoff input. -/

open MeasureTheory Filter
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem complexWeakDerivativeOn_global_of_support {O K : Set (X n)}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {u g : X n → ℂ} {v : X n} (h : ComplexWeakDerivativeOn O u g v)
    (hsu : tsupport u ⊆ K) (hsg : tsupport g ⊆ K) : ComplexWeakDerivative u g v := by
  obtain ⟨θ, hθ, hcθ, hsθ, _hθrange, hθK⟩ :=
    Yau.LeafProofs.L14Aux.exists_model_open_cutoff hO hK hKO
  intro ψ hψ hcψ
  have hh := h (fun x => θ x * ψ x) (hθ.mul hψ) hcθ.mul_right (tsupport_mul_subset_left.trans hsθ)
  have hL : (fun x => u x * (fderiv ℝ (fun y => θ y * ψ y) x v : ℂ)) =
      fun x => u x * (fderiv ℝ ψ x v : ℂ) := by
    funext x
    by_cases hx : x ∈ K
    · rw [fderiv_fun_mul (c := θ) (d := ψ)
        (hθ.differentiable (by simp) x) (hψ.differentiable (by simp) x)]
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
        (hθK x hx).1, (hθK x hx).2, _root_.zero_apply, mul_zero, add_zero, one_mul]
    · have hn : x ∉ tsupport u := fun hh => hx (hsu hh)
      simp only [image_eq_zero_of_notMem_tsupport hn, zero_mul]
  have hR : (fun x => g x * ((θ x * ψ x : ℝ) : ℂ)) = fun x => g x * (ψ x : ℂ) := by
    funext x
    by_cases hx : x ∈ K
    · rw [(hθK x hx).1, one_mul]
    · have hn : x ∉ tsupport g := fun hh => hx (hsg hh)
      simp only [image_eq_zero_of_notMem_tsupport hn, zero_mul]
  rw [hL, hR] at hh
  exact hh

def cutoffWordTerms (χ : X n → ℂ) : List (Yau.RIdx n) → List (WordTerm n)
  | [] => [(χ, [])]
  | a :: w => differentiateWordTerms a (cutoffWordTerms χ w)

def cutoffWordJet (χ : X n → ℂ) (U : List (Yau.RIdx n) → X n → ℂ)
    (w : List (Yau.RIdx n)) : X n → ℂ := evalWordTerms U (cutoffWordTerms χ w)

theorem cutoffWordTerms_order (χ : X n → ℂ) (w : List (Yau.RIdx n)) :
    ∀ t ∈ cutoffWordTerms χ w, t.2.length ≤ w.length := by
  induction w with
  | nil => simp [cutoffWordTerms]
  | cons a w ih => exact differentiateWordTerms_order a _ w.length ih

theorem cutoffWordTerms_smooth {χ : X n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (w : List (Yau.RIdx n)) : ∀ t ∈ cutoffWordTerms χ w, ContDiff ℝ ∞ t.1 := by
  induction w with
  | nil => simpa [cutoffWordTerms] using hχ
  | cons a w ih =>
    intro t ht
    obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact contDiff_directional (ih s hs) _
    · exact ih s hs

theorem cutoffWordTerms_tsupport (χ : X n → ℂ) (w : List (Yau.RIdx n)) :
    ∀ t ∈ cutoffWordTerms χ w, tsupport t.1 ⊆ tsupport χ := by
  induction w with
  | nil => simp [cutoffWordTerms]
  | cons a w ih =>
    intro t ht
    obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact (tsupport_fderiv_apply_subset ℝ _).trans (ih s hs)
    · exact ih s hs

theorem evalWordTerms_tsupport {K : Set (X n)} (U : List (Yau.RIdx n) → X n → ℂ)
    (L : List (WordTerm n)) (hL : ∀ t ∈ L, tsupport t.1 ⊆ K) :
    tsupport (evalWordTerms U L) ⊆ K := by
  induction L with
  | nil =>
    change tsupport (0 : X n → ℂ) ⊆ K
    simp
  | cons t L ih =>
    have htail := ih (fun s hs => hL s (List.mem_cons_of_mem t hs))
    exact (tsupport_add (fun x => t.1 x * U t.2 x) (evalWordTerms U L)).trans
      (Set.union_subset (tsupport_mul_subset_left.trans (hL t (List.mem_cons_self))) htail)

theorem evalWordTerms_memLp {O : Set (X n)} (U : List (Yau.RIdx n) → X n → ℂ)
    (L : List (WordTerm n)) (hc : ∀ t ∈ L, Continuous t.1)
    (hcompact : ∀ t ∈ L, HasCompactSupport t.1) (hs : ∀ t ∈ L, tsupport t.1 ⊆ O)
    (hU : ∀ t ∈ L, LocallyL2On (U t.2) O) : MemLp (evalWordTerms U L) 2 (Yau.lebesgueC n) := by
  induction L with
  | nil => exact MemLp.zero'
  | cons t L ih =>
    have ht := Yau.LeafProofs.L14Aux.memLp_compact_multiplier_of_local t.1 (U t.2)
      (hc t (List.mem_cons_self)) (hcompact t (List.mem_cons_self))
      (hs t (List.mem_cons_self)) (hU t (List.mem_cons_self))
    have htail := ih (fun s h => hc s (List.mem_cons_of_mem t h))
      (fun s h => hcompact s (List.mem_cons_of_mem t h))
      (fun s h => hs s (List.mem_cons_of_mem t h))
      (fun s h => hU s (List.mem_cons_of_mem t h))
    exact ht.add htail

def FiniteComplexWeakJet (N : ℕ) (u : X n → ℂ)
    (U : List (Yau.RIdx n) → X n → ℂ) : Prop :=
  U [] = u ∧ (∀ w, w.length ≤ N → MemLp (U w) 2 (Yau.lebesgueC n) ∧ HasCompactSupport (U w)) ∧
    ∀ w, w.length < N → ∀ a, ComplexWeakDerivative (U w) (U (a :: w)) (Yau.realVec a)

theorem weakGraphJet_cutoff {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} {f : X n → Fin n → ℂ} {u : X n → ℂ}
    (U : List (Yau.RIdx n) → X n → ℂ) (N : ℕ) (hJet : WeakGraphJet A f u U N O)
    (χ : X n → ℂ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ O) :
    FiniteComplexWeakJet N (fun x => χ x * u x) (cutoffWordJet χ U) ∧
      ∀ w, tsupport (cutoffWordJet χ U w) ⊆ tsupport χ := by
  have hs (w : List (Yau.RIdx n)) : tsupport (cutoffWordJet χ U w) ⊆ tsupport χ :=
    evalWordTerms_tsupport U _ (cutoffWordTerms_tsupport χ w)
  have h2 (w : List (Yau.RIdx n)) (hw : w.length ≤ N) :
      MemLp (cutoffWordJet χ U w) 2 (Yau.lebesgueC n) :=
    evalWordTerms_memLp U _ (fun t ht => (cutoffWordTerms_smooth hχ w t ht).continuous)
      (fun t ht => hcχ.of_isClosed_subset (isClosed_tsupport _) (cutoffWordTerms_tsupport χ w t ht))
      (fun t ht => (cutoffWordTerms_tsupport χ w t ht).trans hsχ)
      (fun t ht => hJet.2.1 t.2 ((cutoffWordTerms_order χ w t ht).trans hw))
  refine ⟨⟨?_, fun w hw => ⟨h2 w hw, hcχ.of_isClosed_subset (isClosed_tsupport _) (hs w)⟩, ?_⟩, hs⟩
  · funext x
    change χ x * U [] x + 0 = χ x * u x
    rw [hJet.1, add_zero]
  · intro w hw a
    have hd := evalWordTerms_weak_derivative hO U (cutoffWordTerms χ w) a
      (fun t ht => (cutoffWordTerms_smooth hχ w t ht).contDiffOn)
      (fun t ht => hJet.2.1 t.2 ((cutoffWordTerms_order χ w t ht).trans hw.le))
      (fun t ht => hJet.2.1 (a :: t.2) (by
        have hh := (cutoffWordTerms_order χ w t ht).trans_lt hw
        simp only [List.length_cons]
        omega))
      (fun t ht => hJet.2.2.1 t.2 ((cutoffWordTerms_order χ w t ht).trans_lt hw) a)
    exact complexWeakDerivativeOn_global_of_support hO hcχ hsχ hd.2.2 (hs w) (hs (a :: w))

end Yau.LeafProofs.L21Aux
