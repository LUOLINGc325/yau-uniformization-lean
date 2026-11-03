import Yau.LeafProofs.L21QuantitativeCoefficients
import Yau.LeafProofs.L21FiniteJetEnergy

/-! The already proved weak word equation is the literal classical word
equation for the selected smooth representative. -/

open MeasureTheory Filter
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem contDiffOn_evalWordTerms {O : Set (X n)} (U : List (Yau.RIdx n) → X n → ℂ)
    (L : List (WordTerm n)) (hc : ∀ t ∈ L, ContDiffOn ℝ ∞ t.1 O)
    (hU : ∀ t ∈ L, ContDiffOn ℝ ∞ (U t.2) O) : ContDiffOn ℝ ∞ (evalWordTerms U L) O := by
  induction L with
  | nil => exact contDiffOn_const
  | cons t L ih =>
    change ContDiffOn ℝ ∞ (fun x => t.1 x * U t.2 x + evalWordTerms U L x) O
    exact ((hc t (List.mem_cons_self)).mul (hU t (List.mem_cons_self))).add
      (ih (fun s hs => hc s (List.mem_cons_of_mem t hs)) (fun s hs => hU s (List.mem_cons_of_mem t hs)))

theorem contDiffOn_graphWordSource {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (f : X n → Fin n → ℂ) (hf : ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) O)
    (U : List (Yau.RIdx n) → X n → ℂ) (hU : ∀ w, ContDiffOn ℝ ∞ (U w) O)
    (w : List (Yau.RIdx n)) (i : Fin n) :
    ContDiffOn ℝ ∞ (fun x => graphWordSource A f U w x i) O :=
  (contDiffOn_wordDerivative hO (hf i) w).add
    (contDiffOn_evalWordTerms U (correctionTerms A i w) (correctionTerms_smooth hO hA i w) (fun t _ => hU t.2))

theorem dbarWeakOn_smooth_of_pointwise {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (v : X n → ℂ) (hv : ContDiff ℝ ∞ v) (f : X n → Fin n → ℂ)
    (heq : ∀ x ∈ O, ∀ i, dbarA A i v x = f x i) : DbarWeakOn A v f O := by
  have hh := dbarWeakOn_smooth hO hA hv.contDiffOn
  intro i ψ hψ hcψ hsψ
  apply Eq.trans ?_ (hh i ψ hψ hcψ hsψ)
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ O
  · rw [heq x hx i]
  · have hn : x ∉ tsupport ψ := fun hp => hx (hsψ hp)
    simp only [image_eq_zero_of_notMem_tsupport hn, Complex.ofReal_zero, zero_mul]

theorem smooth_word_graph_weak_equation {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (f : X n → Fin n → ℂ) (hf : ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) O)
    (v : X n → ℂ) (hv : ContDiff ℝ ∞ v)
    (heq : ∀ x ∈ O, ∀ i, dbarA A i v x = f x i) (w : List (Yau.RIdx n)) :
    DbarWeakOn A (wordDerivative v w) (graphWordSource A f (wordDerivative v) w) O := by
  have hU (u : List (Yau.RIdx n)) : LocallyL2On (wordDerivative v u) O :=
    locallyL2On_of_continuousOn (contDiff_wordDerivative hv u).continuous.continuousOn
  have hD (u : List (Yau.RIdx n)) (a : Yau.RIdx n) :
      ComplexWeakDerivativeOn O (wordDerivative v u) (wordDerivative v (a :: u)) (Yau.realVec a) :=
    complexWeakDerivativeOn_smooth hO (contDiff_wordDerivative hv u).contDiffOn _
  induction w with
  | nil =>
    have hs : graphWordSource A f (wordDerivative v) [] = f := by
      funext x i
      simp only [graphWordSource, correctionTerms, wordDerivative, evalWordTerms_nil, add_zero]
    rw [hs]
    exact dbarWeakOn_smooth_of_pointwise hO hA v hv f heq
  | cons a w ih =>
    exact graphWordEquation_directional hO hA f hf (wordDerivative v) w.length
      (fun u _ => hU u) (fun u _ => hD u) w le_rfl ih a

theorem smooth_word_graph_equation {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (f : X n → Fin n → ℂ) (hf : ∀ i, ContDiffOn ℝ ∞ (fun x => f x i) O)
    (v : X n → ℂ) (hv : ContDiff ℝ ∞ v)
    (heq : ∀ x ∈ O, ∀ i, dbarA A i v x = f x i)
    (w : List (Yau.RIdx n)) (x : X n) (hx : x ∈ O) (i : Fin n) :
    dbarA A i (wordDerivative v w) x = graphWordSource A f (wordDerivative v) w x i :=
  smooth_representative_satisfies_dbar hO hA (contDiff_wordDerivative hv w).contDiffOn
    (graphWordSource A f (wordDerivative v) w)
    (fun i => contDiffOn_graphWordSource hO hA f hf (wordDerivative v)
      (fun u => (contDiff_wordDerivative hv u).contDiffOn) w i)
    (smooth_word_graph_weak_equation hO hA f hf v hv heq w)
    (Filter.Eventually.of_forall fun _ => rfl) x hx i

end Yau.LeafProofs.L21Aux
