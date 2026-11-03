import Yau.Proofs.P06HodgeRegularityWeakJets
import Yau.Proofs.P06HodgeRegularityScalarEnergy

/-! Ordered Leibniz splits for actual finite weak jets. Multiplicities are
retained, and no exchange of weak word derivatives is required. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def regularityCoefficientWord (v : ι → E) : List ι → (E → ℝ) → E → ℝ
  | [], a => a
  | i::w, a => regularityDirection (v i) (regularityCoefficientWord v w a)

theorem regularityCoefficientWord_regular (v : ι → E) {a : E → ℝ}
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a) (w : List ι) :
    ContDiff ℝ ∞ (regularityCoefficientWord v w a) ∧
      HasCompactSupport (regularityCoefficientWord v w a) ∧
      tsupport (regularityCoefficientWord v w a) ⊆ tsupport a := by
  induction w with
  | nil => exact ⟨ha, hca, Set.Subset.rfl⟩
  | cons i w ih =>
    exact ⟨regularityDirection_contDiff ih.1 (v i), ih.2.1.fderiv_apply ℝ (v i),
      (tsupport_fderiv_apply_subset ℝ (v i)).trans ih.2.2⟩

def regularityWordSplits : List ι → List (List ι × List ι)
  | [] => [([],[])]
  | i::w => (regularityWordSplits w).flatMap (fun st => [(i::st.1,st.2),(st.1,i::st.2)])

theorem regularityWordSplits_lengths (w : List ι) (st : List ι × List ι)
    (h : st ∈ regularityWordSplits w) : st.1.length + st.2.length = w.length := by
  induction w generalizing st with
  | nil =>
    simp only [regularityWordSplits, List.mem_singleton] at h
    subst st
    rfl
  | cons i w ih =>
    simp only [regularityWordSplits, List.mem_flatMap] at h
    obtain ⟨ab, hab, hs⟩ := h
    have hlen := ih ab hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp only [List.length_cons] <;> omega

def regularityLeibnizJet (v : ι → E) (a : E → ℝ) (J : List ι → E → α → ℝ)
    (w : List ι) (z : E) (c : α) : ℝ :=
  ((regularityWordSplits w).map (fun st => regularityCoefficientWord v st.1 a z * J st.2 z c)).sum

theorem regularityLeibnizJet_nil (v : ι → E) (a : E → ℝ) (J : List ι → E → α → ℝ)
    (z : E) (c : α) : regularityLeibnizJet v a J [] z c = a z * J [] z c := by
  simp only [regularityLeibnizJet, regularityWordSplits, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, regularityCoefficientWord]

theorem regularityLeibnizJet_cons (v : ι → E) (a : E → ℝ) (J : List ι → E → α → ℝ)
    (w : List ι) (i : ι) (z : E) (c : α) :
    regularityLeibnizJet v a J (i::w) z c =
      ((regularityWordSplits w).map (fun st =>
        regularityCoefficientWord v (i::st.1) a z * J st.2 z c +
          regularityCoefficientWord v st.1 a z * J (i::st.2) z c)).sum := by
  unfold regularityLeibnizJet
  simp only [regularityWordSplits, List.map_flatMap, List.map_cons, List.map_nil]
  induction regularityWordSplits w with
  | nil => simp
  | cons st xs ih => simp only [List.flatMap_cons, List.map_cons, List.map_nil,
      List.map_append, List.sum_append, List.sum_cons, List.sum_nil, add_zero, ih]

end Yau.NodeProofs.P06Aux
