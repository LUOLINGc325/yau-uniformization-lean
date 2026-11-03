import Yau.Proofs.Y05Taylor
import Yau.Proofs.Y01PolynomialJets
import Yau.Proofs.Y01DirectionalCoefficients

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment MvPolynomial Yau.Proofs.Y02Aux
open scoped ContDiff

section Composition

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] {d : ℕ}

theorem finite_taylorComp_congr
    {p p' : FormalMultilinearSeries ℂ E F} {q q' : FormalMultilinearSeries ℂ F G}
    (hp : ∀ m ≤ d, p m = p' m) (hq : ∀ m ≤ d, q m = q' m)
    {m : ℕ} (hm : m ≤ d) : q.taylorComp p m = q'.taylorComp p' m := by
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_congr rfl
  intro c hc
  unfold FormalMultilinearSeries.compAlongOrderedFinpartition
  rw [hq c.length (c.length_le.trans hm)]
  congr 1
  funext j
  exact hp (c.partSize j) ((c.partSize_le j).trans hm)

theorem iteratedFDeriv_comp_congr_through
    {f f' : E → F} {g g' : F → G}
    (hf : ContDiffAt ℂ d f 0) (hf' : ContDiffAt ℂ d f' 0)
    (hg : ContDiffAt ℂ d g 0) (hg' : ContDiffAt ℂ d g' 0)
    (hf0 : f 0 = 0) (hf'0 : f' 0 = 0)
    (hff' : ∀ m ≤ d, iteratedFDeriv ℂ m f 0 = iteratedFDeriv ℂ m f' 0)
    (hgg' : ∀ m ≤ d, iteratedFDeriv ℂ m g 0 = iteratedFDeriv ℂ m g' 0) :
    ∀ m ≤ d, iteratedFDeriv ℂ m (g ∘ f) 0 = iteratedFDeriv ℂ m (g' ∘ f') 0 := by
  intro m hm
  have hgF : ContDiffAt ℂ d g (f 0) := by simpa only [hf0] using hg
  have hgF' : ContDiffAt ℂ d g' (f' 0) := by simpa only [hf'0] using hg'
  rw [iteratedFDeriv_comp hgF hf (by exact_mod_cast hm),
    iteratedFDeriv_comp hgF' hf' (by exact_mod_cast hm), hf0, hf'0]
  exact finite_taylorComp_congr hff' hgg' hm

end Composition

variable {n d : ℕ}

theorem scalarJetEq_coefficients {P Q : MvPolynomial (Fin n) ℂ}
    (h : ScalarJetEq (scalarEval P) (scalarEval Q) d)
    (a : Fin n →₀ ℕ) (ha : a.degree ≤ d) : P.coeff a = Q.coeff a := by
  have hP := (Yau.Proofs.Y01Aux.polyEval_contDiff P).of_le
    (WithTop.coe_le_coe.mpr (le_top : (a.degree : ℕ∞) ≤ ⊤))
  have hQ := (Yau.Proofs.Y01Aux.polyEval_contDiff Q).of_le
    (WithTop.coe_le_coe.mpr (le_top : (a.degree : ℕ∞) ≤ ⊤))
  have heval : Yau.Proofs.Y01Aux.polyEval (P - Q) =
      Yau.Proofs.Y01Aux.polyEval P - Yau.Proofs.Y01Aux.polyEval Q := by
    funext z; exact map_sub _ _ _
  have hz : iteratedFDeriv ℂ a.degree (Yau.Proofs.Y01Aux.polyEval (P - Q)) 0 = 0 := by
    rw [heval, iteratedFDeriv_sub_apply hP.contDiffAt hQ.contDiffAt]
    change iteratedFDeriv ℂ a.degree (scalarEval P) 0 -
      iteratedFDeriv ℂ a.degree (scalarEval Q) 0 = 0
    rw [h a.degree ha, sub_self]
  have hb := Yau.Proofs.Y01Aux.scalar_coeff_norm_le_jet (P - Q) a
  rw [hz, norm_zero] at hb
  exact sub_eq_zero.mp (by simpa only [coeff_sub] using
    (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))))

theorem scalar_taylor_unique {P Q : MvPolynomial (Fin n) ℂ}
    (hP : P.totalDegree ≤ d) (hQ : Q.totalDegree ≤ d)
    (h : ScalarJetEq (scalarEval P) (scalarEval Q) d) : P = Q := by
  ext a
  by_cases ha : a.degree ≤ d
  · exact scalarJetEq_coefficients h a ha
  · have hp : P.coeff a = 0 := coeff_eq_zero_of_totalDegree_lt (by
      change P.totalDegree < a.degree; omega)
    have hq : Q.coeff a = 0 := coeff_eq_zero_of_totalDegree_lt (by
      change Q.totalDegree < a.degree; omega)
    rw [hp, hq]

def scalarTruncate (d : ℕ) (P : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  ⟨Finsupp.filter (fun a : Fin n →₀ ℕ => a.degree ≤ d) P.coeff⟩

theorem scalarTruncate_coeff (d : ℕ) (P : MvPolynomial (Fin n) ℂ) (a : Fin n →₀ ℕ) :
    (scalarTruncate d P).coeff a = if a.degree ≤ d then P.coeff a else 0 := rfl

theorem scalarTruncate_degree (d : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    (scalarTruncate d P).totalDegree ≤ d := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro a ha
  exact (Finset.mem_filter.1 ha).2

theorem scalarTruncate_jetEq (d : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    ScalarJetEq (scalarEval (scalarTruncate d P)) (scalarEval P) d := by
  exact fun m hm => Yau.Proofs.Y01Aux.scalar_jetEq_iteratedFDeriv
    (fun a ha => by rw [scalarTruncate_coeff, if_pos ha]) hm

theorem scalarTruncate_coeffNorm_le (d : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    polynomialCoeffNorm (scalarTruncate d P) ≤ polynomialCoeffNorm P := by
  classical
  have hs : (scalarTruncate d P).support ⊆ P.support := Finset.filter_subset _ _
  rw [← sum_norm_coeff_eq (scalarTruncate d P) P.support hs]
  apply Finset.sum_le_sum
  intro a ha
  rw [scalarTruncate_coeff]
  split_ifs
  · exact le_rfl
  · simp

end Yau.Proofs.Y05Aux
