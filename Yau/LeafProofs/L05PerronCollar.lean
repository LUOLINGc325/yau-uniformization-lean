import Yau.LeafProofs.L05PerronCalculus

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem perron_two_point_collar {n : ℕ} {K Gamma : Set (Point n)}
    (hGamma : IsCompact Gamma) (hGK : Gamma⊆K) {u v : Point n → ℝ}
    (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v K)
    (hbd : ∀ p∈Gamma, u p≤v p) {eta : ℝ} (heta : 0<eta) :
    ∃ rho : ℝ, 0<rho ∧ ∀ p∈Gamma, ∀ q∈K, ∀ r∈K,
      dist q p<rho → dist r p<rho → u q-v r<eta := by
  classical
  have hloc (p : Gamma) : ∃ R : ℝ, 0<R ∧
      (∀ q∈K, dist q p<R → u q<u p+eta/3) ∧
      (∀ r∈K, dist r p<R → v p-eta/3<v r) := by
    have hup := hu p (hGK p.property) (u p+eta/3) (by linarith)
    have hvp := hv p (hGK p.property) (v p-eta/3) (by linarith)
    obtain ⟨Ru,hRu,huR⟩ := Metric.mem_nhdsWithin_iff.mp hup
    obtain ⟨Rv,hRv,hvR⟩ := Metric.mem_nhdsWithin_iff.mp hvp
    refine ⟨min Ru Rv,lt_min hRu hRv,?_,?_⟩
    · intro q hq hdist
      exact huR ⟨(Metric.mem_ball.mpr (hdist.trans_le (min_le_left _ _))),hq⟩
    · intro r hr hdist
      exact hvR ⟨(Metric.mem_ball.mpr (hdist.trans_le (min_le_right _ _))),hr⟩
  choose R hR hU hV using hloc
  have hcover : Gamma⊆⋃ p : Gamma, Metric.ball (p : Point n) (R p/4) := by
    intro p hp
    exact Set.mem_iUnion.mpr ⟨⟨p,hp⟩,Metric.mem_ball_self (div_pos (hR ⟨p,hp⟩) (by norm_num))⟩
  obtain ⟨t,ht⟩ := hGamma.elim_finite_subcover
    (fun p : Gamma => Metric.ball (p : Point n) (R p/4)) (fun _ => Metric.isOpen_ball) hcover
  have hfinite (s : Finset Gamma) : ∃ rho : ℝ, 0<rho ∧ ∀ p∈s, rho<R p/4 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert p s hps ih =>
      obtain ⟨rho,hrho,hs⟩ := ih
      have hRp : 0<R p/4 := div_pos (hR p) (by norm_num)
      obtain ⟨rho',hpos,hsmall⟩ := exists_between (lt_min hrho hRp)
      refine ⟨rho',hpos,?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with hqp | hq
      · subst q
        exact hsmall.trans_le (min_le_right _ _)
      · exact (hsmall.trans_le (min_le_left _ _)).trans (hs q hq)
  obtain ⟨rho,hrho,hr⟩ := hfinite t
  refine ⟨rho,hrho,?_⟩
  intro p hp q hq r hrK hqp hrp
  obtain ⟨c,hc⟩ := Set.mem_iUnion.mp (ht hp)
  obtain ⟨hct,hpc⟩ := Set.mem_iUnion.mp hc
  have hpdist := Metric.mem_ball.mp hpc
  have hqdist : dist q c<R c := by
    have hh := dist_triangle q p c
    linarith [hr c hct,hR c]
  have hrdist : dist r c<R c := by
    have hh := dist_triangle r p c
    linarith [hr c hct,hR c]
  have hqv := hU c q hq hqdist
  have hrv := hV c r hrK hrdist
  have hcv := hbd c c.property
  linarith

end Yau.LeafProofs.L05Aux
