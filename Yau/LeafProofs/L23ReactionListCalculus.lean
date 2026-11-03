import Yau.LeafProofs.L23ReactionLists

/-! Differentiation of the actual finite reaction list. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {M : ComplexManifold n}

theorem jetTermListEval_contDiffOn (L : List (JetTerm k))
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier) (v : Fin (4+k) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => jetTermListEval L h c z v) (chartTarget c) := by
  induction L with
  | nil => exact contDiffOn_const
  | cons e L ih => exact (e.eval_contDiffOn h hh c v).add ih

theorem covariantD_jetTermListEval (L : List (JetTerm k))
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i : RIdx n) (v : Fin (4+k) → RIdx n) :
    covariantD h c (fun w => jetTermListEval L h c w) z (Fin.cons i v)=
      jetTermListEval (k := k+1) (L.flatMap (fun e : JetTerm k => [e.dLeft,e.dRight]))
        h c z (Fin.cons i v) := by
  induction L with
  | nil => simp [jetTermListEval_nil,covariantD,rDeriv]
  | cons e L ih =>
      have hE (u : Fin (4+k) → RIdx n) := ((e.eval_contDiffOn h hh c u).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      have hL (u : Fin (4+k) → RIdx n) := ((jetTermListEval_contDiffOn L h hh c u).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      change covariantD h c (fun w => e.eval h c w+jetTermListEval L h c w) z (Fin.cons i v)=_
      rw [covariantD_add_at h c _ _ z hE hL]
      change covariantD h c (e.eval h c) z (Fin.cons i v)+
        covariantD h c (fun w => jetTermListEval L h c w) z (Fin.cons i v)=_
      rw [e.covariantD_eval h hh c hz,ih]
      simp only [List.flatMap_cons,jetTermListEval_append,jetTermListEval_cons,
        jetTermListEval_nil,Pi.add_apply,Pi.zero_apply]
      ring

theorem reactionListEval_contDiffOn (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (k : ℕ) (v : Fin (4+k) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => reactionListEval h c k z v) (chartTarget c) :=
  jetTermListEval_contDiffOn (reactionTerms k) h hh c v

theorem reactionListEval_succ (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (k : ℕ) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (i : RIdx n) (v : Fin (4+k) → RIdx n) :
    reactionListEval h c (k+1) z (Fin.cons i v)=
      covariantD h c (fun w => reactionListEval h c k w) z (Fin.cons i v)+
        jetTermListEval (extraTerms k) h c z (Fin.cons i v) := by
  change jetTermListEval (k := k+1)
    ((reactionTerms k).flatMap (fun e : JetTerm k => [e.dLeft,e.dRight])++extraTerms k)
    h c z (Fin.cons i v)=_
  rw [jetTermListEval_append]
  change jetTermListEval (k := k+1) ((reactionTerms k).flatMap (fun e : JetTerm k => [e.dLeft,e.dRight]))
    h c z (Fin.cons i v)+_= _
  rw [←covariantD_jetTermListEval (reactionTerms k) h hh c hz]
  rfl

end Yau.LeafProofs.L23Aux
