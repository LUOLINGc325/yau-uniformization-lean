import Yau.LeafProofs.L17BootstrapClosedSlabJets

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapEvolutionJetsAux
open L17BootstrapClosedSlabAux

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev JetPack (m : ℕ) := (j : Fin (m+1)) → Jet E ℝ j.val
abbrev State (k : ℕ) := (E × ℝ) × JetPack E (k+2)

def restrictPack {m r : ℕ} (h : m ≤ r) : JetPack E r →L[ℝ] JetPack E m :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.castLE (Nat.succ_le_succ h) j)

def truncateState (k : ℕ) : State E (k+1) →L[ℝ] State E k :=
  (ContinuousLinearMap.id ℝ (E × ℝ)).prodMap (restrictPack E (Nat.le_succ (k+2)))

def projectBaseState (k : ℕ) : State E k →L[ℝ] State E 0 :=
  (ContinuousLinearMap.id ℝ (E × ℝ)).prodMap (restrictPack E (by omega : 2 ≤ k+2))

@[simp] theorem projectBaseState_zero (s : State E 0) : projectBaseState E 0 s=s := by
  rfl

@[simp] theorem projectBaseState_truncate (k : ℕ) (s : State E (k+1)) :
    projectBaseState E k (truncateState E k s)=projectBaseState E (k+1) s := by
  rfl

abbrev nextIndex {k : ℕ} (j : Fin (k+3)) : Fin (k+4) := ⟨j.val+1,by omega⟩

def spatialJetProjection (k : ℕ) (j : Fin (k+3)) :
    State E (k+1) →L[ℝ] (E →L[ℝ] Jet E ℝ j.val) :=
  (ContinuousLinearMap.proj (nextIndex j)).comp
    (ContinuousLinearMap.snd ℝ (E × ℝ) (JetPack E (k+3)))

def spatialJetDirection (k : ℕ) : State E (k+1) →L[ℝ] (E →L[ℝ] JetPack E (k+2)) :=
  (ContinuousLinearMap.piEquivL ℝ E (fun j : Fin (k+3) => Jet E ℝ j.val)).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => spatialJetProjection E k j)

def spatialDirection (k : ℕ) (s : State E (k+1)) : E →L[ℝ] State E k :=
  (ContinuousLinearMap.inl ℝ E ℝ).prod (spatialJetDirection E k s)

@[simp] theorem spatialDirection_apply (k : ℕ) (s : State E (k+1)) (a : E) :
    spatialDirection E k s a=((a,0),fun j => spatialJetProjection E k j s a) := rfl

theorem spatialDirection_contDiff (k : ℕ) : ContDiff ℝ ∞ (spatialDirection E k) := by
  let P : ((E →L[ℝ] E × ℝ) × (E →L[ℝ] JetPack E (k+2))) ≃L[ℝ]
      (E →L[ℝ] State E k) := ContinuousLinearMap.prodL ℝ
  have hP : ContDiff ℝ ∞ P := P.contDiff
  have hPair : ContDiff ℝ ∞ (fun s : State E (k+1) =>
      (ContinuousLinearMap.inl ℝ E ℝ,spatialJetDirection E k s)) :=
    contDiff_const.prodMk (spatialJetDirection E k).contDiff
  exact hP.comp hPair

end Yau.LeafProofs.L17BootstrapEvolutionJetsAux
