import Yau.Proofs.P06InitialTraceAssemblyJoint

/-! The original all-chart, all-order initial trace from compact initial
traces, the actual positive-time limit and a genuine uniform remote estimate. -/
noncomputable section
open Set

namespace Yau.NodeProofs.P06Aux.InitialTrace
open Yau Yau.Blueprint
variable {n k : ℕ} {M : ComplexManifold n}

theorem formSmoothInitial_of_jointJetLimit_remoteBounds
    (As : ℕ → RealForm M k) (A : RealForm M k)
    (Us : ℕ → ℝ → RealForm M k) (U : ℝ → RealForm M k)
    (hA : SmoothRealForm A) (hzero : U 0 = A)
    (hUs : ∀ l, 1 ≤ l → SmoothFormTime (Us l) (Ioi 0))
    (hU : SmoothFormTime U (Ioi 0))
    (hinit : ∀ J, 1 ≤ J → FormSmoothInitial (Us J) (As J))
    (hlim : LocalCauchyLimit.JointJetLimit Us U) (hremote : RemoteJetBounds As A Us) :
    FormSmoothInitial U A := by
  exact formSmoothInitial_of_spatialJetLimit_remoteBounds As A Us U hA hzero
    (fun l hl t ht => smoothFormTime_spatial_slice (Us l) (hUs l hl) ht)
    (fun t ht => smoothFormTime_spatial_slice U hU ht) hinit
    (spatialJetLimit_of_jointJetLimit Us U hUs hU hlim) hremote

/-- The two-form specialization consumes the frozen original local-smooth-limit
predicate literally. The remote bound remains a natural internal estimate. -/
theorem formSmoothInitial_of_localSmoothLimit_remoteBounds
    (As : ℕ → RealForm M 2) (A : RealForm M 2)
    (Us : ℕ → ℝ → RealForm M 2) (U : ℝ → RealForm M 2)
    (hA : SmoothRealForm A) (hzero : U 0 = A)
    (hUs : ∀ l, 1 ≤ l → SmoothFormTime (Us l) (Ioi 0))
    (hU : SmoothFormTime U (Ioi 0))
    (hinit : ∀ J, 1 ≤ J → FormSmoothInitial (Us J) (As J))
    (hlim : FormHeatLocalSmoothLimit Us U) (hremote : RemoteJetBounds As A Us) :
    FormSmoothInitial U A :=
  formSmoothInitial_of_jointJetLimit_remoteBounds As A Us U hA hzero hUs hU hinit hlim hremote

end Yau.NodeProofs.P06Aux.InitialTrace
