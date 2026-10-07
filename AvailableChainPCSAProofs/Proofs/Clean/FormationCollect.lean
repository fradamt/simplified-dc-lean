module
public import AvailableChainPCSAProofs.Proofs.Foundations.Install
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool
public import AvailableChainPCSA.Model.Frame
public import AvailableChainPCSA.Statements.Invariants

public section

/-! Formation PC collection and installation (pcsa34-r4.3b §5.3).
A collected store holds every supported, resolved PC identity. Every
reachable store is collected. A standalone PC installs only its slot and
root. A completing ack belongs to the certificate that its call installs.
These facts supply the whole-PC relay trigger. The proposal case and the
run-level early-view bound remain open. No whole claim is exported. -/

open AvailableChain
namespace AvailableChain.PCSA
variable {n : Nat}

def FormationPCIdentity (st : State n) (s : Slot) (b : Block) : Prop :=
  ∃ C ∈ st.pcs, C.slot = s ∧ C.target = b

theorem FormationPCIdentity_def (st : State n) (s : Slot) (b : Block) :
    FormationPCIdentity st s b = (∃ C ∈ st.pcs, C.slot = s ∧ C.target = b) := by
  apply propext
  exact ⟨fun h => h, fun h => h⟩

private theorem formation_identity_mono (st st' : State n) (s : Slot) (b : Block)
    (h : st.pcs ⊆ st'.pcs) : FormationPCIdentity st s b → FormationPCIdentity st' s b := by
  rintro ⟨C, hC, hs, hb⟩
  exact ⟨C, h hC, hs, hb⟩

private theorem formation_collect_step_frame (st : State n) (sr : Slot × BlockId) :
    let dst := match st.base.blocks.find? (fun b => b.root == sr.2) with
      | none => st
      | some b => match assemblePC st sr.1 b with
        | none => st
        | some C => installPC st C
    dst.base.blocks = st.base.blocks ∧ dst.ackPool = st.ackPool ∧
      dst.fg = st.fg ∧ st.pcs ⊆ dst.pcs := by
  dsimp only
  cases st.base.blocks.find? (fun b => b.root == sr.2) with
  | none => exact ⟨rfl, rfl, rfl, List.Subset.refl _⟩
  | some b =>
    dsimp only
    cases assemblePC st sr.1 b with
    | none => exact ⟨rfl, rfl, rfl, List.Subset.refl _⟩
    | some C => exact ⟨(installPC_frame st C).2.1,
        (installPC_frame st C).2.2.1, (installPC_frame st C).2.2.2.2,
        installPC_pcs_mono st C⟩

private theorem formation_identity_install (st : State n) (C : PC n) :
    FormationPCIdentity (installPC st C) C.slot C.target := by
  cases h : st.pcs.any (fun A => A.slot == C.slot && A.target == C.target) with
  | true =>
    rw [installPC_duplicate st C h]
    obtain ⟨A, ha, he⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    exact ⟨A, ha, he⟩
  | false =>
    refine ⟨C, ?_, rfl, rfl⟩
    rw [installPC_pcs_new st C h]
    exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem formation_collect_fold_mono (cs : List (Slot × BlockId)) (st : State n) :
    st.pcs ⊆ (cs.foldl (fun acc sr =>
      match acc.base.blocks.find? (fun b => b.root == sr.2) with
      | none => acc
      | some b => match assemblePC acc sr.1 b with
        | none => acc
        | some C => installPC acc C) st).pcs := by
  induction cs generalizing st with
  | nil => exact List.Subset.refl _
  | cons sr cs ih =>
    rw [List.foldl_cons]
    exact List.Subset.trans (formation_collect_step_frame st sr).2.2.2 (ih _)

private theorem formation_assemble_eq_of_frame (st st' : State n) (s : Slot) (b : Block)
    (hb : st'.base.blocks = st.base.blocks) (ha : st'.ackPool = st.ackPool)
    (hf : st'.fg = st.fg) : assemblePC st' s b = assemblePC st s b := by
  delta assemblePC pcValid acksOn activeCompatible
  rw [hb, ha, hf]

private theorem formation_collect_fold_identity (cs : List (Slot × BlockId))
    (st : State n) (s : Slot) (b : Block) (C : PC n)
    (hm : (s, b.root) ∈ cs)
    (hb : st.base.blocks.find? (fun B => B.root == b.root) = some b)
    (hc : assemblePC st s b = some C) :
    FormationPCIdentity (cs.foldl (fun acc sr =>
      match acc.base.blocks.find? (fun B => B.root == sr.2) with
      | none => acc
      | some B => match assemblePC acc sr.1 B with
        | none => acc
        | some D => installPC acc D) st) s b := by
  induction cs generalizing st with
  | nil => exact (List.not_mem_nil hm).elim
  | cons sr cs ih =>
    rw [List.foldl_cons]
    let dst := match st.base.blocks.find? (fun B => B.root == sr.2) with
      | none => st
      | some B => match assemblePC st sr.1 B with
        | none => st
        | some D => installPC st D
    have hd := formation_collect_step_frame st sr
    rcases List.mem_cons.mp hm with he | hm
    · subst sr
      change FormationPCIdentity (cs.foldl _ dst) s b
      apply formation_identity_mono dst _ s b (formation_collect_fold_mono cs dst)
      dsimp only [dst]
      rw [hb]
      dsimp only
      rw [hc]
      have he := (assemblePC_some_iff st s b C).mp hc
      obtain rfl := he.1
      exact formation_identity_install st _
    · apply ih dst hm
      · rw [hd.1]
        exact hb
      · rw [formation_assemble_eq_of_frame st dst s b hd.1 hd.2.1 hd.2.2.1]
        exact hc

/-- A visited, resolved candidate is installed by collection. -/
theorem pcsa_formation_collect_identity (st : State n) (s : Slot) (b : Block)
    (C : PC n)
    (hm : (s, b.root) ∈ (st.ackPool.filterMap (fun a =>
      (AckWire.decode? a).map (fun x => (x.1, x.2.2)))).eraseDups)
    (hb : st.base.blocks.find? (fun B => B.root == b.root) = some b)
    (hc : assemblePC st s b = some C) : FormationPCIdentity (collectPCs st) s b := by
  delta collectPCs
  exact formation_collect_fold_identity _ st s b C hm hb hc

private theorem formation_collect_new_origin (cs : List (Slot × BlockId))
    (st : State n) (C : PC n)
    (hm : C ∈ (cs.foldl (fun acc sr =>
      match acc.base.blocks.find? (fun B => B.root == sr.2) with
      | none => acc
      | some B => match assemblePC acc sr.1 B with
        | none => acc
        | some D => installPC acc D) st).pcs)
    (hNew : C ∉ st.pcs) :
    (C.slot, C.target.root) ∈ cs ∧
      st.base.blocks.find? (fun B => B.root == C.target.root) = some C.target ∧
      assemblePC st C.slot C.target = some C := by
  induction cs generalizing st with
  | nil => exact (hNew hm).elim
  | cons sr cs ih =>
    rw [List.foldl_cons] at hm
    let dst := match st.base.blocks.find? (fun B => B.root == sr.2) with
      | none => st
      | some B => match assemblePC st sr.1 B with
        | none => st
        | some D => installPC st D
    have hf := formation_collect_step_frame st sr
    by_cases hDst : C ∈ dst.pcs
    · dsimp only [dst] at hDst
      cases hb : st.base.blocks.find? (fun B => B.root == sr.2) with
      | none => rw [hb] at hDst; exact (hNew hDst).elim
      | some B =>
        rw [hb] at hDst
        dsimp only at hDst
        cases hc : assemblePC st sr.1 B with
        | none => rw [hc] at hDst; exact (hNew hDst).elim
        | some D =>
          rw [hc] at hDst
          obtain hOld | rfl := mem_installPC_pcs st D C hDst
          · exact (hNew hOld).elim
          · have he := (assemblePC_some_iff st sr.1 B C).mp hc
            have hs : C.slot = sr.1 := congrArg PC.slot he.1
            have ht : C.target = B := congrArg PC.target he.1
            have hr : B.root = sr.2 := by simpa only [beq_iff_eq] using List.find?_some hb
            have hp : (C.slot, C.target.root) = sr := by
              apply Prod.ext
              · exact hs
              · exact (congrArg Block.root ht).trans hr
            refine ⟨hp.symm ▸ (List.mem_cons_self : sr ∈ sr :: cs), ?_, ?_⟩
            · rw [ht, hr]
              exact hb
            · rw [hs, ht]
              exact hc
    · obtain ⟨hcs, hb, hc⟩ := ih dst hm hDst
      refine ⟨List.mem_cons_of_mem sr hcs, ?_, ?_⟩
      · rw [hf.1] at hb
        exact hb
      · rw [formation_assemble_eq_of_frame st dst C.slot C.target hf.1 hf.2.1 hf.2.2.1] at hc
        exact hc

/-- A new collected certificate is exactly a resolved assembly candidate. -/
theorem pcsa_formation_collect_new_origin (st : State n) (C : PC n)
    (hm : C ∈ (collectPCs st).pcs) (hNew : C ∉ st.pcs) :
    (C.slot, C.target.root) ∈ (st.ackPool.filterMap (fun a =>
      (AckWire.decode? a).map (fun x => (x.1, x.2.2)))).eraseDups ∧
      st.base.blocks.find? (fun B => B.root == C.target.root) = some C.target ∧
      assemblePC st C.slot C.target = some C := by
  delta collectPCs at hm
  exact formation_collect_new_origin _ st C hm hNew

/-- Every supported root candidate has its installed PC identity. -/
def FormationCollected (st : State n) : Prop :=
  ∀ (s : Slot) (b : Block) (C : PC n),
    (s, b.root) ∈ (st.ackPool.filterMap (fun a =>
      (AckWire.decode? a).map (fun x => (x.1, x.2.2)))).eraseDups →
    st.base.blocks.find? (fun B => B.root == b.root) = some b →
    assemblePC st s b = some C → FormationPCIdentity st s b

theorem FormationCollected_def (st : State n) : FormationCollected st =
    (∀ (s : Slot) (b : Block) (C : PC n),
      (s, b.root) ∈ (st.ackPool.filterMap (fun a =>
        (AckWire.decode? a).map (fun x => (x.1, x.2.2)))).eraseDups →
      st.base.blocks.find? (fun B => B.root == b.root) = some b →
      assemblePC st s b = some C → FormationPCIdentity st s b) := by
  apply propext
  exact ⟨fun h => h, fun h => h⟩

/-- Collection leaves no supported candidate without an installed identity. -/
theorem pcsa_formation_collect_invariant (st : State n) : FormationCollected (collectPCs st) := by
  intro s b C hm hb hc
  have hf := collectPCs_frame st
  rw [hf.2.2.1] at hm
  rw [hf.2.1] at hb
  rw [formation_assemble_eq_of_frame st (collectPCs st) s b
    hf.2.1 hf.2.2.1 hf.2.2.2.2] at hc
  exact pcsa_formation_collect_identity st s b C hm hb hc

/-- Changes outside the assembly inputs preserve collection closure. -/
theorem pcsa_formation_collected_of_frame (st st' : State n)
    (h : FormationCollected st)
    (hb : st'.base.blocks = st.base.blocks) (ha : st'.ackPool = st.ackPool)
    (hf : st'.fg = st.fg) (hp : st.pcs ⊆ st'.pcs) : FormationCollected st' := by
  intro s b C hm hfind hc
  rw [ha] at hm
  rw [hb] at hfind
  rw [formation_assemble_eq_of_frame st st' s b hb ha hf] at hc
  exact formation_identity_mono st st' s b hp (h s b C hm hfind hc)

private theorem formation_pc_nonempty (C : PC n) (hn : 0 < n)
    (hw : C.wellFormed = true) : C.acks ≠ [] := by
  have h1 := (Bool.and_eq_true_iff.mp hw).1
  have h2 := (Bool.and_eq_true_iff.mp h1).1
  have hCard : pcQuorum n ≤ C.acks.length :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h2).2
  have hq : 0 < pcQuorum n := by delta pcQuorum; omega
  intro he
  rw [he] at hCard
  simp only [List.length_nil] at hCard
  omega

private theorem formation_firstPerSeat_subset (as : List (AckWire n)) :
    firstPerSeat as ⊆ as := by
  delta firstPerSeat
  suffices ∀ acc : List (AckWire n), acc ⊆ as →
      (as.foldl (fun acc a =>
        if acc.any (fun old => old.seat? == a.seat?) then acc else acc ++ [a]) acc) ⊆ as
    from this [] (by simp)
  intro acc h
  apply List.foldlRecOn (motive := fun acc => acc ⊆ as)
  · exact h
  · intro acc ha a hm
    split
    · exact ha
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ha hb
      · exact List.mem_singleton.mp hb ▸ hm

private theorem formation_assembly_candidate (st : State n) (s : Slot) (b : Block)
    (C : PC n) (hn : 0 < n) (hc : assemblePC st s b = some C) :
    (s, b.root) ∈ (st.ackPool.filterMap (fun a =>
      (AckWire.decode? a).map (fun x => (x.1, x.2.2)))).eraseDups := by
  have he := (assemblePC_some_iff st s b C).mp hc
  have hw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp he.2).1).1
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil C.acks (formation_pc_nonempty C hn hw)
  have hm : a ∈ acksOn st s b.root := by
    rw [he.1] at ha
    exact formation_firstPerSeat_subset _ ha
  obtain ⟨hp, i, hd⟩ := (mem_acksOn_iff st s b.root a).mp hm
  apply List.mem_eraseDups.mpr
  exact List.mem_filterMap.mpr ⟨a, hp, by rw [hd]; rfl⟩

/-- A resolved assembly has its installed identity in a collected store. -/
theorem pcsa_formation_collected_identity (st : State n) (s : Slot) (b : Block)
    (C : PC n) (hn : 0 < n) (h : FormationCollected st)
    (hb : st.base.blocks.find? (fun B => B.root == b.root) = some b)
    (hc : assemblePC st s b = some C) : FormationPCIdentity st s b :=
  h s b C (formation_assembly_candidate st s b C hn hc) hb hc

private theorem formation_assemble_eq_of_on (st st' : State n) (s : Slot) (b : Block)
    (hb : st'.base.blocks = st.base.blocks) (hf : st'.fg = st.fg)
    (ha : acksOn st' s b.root = acksOn st s b.root) :
    assemblePC st' s b = assemblePC st s b := by
  delta assemblePC
  rw [ha]
  delta pcValid activeCompatible
  rw [hb, hf]

private theorem formation_poolRaw_on_miss (st : State n) (a : AckWire n)
    (s : Slot) (r : BlockId) (hMiss : ∀ i, (AckWire.decode? a) ≠ some (s, i, r)) :
    acksOn (poolAckRaw st a) s r = acksOn st s r := by
  delta poolAckRaw
  cases hd : (AckWire.decode? a) with
  | none => rfl
  | some x =>
    dsimp only
    split
    · rfl
    · delta acksOn
      rw [List.filter_append]
      have hm : (match (AckWire.decode? a) with
          | some (s', _, r') => s' == s && r' == r
          | none => false) = false := by
        rw [hd]
        rcases x with ⟨s', i, r'⟩
        dsimp only
        apply Bool.eq_false_iff.mpr
        intro ht
        simp only [Bool.and_eq_true, beq_iff_eq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact hMiss i hd
      have hnil : [a].filter (fun a => match (AckWire.decode? a) with
          | some (s', _, r') => s' == s && r' == r
          | none => false) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        obtain rfl := List.mem_singleton.mp hb
        intro ht
        have hh := hm.symm.trans ht
        cases hh
      exact (congrArg (fun xs => st.ackPool.filter (fun a => match (AckWire.decode? a) with
        | some (s', _, r') => s' == s && r' == r
        | none => false) ++ xs) hnil).trans (List.append_nil _)

private theorem formation_raw_on_miss (st : State n) (as : List (AckWire n))
    (s : Slot) (r : BlockId) (hMiss : ∀ a ∈ as, ∀ i, (AckWire.decode? a) ≠ some (s, i, r)) :
    acksOn (as.foldl poolAckRaw st) s r = acksOn st s r := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, ih _ (fun b hb => hMiss b (List.mem_cons_of_mem a hb)),
      formation_poolRaw_on_miss st a s r (hMiss a List.mem_cons_self)]

private theorem formation_raw_frame (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).base.blocks = st.base.blocks ∧
      (as.foldl poolAckRaw st).fg = st.fg ∧ (as.foldl poolAckRaw st).pcs = st.pcs := by
  induction as generalizing st with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons a as ih =>
    rw [List.foldl_cons]
    have ht := ih (poolAckRaw st a)
    have hs := poolAckRaw_frame st a
    exact ⟨ht.1.trans (congrArg (fun v => v.blocks) hs.2.2.1),
      ht.2.1.trans hs.2.2.2, ht.2.2.trans hs.1⟩

private theorem formation_pc_ack_decode (D : PC n) (hD : D.wellFormed = true)
    (a : AckWire n) (ha : a ∈ D.acks) :
    ∃ i, (AckWire.decode? a) = some (D.slot, i, D.target.root) := by
  have hd := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hD).2 a ha
  rcases a with ⟨auth, root⟩
  cases auth with
  | none => change false = true at hd; cases hd
  | proposer k => change false = true at hd; cases hd
  | seat l j =>
    cases l with
    | head k => change false = true at hd; cases hd
    | fg => change false = true at hd; cases hd
    | ack k =>
      change (k == D.slot && root == D.target.root) = true at hd
      simp only [Bool.and_eq_true, beq_iff_eq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      exact ⟨j, rfl⟩

/-- A standalone PC wire can newly install only its slot and root.
Collection closure excludes an unrelated candidate from an earlier pool. -/
theorem pcsa_formation_admitPC_root (st : State n) (D C : PC n) (hn : 0 < n)
    (hClosed : FormationCollected st) (hD : D.wellFormed = true)
    (hNew : ¬FormationPCIdentity st C.slot C.target)
    (hm : C ∈ (admitPC st D).pcs) : D.slot = C.slot ∧ D.target.root = C.target.root := by
  have hf := formation_raw_frame st D.acks
  have hNot : C ∉ (D.acks.foldl poolAckRaw st).pcs := by
    rw [hf.2.2]
    intro hc
    exact hNew ⟨C, hc, rfl, rfl⟩
  change C ∈ (if D.wellFormed then collectPCs (D.acks.foldl poolAckRaw st) else st).pcs at hm
  rw [ite_eq_left hD] at hm
  obtain ⟨_, hb, hc⟩ := pcsa_formation_collect_new_origin _ C hm hNot
  by_contra hDiff
  have hMiss : ∀ a ∈ D.acks, ∀ i, (AckWire.decode? a) ≠ some (C.slot, i, C.target.root) := by
    intro a ha i hi
    obtain ⟨j, hd⟩ := formation_pc_ack_decode D hD a ha
    have he := Option.some.inj (hd.symm.trans hi)
    simp only [Prod.mk.injEq] at he
    exact hDiff ⟨he.1, he.2.2⟩
  have hOn := formation_raw_on_miss st D.acks C.slot C.target.root hMiss
  rw [formation_assemble_eq_of_on st _ C.slot C.target hf.1 hf.2.1 hOn] at hc
  rw [hf.1] at hb
  exact hNew (pcsa_formation_collected_identity st _ _ C hn hClosed hb hc)

private theorem formation_ack_shape (a : AckWire n) (s : Slot) (i : Fin n)
    (r : BlockId) (hd : (AckWire.decode? a) = some (s, i, r)) :
    a = ⟨.seat (.ack s) i, r⟩ := by
  rcases a with ⟨auth, root⟩
  cases auth with
  | none => cases hd
  | proposer k => cases hd
  | seat l j =>
    cases l with
    | head k => cases hd
    | fg => cases hd
    | ack k =>
      change some (k, j, root) = some (s, i, r) at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      rfl

private theorem formation_first_fold_covers (D : List (AckWire n))
    (hInj : ∀ x ∈ D, ∀ y ∈ D, (AckWire.seat? x) = (AckWire.seat? y) → x = y)
    (as acc : List (AckWire n)) (hAs : as ⊆ D) (hAcc : acc ⊆ D)
    (a : AckWire n) (ha : a ∈ acc ∨ a ∈ as) :
    a ∈ as.foldl (fun acc b =>
      if acc.any (fun old => (AckWire.seat? old) == (AckWire.seat? b)) then acc
      else acc ++ [b]) acc := by
  induction as generalizing acc with
  | nil => simpa using ha
  | cons b as ih =>
    rw [List.foldl_cons]
    let next :=
      if acc.any (fun old => (AckWire.seat? old) == (AckWire.seat? b)) then acc
      else acc ++ [b]
    have hb : b ∈ D := hAs List.mem_cons_self
    have hMono : acc ⊆ next := by
      dsimp only [next]
      split
      · exact List.Subset.refl _
      · exact List.subset_append_left _ _
    have hB : b ∈ next := by
      dsimp only [next]
      split
      · rename_i hh
        obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
        have hxb := hInj x (hAcc hx) b hb (beq_iff_eq.mp he)
        exact hxb ▸ hx
      · exact List.mem_append_right _ (List.mem_singleton_self _)
    have hNext : next ⊆ D := by
      dsimp only [next]
      split
      · exact hAcc
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hAcc hx
        · exact List.mem_singleton.mp hx ▸ hb
    apply ih next (fun x hx => hAs (List.mem_cons_of_mem b hx)) hNext
    rcases ha with ha | ha
    · exact Or.inl (hMono ha)
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl hB
      · exact Or.inr ha

/-- In a single slot/root pool, first-per-seat selection drops only duplicates. -/
theorem pcsa_formation_firstPerSeat_covers (as : List (AckWire n)) (s : Slot)
    (r : BlockId) (hUniform : ∀ a ∈ as, ∃ i, (AckWire.decode? a) = some (s, i, r)) :
    as ⊆ firstPerSeat as := by
  intro a ha
  delta firstPerSeat
  apply formation_first_fold_covers as ?_ as [] (List.Subset.refl _) (by simp) a (Or.inr ha)
  intro x hx y hy he
  obtain ⟨i, hd⟩ := hUniform x hx
  obtain ⟨j, hu⟩ := hUniform y hy
  change (AckWire.decode? x).map (fun z => z.2.1) = (AckWire.decode? y).map (fun z => z.2.1) at he
  rw [hd, hu] at he
  have hij : i = j := Option.some.inj he
  subst j
  exact (formation_ack_shape x s i r hd).trans (formation_ack_shape y s i r hu).symm

private theorem formation_poolAck_cases (p : Params) (st : State p.n) (a : AckWire p.n) :
    poolAck p st a = st ∨ poolAck p st a = { st with ackPool := st.ackPool ++ [a] } := by
  delta poolAck
  cases (AckWire.decode? a) with
  | none => exact Or.inl rfl
  | some x =>
    rcases x with ⟨s, i, r⟩
    dsimp only
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl

private theorem formation_poolAck_frame (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).base.blocks = st.base.blocks ∧
      (poolAck p st a).fg = st.fg ∧ (poolAck p st a).pcs = st.pcs := by
  rcases formation_poolAck_cases p st a with he | he <;> rw [he]
  all_goals exact ⟨rfl, rfl, rfl⟩

private theorem formation_filter_append_missing {α : Type} (xs : List α) (a : α)
    (f : α → Bool) (hNot : a ∉ (xs ++ [a]).filter f) :
    (xs ++ [a]).filter f = xs.filter f := by
  have hMiss : f a = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    exact hNot (List.mem_filter.mpr
      ⟨List.mem_append_right _ (List.mem_singleton_self _), ht⟩)
  rw [List.filter_append]
  have hnil : [a].filter f = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro b hb
    obtain rfl := List.mem_singleton.mp hb
    intro ht
    have hh := hMiss.symm.trans ht
    cases hh
  exact (congrArg (fun ys => xs.filter f ++ ys) hnil).trans (List.append_nil _)

private theorem formation_poolAck_on_missing (p : Params) (st : State p.n)
    (a : AckWire p.n) (s : Slot) (r : BlockId)
    (hNot : a ∉ acksOn (poolAck p st a) s r) :
    acksOn (poolAck p st a) s r = acksOn st s r := by
  rcases formation_poolAck_cases p st a with he | he
  · rw [he]
  · rw [he] at hNot ⊢
    delta acksOn at hNot ⊢
    exact formation_filter_append_missing st.ackPool a _ hNot

/-- A completing ack belongs to the certificate that its call newly installs. -/
theorem pcsa_formation_admitAck_contains (p : Params) (st : State p.n)
    (a : AckWire p.n) (C : PC p.n) (hClosed : FormationCollected st)
    (hNew : ¬FormationPCIdentity st C.slot C.target)
    (hm : C ∈ (admitAck p st a).pcs) : a ∈ C.acks := by
  have hf := formation_poolAck_frame p st a
  have hNot : C ∉ (poolAck p st a).pcs := by
    rw [hf.2.2]
    intro hc
    exact hNew ⟨C, hc, rfl, rfl⟩
  obtain ⟨_, hb, hc⟩ := pcsa_formation_collect_new_origin _ C hm hNot
  by_contra hA
  have hMiss : a ∉ acksOn (poolAck p st a) C.slot C.target.root := by
    intro ha
    have hCover := pcsa_formation_firstPerSeat_covers
      (acksOn (poolAck p st a) C.slot C.target.root) C.slot C.target.root
      (fun b hb => (mem_acksOn_iff _ _ _ b).mp hb |>.2)
    have hIn := hCover ha
    have he := congrArg PC.acks ((assemblePC_some_iff _ _ _ C).mp hc).1
    change C.acks = firstPerSeat (acksOn (poolAck p st a) C.slot C.target.root) at he
    rw [← he] at hIn
    exact hA hIn
  have hOn := formation_poolAck_on_missing p st a C.slot C.target.root hMiss
  rw [formation_assemble_eq_of_on st _ C.slot C.target hf.1 hf.2.1 hOn] at hc
  rw [hf.1] at hb
  exact hNew (pcsa_formation_collected_identity st _ _ C p.nPos hClosed hb hc)

private theorem formation_initial_collected : FormationCollected (initial n) := by
  intro s b C hm
  exact (List.not_mem_nil hm).elim

private theorem formation_row_collected (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : FormationCollected st) : FormationCollected (admitRow p st a) := by
  delta admitRow
  cases (RowWire.decode? a) with
  | none => exact h
  | some x =>
    dsimp only
    split
    · exact h
    · exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)

private theorem formation_rows_collected (p : Params) (st : State p.n)
    (as : List (RowWire p.n)) (h : FormationCollected st) :
    FormationCollected (as.foldl (admitRow p) st) := by
  induction as generalizing st with
  | nil => exact h
  | cons a as ih =>
    rw [List.foldl_cons]
    exact ih _ (formation_row_collected p st a h)

private theorem formation_head_collected (p : Params) (st : State p.n) (s : Slot)
    (i : Fin p.n) (r : BlockId) (h : FormationCollected st) :
    FormationCollected (admitHead p st s i r) := by
  delta admitHead GridCO.admitVote
  dsimp only
  split
  · exact h
  · exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)

private theorem formation_clockPre_collected (p : Params) (st : State p.n) (t : Time)
    (h : FormationCollected st) : FormationCollected (clockPre p st t) := by
  delta clockPre
  dsimp only
  split <;> split <;> split
  all_goals exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)

private theorem formation_gate_collected (p : Params) (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) (h : FormationCollected st) :
    FormationCollected (gateFrom p a cs rank st s) := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none =>
    exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)
  | some result =>
    dsimp only
    split
    · exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)
    · apply List.foldlRecOn
      · exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)
      · intro acc ha b _
        apply List.foldlRecOn
        · exact ha
        · intro acc' ha' g _
          exact pcsa_formation_collected_of_frame acc' _ ha' rfl rfl rfl (List.Subset.refl _)

private theorem formation_normalize_collected (st : State n) (h : FormationCollected st) :
    FormationCollected (normalizeS st) := by
  delta normalizeS
  split
  · exact h
  · exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)

/-- A tick preserves collection closure. -/
theorem pcsa_formation_clock_collected (p : Params) (st : State p.n) (t : Time)
    (h : FormationCollected st) : FormationCollected (clock p st t) := by
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    apply formation_normalize_collected
    split
    · exact formation_clockPre_collected p st t h
    · exact formation_gate_collected p _ _ _ _ _ (formation_clockPre_collected p st t h)
  · exact formation_clockPre_collected p st t h

/-- Every handler leaves the supported PC candidates collected. -/
theorem pcsa_formation_process_collected (p : Params) (st : State p.n) (o : Wire p.n)
    (h : FormationCollected st) : FormationCollected (process p st o) := by
  delta process
  cases o.decode with
  | none => exact h
  | some d =>
    cases d with
    | vote s i r => exact formation_head_collected p st s i r h
    | row i body => exact formation_row_collected p st _ h
    | ack s i r => exact pcsa_formation_collect_invariant _
    | pc C =>
      change FormationCollected (admitPC st C)
      delta admitPC
      split
      · exact pcsa_formation_collect_invariant _
      · exact h
    | block s N =>
      change FormationCollected (admitBlock p st s N)
      delta admitBlock
      split
      · exact h
      · cases parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · exact formation_rows_collected p _ N.rows (pcsa_formation_collect_invariant _)
          · exact h

/-- Collection closure holds in every reachable store. -/
theorem pcsa_formation_reachable_collected (p : Params) (st : State p.n)
    (h : Reachable p st) : FormationCollected st := by
  induction h with
  | init => exact formation_initial_collected
  | tick t _ ih => exact pcsa_formation_clock_collected p _ t ih
  | deliver o _ ih => exact pcsa_formation_process_collected p _ o ih

end AvailableChain.PCSA
end
